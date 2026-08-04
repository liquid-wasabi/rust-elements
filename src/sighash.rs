// Rust Bitcoin Library
// Written in 2018 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! BIP143 Implementation
//!
//! Implementation of BIP143 Segwit-style signatures. Should be sufficient
//! to create signatures for Segwit transactions (which should be pushed into
//! the appropriate place in the `Transaction::witness` array) or bcash
//! signatures, which are placed in the scriptSig.
//!

use std::borrow::Borrow;
use crate::encode::{self, Encodable, VarInt};
use crate::hash_types::Sighash;
use crate::hashes::{sha256d, sha256t, sha256, HashEngine as _};
use crate::script::Script;
use std::ops::{Deref, DerefMut};
use std::io;
use crate::endian;
use crate::taproot::LeafVersion;
use crate::transaction::{EcdsaSighashType, Transaction, TxIn, TxOut, TxInWitness};
use crate::confidential;
use crate::Sequence;
use std::fmt;
use crate::taproot::{TapSighashHash, TapLeafHash};

use crate::BlockHash;

use crate::transaction::SighashTypeParseError;
/// Efficiently calculates signature hash message for legacy, segwit and taproot inputs.
#[derive(Debug)]
pub struct SighashCache<T: Deref<Target = Transaction>> {
    /// Access to transaction required for various introspection, moreover type
    /// `T: Deref<Target=Transaction>` allows to accept borrow and mutable borrow, the
    /// latter in particular is necessary for [`SighashCache::witness_mut`]
    tx: T,

    /// Common cache for taproot and segwit inputs. It's an option because it's not needed for legacy inputs
    common_cache: Option<CommonCache>,

    /// Cache for segwit v0 inputs, it's the result of another round of sha256 on `common_cache`
    segwit_cache: Option<SegwitCache>,

    /// Cache for taproot v1 inputs
    taproot_cache: Option<TaprootCache>,
}

/// Values cached common between segwit and taproot inputs
#[derive(Debug)]
struct CommonCache {
    prevouts: sha256::Hash,
    sequences: sha256::Hash,

    /// in theory, `outputs` could be `Option` since `NONE` and `SINGLE` doesn't need it, but since
    /// `ALL` is the mostly used variant by large, we don't bother
    outputs: sha256::Hash,
    issuances: sha256::Hash,
}

/// Values cached for segwit inputs, it's equal to [`CommonCache`] plus another round of `sha256`
#[derive(Debug)]
struct SegwitCache {
    prevouts: sha256d::Hash,
    sequences: sha256d::Hash,
    issuances: sha256d::Hash,
    outputs: sha256d::Hash,
    rangeproofs: sha256d::Hash,
}

/// Values cached for taproot inputs
#[derive(Debug)]
struct TaprootCache {
    script_pubkeys: sha256::Hash,
    outpoint_flags: sha256::Hash,
    asset_amounts: sha256::Hash,
    issuance_rangeproofs: sha256::Hash,
    output_witnesses: sha256::Hash,
}

/// Whether the `SCRIPT_SIGHASH_RANGEPROOF` script-verification flag is active.
///
/// This consensus context is independent of the `SIGHASH_RANGEPROOF` bit in an
/// [`EcdsaSighashType`]. Before activation, the bit is still serialized in the
/// sighash type but output proofs are not added to the signing data.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum SighashRangeproofMode {
    /// Use pre-activation signing semantics without output-proof commitments.
    Disabled,
    /// Use post-activation signing semantics with output-proof commitments.
    Enabled,
}

impl SighashRangeproofMode {
    fn is_enabled(self) -> bool {
        self == Self::Enabled
    }
}

/// Result of encoding legacy signing data.
///
/// This type forces callers to handle the legacy `SIGHASH_SINGLE` sentinel,
/// which is already a hash value and cannot be represented as signing data to
/// be hashed again.
#[must_use]
pub enum EncodeSigningDataResult<E> {
    /// The input triggers the legacy `SIGHASH_SINGLE` bug and must use the
    /// uint256 value one directly as its sighash.
    SighashSingleBug,
    /// Signing data was encoded normally, or the writer returned an error.
    WriteResult(Result<(), E>),
}

impl<E> EncodeSigningDataResult<E> {
    /// Return whether the input triggers the legacy `SIGHASH_SINGLE` bug,
    /// propagating any writer error.
    pub fn is_sighash_single_bug(self) -> Result<bool, E> {
        match self {
            Self::SighashSingleBug => Ok(true),
            Self::WriteResult(Ok(())) => Ok(false),
            Self::WriteResult(Err(error)) => Err(error),
        }
    }

    /// Map a writer error while preserving the `SIGHASH_SINGLE` sentinel.
    pub fn map_err<F, O>(self, op: O) -> EncodeSigningDataResult<F>
    where
        O: FnOnce(E) -> F,
    {
        match self {
            Self::SighashSingleBug => EncodeSigningDataResult::SighashSingleBug,
            Self::WriteResult(Ok(())) => EncodeSigningDataResult::WriteResult(Ok(())),
            Self::WriteResult(Err(error)) => {
                EncodeSigningDataResult::WriteResult(Err(op(error)))
            }
        }
    }
}

/// Contains outputs of previous transactions.
/// In the case [`SchnorrSighashType`] variant is `ANYONECANPAY`, [`Prevouts::One`] may be provided
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Prevouts<'u, T> where T: 'u + Borrow<TxOut> {
    /// `One` variant allows to provide the single Prevout needed. It's useful for example
    /// when modifier `ANYONECANPAY` is provided, only prevout of the current input is needed.
    /// The first `usize` argument is the input index this [`TxOut`] is referring to.
    One(usize, T),
    /// When `ANYONECANPAY` is not provided, or the caller is handy giving all prevouts so the same
    /// variable can be used for multiple inputs.
    All(&'u [T]),
}

const KEY_VERSION_0: u8 = 0u8;

/// Information related to the script path spending
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ScriptPath<'s> {
    script: &'s Script,
    code_separator_pos: u32,
    leaf_version: LeafVersion,
}

/// Possible errors in computing the signature message
#[derive(Debug)]
pub enum Error {
    /// Could happen only by using `*_encode_signing_*` methods with custom writers, engines writers
    /// like the ones used in methods `*_signature_hash` don't error
    Encode(encode::Error),

    /// Requested index is greater or equal than the number of inputs in the transaction
    IndexOutOfInputsBounds {
        /// Requested index
        index: usize,
        /// Number of transaction inputs
        inputs_size: usize,
    },

    /// Using `SIGHASH_SINGLE` without a "corresponding output" (an output with the same index as the
    /// input being verified) is a validation failure
    SingleWithoutCorrespondingOutput {
        /// Requested index
        index: usize,
        /// Number of transaction outputs
        outputs_size: usize,
    },

    /// There are mismatches in the number of prevouts provided compared with the number of
    /// inputs in the transaction
    PrevoutsSize,

    /// Requested a prevout index which is greater than the number of prevouts provided or a
    /// [`Prevouts::One`] with different index
    PrevoutIndex,

    /// A single prevout has been provided but all prevouts are needed without `ANYONECANPAY`
    PrevoutKind,

    /// Annex must be at least one byte long and the first bytes must be `0x50`
    WrongAnnex,

    /// Invalid Sighash type
    InvalidSighashType(u8),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Encode(ref e) => write!(f, "Writer errored: {:?}", e),
            Error::IndexOutOfInputsBounds { index, inputs_size } => write!(f, "Requested index ({}) is greater or equal than the number of transaction inputs ({})", index, inputs_size),
            Error::SingleWithoutCorrespondingOutput { index, outputs_size } => write!(f, "SIGHASH_SINGLE for input ({}) haven't a corresponding output (#outputs:{})", index, outputs_size),
            Error::PrevoutsSize => write!(f, "Number of supplied prevouts differs from the number of inputs in transaction"),
            Error::PrevoutIndex => write!(f, "The index requested is greater than available prevouts or different from the provided [Provided::Anyone] index"),
            Error::PrevoutKind => write!(f, "A single prevout has been provided but all prevouts are needed without `ANYONECANPAY`"),
            Error::WrongAnnex => write!(f, "Annex must be at least one byte long and the first bytes must be `0x50`"),
            Error::InvalidSighashType(hash_ty) => write!(f, "Invalid schnorr Signature hash type : {} ", hash_ty),
        }
    }
}

impl ::std::error::Error for Error {}

impl<T> Prevouts<'_, T> where T: Borrow<TxOut> {
    fn check_all(&self, tx: &Transaction) -> Result<(), Error> {
        if let Prevouts::All(prevouts) = self {
            if prevouts.len() != tx.input.len() {
                return Err(Error::PrevoutsSize);
            }
        }
        Ok(())
    }

    fn get_all(&self) -> Result<&[T], Error> {
        match self {
            Prevouts::All(prevouts) => Ok(*prevouts),
            Prevouts::One(..) => Err(Error::PrevoutKind),
        }
    }

    fn get(&self, input_index: usize) -> Result<&TxOut, Error> {
        match self {
            Prevouts::One(index, prevout) => {
                if input_index == *index {
                    Ok(prevout.borrow())
                } else {
                    Err(Error::PrevoutIndex)
                }
            }
            Prevouts::All(prevouts) => prevouts
                .get(input_index)
                .map(T::borrow)
                .ok_or(Error::PrevoutIndex),
        }
    }
}

impl<'s> ScriptPath<'s> {
    /// Create a new `ScriptPath` structure
    pub fn new(script: &'s Script, code_separator_pos: u32, leaf_version: LeafVersion) -> Self {
        ScriptPath {
            script,
            code_separator_pos,
            leaf_version,
        }
    }
    /// Create a new `ScriptPath` structure using default values for `code_separator_pos` and `leaf_version`
    pub fn with_defaults(script: &'s Script) -> Self {
        Self::new(script, 0xFFFF_FFFFu32, LeafVersion::TAPSCRIPT)
    }

    /// Compute the leaf hash
    pub fn leaf_hash(&self) -> TapLeafHash {
        TapLeafHash::from_script(self.script, self.leaf_version)
    }
}

impl<'s> From<ScriptPath<'s>> for TapLeafHash {
    fn from(script_path: ScriptPath<'s>) -> TapLeafHash {
        script_path.leaf_hash()
    }
}

impl<R: Deref<Target = Transaction>> SighashCache<R> {
    /// Compute the sighash components from an unsigned transaction and auxiliary
    /// in a lazy manner when required.
    /// For the generated sighashes to be valid, no fields in the transaction may change except for
    /// `script_sig` and witnesses.
    pub fn new(tx: R) -> Self {
        SighashCache {
            tx,
            common_cache: None,
            taproot_cache: None,
            segwit_cache: None,
        }
    }

    /// Encode the BIP341 signing data for any flag type into a given object implementing a
    /// `io::Write` trait.
    #[allow(clippy::too_many_arguments)]
    pub fn taproot_encode_signing_data_to<Write: io::Write, T: Borrow<TxOut>>(
        &mut self,
        mut writer: Write,
        input_index: usize,
        prevouts: &Prevouts<T>,
        annex: Option<Annex>,
        leaf_hash_code_separator: Option<(TapLeafHash, u32)>,
        sighash_type: SchnorrSighashType,
        genesis_hash: BlockHash,
    ) -> Result<(), Error> {
        prevouts.check_all(&self.tx)?;

        let (sighash, anyone_can_pay) = sighash_type.split_anyonecanpay_flag();

        // Genesis hash twice
        genesis_hash.consensus_encode(&mut writer)?;
        genesis_hash.consensus_encode(&mut writer)?;

        // No epoch in elements

        // * Control:
        // hash_type (1).
        (sighash_type as u8).consensus_encode(&mut writer)?;

        // * Transaction Data:
        // nVersion (4): the nVersion of the transaction.
        self.tx.version.consensus_encode(&mut writer)?;

        // nLockTime (4): the nLockTime of the transaction.
        self.tx.lock_time.consensus_encode(&mut writer)?;

        // If the hash_type & 0x80 does not equal SIGHASH_ANYONECANPAY:
        //     sha_outpoint_flags (32): (ELEMENTS) the SHA256 of outpoint flags
        //     sha_prevouts (32): the SHA256 of the serialization of all input outpoints.
        //     sha_asset_amounts (32): (ELEMENTS) the SHA256 of the serialization of all spent output asset followed by amounts.
        //     sha_scriptpubkeys (32): the SHA256 of the serialization of all spent output scriptPubKeys.
        //     sha_sequences (32): the SHA256 of the serialization of all input nSequence.
        //     sha_issuances (32): (ELEMENTS) the SHA256 of the serialization of the concatenation of asset issuance data
        //     sha_issuance_rangeproofs (32): (ELEMENTS) the sha256 of issuance amount rangeproof followed by inflation keys rangeproof
        if !anyone_can_pay {
            self.taproot_cache(prevouts.get_all()?)
                .outpoint_flags
                .consensus_encode(&mut writer)?;
            self.common_cache().prevouts.consensus_encode(&mut writer)?;
            self.taproot_cache(prevouts.get_all()?)
                .asset_amounts
                .consensus_encode(&mut writer)?;
            self.taproot_cache(prevouts.get_all()?)
                .script_pubkeys
                .consensus_encode(&mut writer)?;
            self.common_cache()
                .sequences
                .consensus_encode(&mut writer)?;
            self.common_cache()
                .issuances
                .consensus_encode(&mut writer)?;
            self.taproot_cache(prevouts.get_all()?)
                .issuance_rangeproofs
                .consensus_encode(&mut writer)?;
        }

        // If hash_type & 3 does not equal SIGHASH_NONE or SIGHASH_SINGLE:
        //     sha_outputs (32): the SHA256 of the serialization of all outputs in CTxOut format.
        //     sha_output_witnesses (32): (ELEMENTS) the SHA256 of the serialization of all output witnesses
        if sighash != SchnorrSighashType::None && sighash != SchnorrSighashType::Single {
            self.common_cache().outputs.consensus_encode(&mut writer)?;
            self.taproot_cache(prevouts.get_all()?)
                .output_witnesses
                .consensus_encode(&mut writer)?;
        }

        // * Data about this input:
        // spend_type (1): equal to (ext_flag * 2) + annex_present, where annex_present is 0
        // if no annex is present, or 1 otherwise
        let mut spend_type = 0u8;
        if annex.is_some() {
            spend_type |= 1u8;
        }
        if leaf_hash_code_separator.is_some() {
            spend_type |= 2u8;
        }
        spend_type.consensus_encode(&mut writer)?;

        // If hash_type & 0x80 equals SIGHASH_ANYONECANPAY:
        //      outpoint_flag(1) : (ELEMENTS) the outpoint flag of this input
        //      outpoint (36): the COutPoint of this input (32-byte hash + 4-byte little-endian).
        //      asset (33): (ELEMENTS) the asset of the previous output
        //      value (9-33): (modified in ELEMENTS) value of the previous output spent by this input.
        //      scriptPubKey (35): scriptPubKey of the previous output spent by this input, serialized as script inside CTxOut. Its size is always 35 bytes.
        //      nSequence (4): nSequence of this input.
        //      asset_issuance (1-130): (ELEMENTS) asset issuance data if present; otherwise 0x00
        //      asset_issuance_rangeproofs (0-32) : (ELEMENTS) the sha256 of serialization of issuance proofs for this input
        if anyone_can_pay {
            let txin =
                &self
                    .tx
                    .input
                    .get(input_index)
                    .ok_or(Error::IndexOutOfInputsBounds {
                        index: input_index,
                        inputs_size: self.tx.input.len(),
                    })?;
            let previous_output = prevouts.get(input_index)?;
            txin.outpoint_flag().consensus_encode(&mut writer)?;
            txin.previous_output.consensus_encode(&mut writer)?;
            previous_output.asset.consensus_encode(&mut writer)?;
            previous_output.value.consensus_encode(&mut writer)?;
            previous_output
                .script_pubkey
                .consensus_encode(&mut writer)?;
            txin.sequence.consensus_encode(&mut writer)?;
            if txin.has_issuance(){
                txin.asset_issuance.consensus_encode(&mut writer)?;
                let mut eng = sha256::Hash::engine();
                txin.witness.amount_rangeproof.consensus_encode(&mut eng)?;
                txin.witness.inflation_keys_rangeproof.consensus_encode(&mut eng)?;
                let sha_single_issuance_rangeproofs = sha256::Hash::from_engine(eng);
                sha_single_issuance_rangeproofs.consensus_encode(&mut writer)?;
            } else {
                0u8.consensus_encode(&mut writer)?;
            }
        } else {
            (input_index as u32).consensus_encode(&mut writer)?;
        }

        // If an annex is present (the lowest bit of spend_type is set):
        //      sha_annex (32): the SHA256 of (compact_size(size of annex) || annex), where annex
        //      includes the mandatory 0x50 prefix.
        if let Some(annex) = annex {
            let mut enc = sha256::Hash::engine();
            annex.consensus_encode(&mut enc)?;
            let hash = sha256::Hash::from_engine(enc);
            hash.consensus_encode(&mut writer)?;
        }

        // * Data about this output:
        // If hash_type & 3 equals SIGHASH_SINGLE:
        //      sha_single_output (32): the SHA256 of the corresponding output in CTxOut format.
        //      sha_single_output_witness (32): the sha256 serialization of output witnesses
        if sighash == SchnorrSighashType::Single {
            let mut enc = sha256::Hash::engine();
            let out = self.tx
                .output
                .get(input_index)
                .ok_or(Error::SingleWithoutCorrespondingOutput {
                    index: input_index,
                    outputs_size: self.tx.output.len(),
                })?;
            out.consensus_encode(&mut enc)?;
            let hash = sha256::Hash::from_engine(enc);
            hash.consensus_encode(&mut writer)?;

            // Witness serialization
            let mut eng = sha256::Hash::engine();
            out.witness.consensus_encode(&mut eng)?;
            let sha_single_output_witness = sha256::Hash::from_engine(eng);
            sha_single_output_witness.consensus_encode(&mut writer)?;
        }

        //     if (scriptpath):
        //         ss += TaggedHash("TapLeaf", bytes([leaf_ver]) + ser_string(script))
        //         ss += bytes([0])
        //         ss += struct.pack("<i", codeseparator_pos)
        if let Some((hash, code_separator_pos)) = leaf_hash_code_separator {
            hash.to_byte_array().consensus_encode(&mut writer)?;
            KEY_VERSION_0.consensus_encode(&mut writer)?;
            code_separator_pos.consensus_encode(&mut writer)?;
        }

        Ok(())
    }

    /// Compute the BIP341 sighash for any flag type.
    pub fn taproot_sighash<T: Borrow<TxOut>>(
        &mut self,
        input_index: usize,
        prevouts: &Prevouts<T>,
        annex: Option<Annex>,
        leaf_hash_code_separator: Option<(TapLeafHash, u32)>,
        sighash_type: SchnorrSighashType,
        genesis_hash: BlockHash,
    ) -> Result<TapSighashHash, Error> {
        let mut enc = sha256t::Hash::engine();
        self.taproot_encode_signing_data_to(
            &mut enc,
            input_index,
            prevouts,
            annex,
            leaf_hash_code_separator,
            sighash_type,
            genesis_hash,
        )?;
        Ok(TapSighashHash(enc.finalize()))
    }

    /// Compute the BIP341 sighash for a key spend
    pub fn taproot_key_spend_signature_hash<T: Borrow<TxOut>>(
        &mut self,
        input_index: usize,
        prevouts: &Prevouts<T>,
        sighash_type: SchnorrSighashType,
        genesis_hash: BlockHash,
    ) -> Result<TapSighashHash, Error> {
        let mut enc = sha256t::Hash::engine();
        self.taproot_encode_signing_data_to(
            &mut enc,
            input_index,
            prevouts,
            None,
            None,
            sighash_type,
            genesis_hash,
        )?;
        Ok(TapSighashHash(enc.finalize()))
    }

    /// Compute the BIP341 sighash for a script spend
    ///
    /// Assumes the default `OP_CODESEPARATOR` position of `0xFFFFFFFF`. Custom values can be
    /// provided through the more fine-grained API of [`SighashCache::taproot_encode_signing_data_to`].
    pub fn taproot_script_spend_signature_hash<S: Into<TapLeafHash>, T: Borrow<TxOut>>(
        &mut self,
        input_index: usize,
        prevouts: &Prevouts<T>,
        leaf_hash: S,
        sighash_type: SchnorrSighashType,
        genesis_hash: BlockHash,
    ) -> Result<TapSighashHash, Error> {
        let mut enc = sha256t::Hash::engine();
        self.taproot_encode_signing_data_to(
            &mut enc,
            input_index,
            prevouts,
            None,
            Some((leaf_hash.into(), 0xFFFF_FFFF)),
            sighash_type,
            genesis_hash
        )?;
        Ok(TapSighashHash(enc.finalize()))
    }

    /// Encode the BIP143 signing data for any flag type into a given object implementing a
    /// `std::io::Write` trait.
    ///
    /// This method uses post-activation [`SighashRangeproofMode::Enabled`]
    /// semantics. Use
    /// [`SighashCache::encode_segwitv0_signing_data_to_with_rangeproof_mode`]
    /// when reproducing pre-activation hashes.
    ///
    /// *Warning* This does NOT attempt to support `OP_CODESEPARATOR`. In general
    /// this would require evaluating `script_pubkey` to determine which separators
    /// get evaluated and which don't, which we don't have the information to
    /// determine.
    ///
    /// # Panics
    /// Panics if `input_index` is greater than or equal to `self.input.len()`
    ///
    pub fn encode_segwitv0_signing_data_to<Write: io::Write>(
        &mut self,
        writer: Write,
        input_index: usize,
        script_code: &Script,
        value: confidential::Value,
        sighash_type: EcdsaSighashType,
    ) -> Result<(), encode::Error> {
        self.encode_segwitv0_signing_data_to_with_rangeproof_mode(
            writer,
            input_index,
            script_code,
            value,
            sighash_type,
            SighashRangeproofMode::Enabled,
        )
    }

    /// Encode the BIP143 signing data with explicit
    /// `SCRIPT_SIGHASH_RANGEPROOF` activation semantics.
    ///
    /// Use [`SighashRangeproofMode::Disabled`] to reproduce pre-activation
    /// hashes and [`SighashRangeproofMode::Enabled`] for post-activation hashes.
    pub fn encode_segwitv0_signing_data_to_with_rangeproof_mode<Write: io::Write>(
        &mut self,
        mut writer: Write,
        input_index: usize,
        script_code: &Script,
        value: confidential::Value,
        sighash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
    ) -> Result<(), encode::Error> {
        let zero_hash = [0u8; 32];

        let (sighash, anyone_can_pay, has_rangeproof_bit) = sighash_type.split_flags();
        let rangeproof = rangeproof_mode.is_enabled() && has_rangeproof_bit;

        self.tx.version.consensus_encode(&mut writer)?;

        if anyone_can_pay {
            zero_hash.consensus_encode(&mut writer)?;
        } else {
            self.segwit_cache().prevouts.consensus_encode(&mut writer)?;
        }

        if !anyone_can_pay && sighash != EcdsaSighashType::Single && sighash != EcdsaSighashType::None {
            self.segwit_cache().sequences.consensus_encode(&mut writer)?;
        } else {
            zero_hash.consensus_encode(&mut writer)?;
        }

        // Elements: Push the hash issuance zero hash as required
        // If required implement for issuance, but not necessary as of now
        if anyone_can_pay {
            zero_hash.consensus_encode(&mut writer)?;
        } else {
            self.segwit_cache().issuances.consensus_encode(&mut writer)?;
        }

        // input specific values
        {
            let txin = &self.tx.input[input_index];

            txin.previous_output.consensus_encode(&mut writer)?;
            script_code.consensus_encode(&mut writer)?;
            value.consensus_encode(&mut writer)?;
            txin.sequence.consensus_encode(&mut writer)?;
            if txin.has_issuance(){
                txin.asset_issuance.consensus_encode(&mut writer)?;
            }
        }

        // hashoutputs
        if sighash != EcdsaSighashType::Single && sighash != EcdsaSighashType::None {
            self.segwit_cache().outputs.consensus_encode(&mut writer)?;
        } else if sighash == EcdsaSighashType::Single && input_index < self.tx.output.len() {
            let mut single_enc = sha256d::Hash::engine();
            self.tx.output[input_index].consensus_encode(&mut single_enc)?;
            Sighash(single_enc.finalize()).consensus_encode(&mut writer)?;
        } else {
            zero_hash.consensus_encode(&mut writer)?;
        }

        if rangeproof {
            if sighash != EcdsaSighashType::Single && sighash != EcdsaSighashType::None {
                self.segwit_cache().rangeproofs.consensus_encode(&mut writer)?;
            } else if sighash == EcdsaSighashType::Single && input_index < self.tx.output.len() {
                let mut single_enc = sha256d::Hash::engine();
                let witness = &self.tx.output[input_index].witness;
                witness.rangeproof.consensus_encode(&mut single_enc)?;
                witness.surjection_proof.consensus_encode(&mut single_enc)?;
                Sighash(single_enc.finalize()).consensus_encode(&mut writer)?;
            } else {
                zero_hash.consensus_encode(&mut writer)?;
            }
        }

        self.tx.lock_time.consensus_encode(&mut writer)?;
        sighash_type.as_u32().consensus_encode(&mut writer)?;
        Ok(())
    }

    /// Compute the segwitv0(BIP143) style sighash for any flag type.
    ///
    /// This method uses post-activation [`SighashRangeproofMode::Enabled`]
    /// semantics. Use [`SighashCache::segwitv0_sighash_with_rangeproof_mode`]
    /// when reproducing pre-activation hashes.
    /// *Warning* This does NOT attempt to support `OP_CODESEPARATOR`. In general
    /// this would require evaluating `script_pubkey` to determine which separators
    /// get evaluated and which don't, which we don't have the information to
    /// determine.
    ///
    /// # Panics
    /// Panics if `input_index` is greater than or equal to `self.input.len()`
    ///
    pub fn segwitv0_sighash(
        &mut self,
        input_index: usize,
        script_code: &Script,
        value: confidential::Value,
        sighash_type: EcdsaSighashType
    ) -> Sighash {
        self.segwitv0_sighash_with_rangeproof_mode(
            input_index,
            script_code,
            value,
            sighash_type,
            SighashRangeproofMode::Enabled,
        )
    }

    /// Compute a SegWit-v0 sighash with explicit
    /// `SCRIPT_SIGHASH_RANGEPROOF` activation semantics.
    pub fn segwitv0_sighash_with_rangeproof_mode(
        &mut self,
        input_index: usize,
        script_code: &Script,
        value: confidential::Value,
        sighash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
    ) -> Sighash {
        let mut enc = sha256d::Hash::engine();
        self.encode_segwitv0_signing_data_to_with_rangeproof_mode(
            &mut enc,
            input_index,
            script_code,
            value,
            sighash_type,
            rangeproof_mode,
        )
        .expect("engines don't error");
        Sighash(enc.finalize())
    }

    /// Encodes the signing data from which a signature hash for a given input index with a given
    /// sighash flag can be computed.  To actually produce a scriptSig, this hash needs to be run
    /// through an ECDSA signer, the `SighashType` appended to the resulting sig, and a script
    /// written around this, but this is the general (and hard) part.
    ///
    /// This method uses post-activation [`SighashRangeproofMode::Enabled`]
    /// semantics. It is retained for compatibility, but cannot represent the
    /// legacy `SIGHASH_SINGLE` sentinel and returns an invalid-input error for
    /// that case without writing bytes. New code should use
    /// [`SighashCache::legacy_encode_signing_data_to`] or
    /// [`SighashCache::legacy_encode_signing_data_to_with_rangeproof_mode`].
    ///
    /// *Warning* This does NOT attempt to support `OP_CODESEPARATOR`. In general this would require
    /// evaluating `script_pubkey` to determine which separators get evaluated and which don't,
    /// which we don't have the information to determine.
    ///
    /// # Panics Panics if `input_index` is greater than or equal to `self.input.len()`
    ///
    pub fn encode_legacy_signing_data_to<Write: io::Write>(
        &self,
        writer: Write,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
    ) -> Result<(), encode::Error> {
        match self
            .legacy_encode_signing_data_to(
                writer,
                input_index,
                script_pubkey,
                sighash_type,
            )
            .is_sighash_single_bug()
        {
            Ok(false) => Ok(()),
            Ok(true) => Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "legacy SIGHASH_SINGLE sentinel cannot be encoded as signing data",
            )
            .into()),
            Err(error) => Err(error),
        }
    }

    /// Encode legacy signing data using post-activation
    /// [`SighashRangeproofMode::Enabled`] semantics.
    ///
    /// The return value forces callers to handle the legacy `SIGHASH_SINGLE`
    /// sentinel without accidentally hashing it again.
    pub fn legacy_encode_signing_data_to<Write: io::Write>(
        &self,
        writer: Write,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
    ) -> EncodeSigningDataResult<encode::Error> {
        self.legacy_encode_signing_data_to_with_rangeproof_mode(
            writer,
            input_index,
            script_pubkey,
            sighash_type,
            SighashRangeproofMode::Enabled,
        )
    }

    /// Encode legacy signing data with explicit
    /// `SCRIPT_SIGHASH_RANGEPROOF` activation semantics.
    ///
    /// Use [`SighashRangeproofMode::Disabled`] to reproduce pre-activation
    /// hashes and [`SighashRangeproofMode::Enabled`] for post-activation hashes.
    pub fn legacy_encode_signing_data_to_with_rangeproof_mode<Write: io::Write>(
        &self,
        writer: Write,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
    ) -> EncodeSigningDataResult<encode::Error> {
        assert!(input_index < self.tx.input.len());  // Panic on OOB

        let (sighash, _, _) = sighash_type.split_flags();

        // The sentinel is already the final sighash and must not be hashed again.
        if sighash == EcdsaSighashType::Single && input_index >= self.tx.output.len() {
            return EncodeSigningDataResult::SighashSingleBug;
        }

        EncodeSigningDataResult::WriteResult(self.encode_legacy_signing_data_to_inner(
            writer,
            input_index,
            script_pubkey,
            sighash_type,
            rangeproof_mode,
        ))
    }

    fn encode_legacy_signing_data_to_inner<Write: io::Write>(
        &self,
        mut writer: Write,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
    ) -> Result<(), encode::Error> {
        let (sighash, anyone_can_pay, has_rangeproof_bit) = sighash_type.split_flags();
        let rangeproof = rangeproof_mode.is_enabled() && has_rangeproof_bit;

        // Build tx to sign
        let mut tx = Transaction {
            version: self.tx.version,
            lock_time: self.tx.lock_time,
            input: vec![],
            output: vec![],
        };
        // Add all inputs necessary..
        if anyone_can_pay {
            tx.input = vec![TxIn {
                previous_output: self.tx.input[input_index].previous_output,
                is_pegin: self.tx.input[input_index].is_pegin,
                script_sig: script_pubkey.clone(),
                sequence: self.tx.input[input_index].sequence,
                asset_issuance: self.tx.input[input_index].asset_issuance,
                witness: TxInWitness::default(),
            }];
        } else {
            tx.input = Vec::with_capacity(self.tx.input.len());
            for (n, input) in self.tx.input.iter().enumerate() {
                tx.input.push(TxIn {
                    previous_output: input.previous_output,
                    is_pegin: input.is_pegin,
                    script_sig: if n == input_index { script_pubkey.clone() } else { Script::new() },
                    sequence: if n != input_index && (sighash == EcdsaSighashType::Single || sighash == EcdsaSighashType::None) { Sequence::ZERO } else { input.sequence },
                    asset_issuance: input.asset_issuance,
                    witness: TxInWitness::default(),
                });
            }
        }
        // ..then all outputs
        tx.output = match sighash {
            EcdsaSighashType::All => self.tx.output.clone(),
            EcdsaSighashType::Single => {
                let output_iter = self.tx.output.iter()
                                      .take(input_index + 1)  // sign all outputs up to and including this one, but erase
                                      .enumerate()            // all of them except for this one
                                      .map(|(n, out)| if n == input_index { out.clone() } else { TxOut::default() });
                output_iter.collect()
            }
            EcdsaSighashType::None => vec![],
            _ => unreachable!()
        };
        // hash the result
        // cannot encode tx directly because of different consensus encoding
        // of elements tx(they include witness flag even for non-witness transactions)
        tx.version.consensus_encode(&mut writer)?;
        // Elements legacy sighashes serialize outpoints without the issuance and
        // pegin flags that normal transaction input encoding places in `vout`.
        VarInt(tx.input.len() as u64).consensus_encode(&mut writer)?;
        for input in &tx.input {
            input.previous_output.consensus_encode(&mut writer)?;
            input.script_sig.consensus_encode(&mut writer)?;
            input.sequence.consensus_encode(&mut writer)?;
            if input.has_issuance() {
                input.asset_issuance.consensus_encode(&mut writer)?;
            }
        }
        if rangeproof {
            VarInt(tx.output.len() as u64).consensus_encode(&mut writer)?;
            for (index, output) in tx.output.iter().enumerate() {
                output.consensus_encode(&mut writer)?;
                if sighash != EcdsaSighashType::Single || index == input_index {
                    output.witness.rangeproof.consensus_encode(&mut writer)?;
                    output.witness.surjection_proof.consensus_encode(&mut writer)?;
                }
            }
        } else {
            tx.output.consensus_encode(&mut writer)?;
        }
        tx.lock_time.consensus_encode(&mut writer)?;

        let sighash_arr = endian::u32_to_array_le(sighash_type.as_u32());
        sighash_arr.consensus_encode(&mut writer)?;
        Ok(())
    }

    /// Computes a signature hash for a given input index with a given sighash flag.
    /// To actually produce a scriptSig, this hash needs to be run through an
    /// ECDSA signer, the `SighashType` appended to the resulting sig, and a
    /// script written around this, but this is the general (and hard) part.
    /// Does not take a mutable reference because it does not do any caching.
    ///
    /// This method uses post-activation [`SighashRangeproofMode::Enabled`]
    /// semantics. Use [`SighashCache::legacy_sighash_with_rangeproof_mode`]
    /// when reproducing pre-activation hashes.
    ///
    /// *Warning* This does NOT attempt to support `OP_CODESEPARATOR`. In general
    /// this would require evaluating `script_pubkey` to determine which separators
    /// get evaluated and which don't, which we don't have the information to
    /// determine.
    ///
    /// # Panics
    /// Panics if `input_index` is greater than or equal to `self.input.len()`
    ///
    pub fn legacy_sighash(
        &self,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
    ) -> Sighash {
        self.legacy_sighash_with_rangeproof_mode(
            input_index,
            script_pubkey,
            sighash_type,
            SighashRangeproofMode::Enabled,
        )
    }

    /// Compute a legacy sighash with explicit
    /// `SCRIPT_SIGHASH_RANGEPROOF` activation semantics.
    pub fn legacy_sighash_with_rangeproof_mode(
        &self,
        input_index: usize,
        script_pubkey: &Script,
        sighash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
    ) -> Sighash {
        let mut engine = sha256d::Hash::engine();
        let single_bug = self
            .legacy_encode_signing_data_to_with_rangeproof_mode(
            &mut engine,
            input_index,
            script_pubkey,
            sighash_type,
            rangeproof_mode,
        )
            .is_sighash_single_bug()
            .expect("engines don't error");
        if single_bug {
            Sighash::from_byte_array([
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ])
        } else {
            Sighash(engine.finalize())
        }
    }

    #[inline]
    fn common_cache(&mut self) -> &CommonCache {
        Self::common_cache_minimal_borrow(&mut self.common_cache, &self.tx)
    }

    fn common_cache_minimal_borrow<'a>(
        common_cache: &'a mut Option<CommonCache>,
        tx: &R,
    ) -> &'a CommonCache {
        common_cache.get_or_insert_with(|| {
            let mut enc_prevouts = sha256::Hash::engine();
            let mut enc_sequences = sha256::Hash::engine();
            for txin in &tx.input {
                txin.previous_output
                    .consensus_encode(&mut enc_prevouts)
                    .unwrap();
                txin.sequence.consensus_encode(&mut enc_sequences).unwrap();
            }
            CommonCache {
                prevouts: sha256::Hash::from_engine(enc_prevouts),
                sequences: sha256::Hash::from_engine(enc_sequences),
                outputs: {
                    let mut enc = sha256::Hash::engine();
                    for txout in &tx.output {
                        txout.consensus_encode(&mut enc).unwrap();
                    }
                    sha256::Hash::from_engine(enc)
                },
                issuances: {
                    let mut enc = sha256::Hash::engine();
                    for txin in &tx.input {
                        if txin.has_issuance() {
                            txin.asset_issuance.consensus_encode(&mut enc).unwrap();
                        } else {
                            0u8.consensus_encode(&mut enc).unwrap();
                        }
                    }
                    sha256::Hash::from_engine(enc)
                },
            }
        })
    }

    fn segwit_cache(&mut self) -> &SegwitCache {
        let common_cache = &mut self.common_cache;
        let tx = &self.tx;
        self.segwit_cache.get_or_insert_with(|| {
            let common_cache = Self::common_cache_minimal_borrow(common_cache, tx);
            SegwitCache {
                prevouts: sha256d::Hash::from_byte_array(
                    sha256::Hash::hash(common_cache.prevouts.as_ref()).to_byte_array(),
                ),
                sequences: sha256d::Hash::from_byte_array(
                    sha256::Hash::hash(common_cache.sequences.as_ref()).to_byte_array(),
                ),
                outputs: sha256d::Hash::from_byte_array(
                    sha256::Hash::hash(common_cache.outputs.as_ref()).to_byte_array(),
                ),
                issuances: sha256d::Hash::from_byte_array(
                    sha256::Hash::hash(common_cache.issuances.as_ref()).to_byte_array(),
                ),
                rangeproofs: {
                    let mut enc = sha256d::Hash::engine();
                    for output in &tx.output {
                        output.witness.rangeproof.consensus_encode(&mut enc).unwrap();
                        output.witness.surjection_proof.consensus_encode(&mut enc).unwrap();
                    }
                    sha256d::Hash::from_engine(enc)
                },
            }
        })
    }

    #[inline]
    fn taproot_cache<T: Borrow<TxOut>>(&mut self, prevouts: &[T]) -> &TaprootCache {
        Self::taproot_cache_minimal_borrow(&mut self.taproot_cache, &self.tx, prevouts)
    }

    fn taproot_cache_minimal_borrow<'a, T: Borrow<TxOut>>(
        taproot_cache: &'a mut Option<TaprootCache>,
        tx: &R,
        prevouts: &[T],
    ) -> &'a TaprootCache {
        taproot_cache.get_or_insert_with(|| {
            let mut enc_asset_amounts = sha256::Hash::engine();
            let mut enc_script_pubkeys = sha256::Hash::engine();
            let mut enc_outpoint_flags = sha256::Hash::engine();
            let mut enc_issuance_rangeproofs = sha256::Hash::engine();
            let mut enc_output_witnesses = sha256::Hash::engine();
            for prevout in prevouts {
                prevout.borrow().asset.consensus_encode(&mut enc_asset_amounts).unwrap();
                prevout.borrow().value.consensus_encode(&mut enc_asset_amounts).unwrap();
                prevout
                    .borrow()
                    .script_pubkey
                    .consensus_encode(&mut enc_script_pubkeys)
                    .unwrap();
            }
            for inp in &tx.input {
                inp.outpoint_flag()
                    .consensus_encode(&mut enc_outpoint_flags).unwrap();
                inp.witness.amount_rangeproof
                    .consensus_encode(&mut enc_issuance_rangeproofs).unwrap();
                inp.witness.inflation_keys_rangeproof
                    .consensus_encode(&mut enc_issuance_rangeproofs).unwrap();
            }

            for out in &tx.output {
                out.witness.surjection_proof.consensus_encode(&mut enc_output_witnesses).unwrap();
                out.witness.rangeproof.consensus_encode(&mut enc_output_witnesses).unwrap();
            }
            TaprootCache {
                asset_amounts: sha256::Hash::from_engine(enc_asset_amounts),
                script_pubkeys: sha256::Hash::from_engine(enc_script_pubkeys),
                outpoint_flags: sha256::Hash::from_engine(enc_outpoint_flags),
                issuance_rangeproofs: sha256::Hash::from_engine(enc_issuance_rangeproofs),
                output_witnesses: sha256::Hash::from_engine(enc_output_witnesses),
            }
        })
    }
}

impl<R: DerefMut<Target = Transaction>> SighashCache<R> {
    /// When the `SighashCache` is initialized with a mutable reference to a transaction instead of a
    /// regular reference, this method is available to allow modification to the witnesses.
    ///
    /// This allows in-line signing such as
    /// ```
    /// use elements::{LockTime, Transaction, EcdsaSighashType};
    /// use elements::sighash::SighashCache;
    /// use elements::Script;
    /// use elements::confidential;
    ///
    /// let mut tx_to_sign = Transaction { version: 2, lock_time: LockTime::ZERO, input: Vec::new(), output: Vec::new() };
    /// let input_count = tx_to_sign.input.len();
    ///
    /// let mut sig_hasher = SighashCache::new(&mut tx_to_sign);
    /// for inp in 0..input_count {
    ///     let prevout_script = Script::new();
    ///     let _sighash = sig_hasher.segwitv0_sighash(inp, &prevout_script, confidential::Value::Explicit(42), EcdsaSighashType::All);
    ///     // ... sign the sighash
    ///     sig_hasher.witness_mut(inp).unwrap().push(Vec::new());
    /// }
    /// ```
    pub fn witness_mut(&mut self, input_index: usize) -> Option<&mut crate::Witness> {
        self.tx.input.get_mut(input_index).map(|i| &mut i.witness.script_witness)
    }
}

impl From<encode::Error> for Error {
    fn from(e: encode::Error) -> Self {
        Error::Encode(e)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// The `Annex` struct is a slice wrapper enforcing first byte to be `0x50`
pub struct Annex<'a>(&'a [u8]);

impl<'a> Annex<'a> {
    /// Creates a new `Annex` struct checking the first byte is `0x50`
    pub fn new(annex_bytes: &'a [u8]) -> Result<Self, Error> {
        if annex_bytes.first() == Some(&0x50) {
            Ok(Annex(annex_bytes))
        } else {
            Err(Error::WrongAnnex)
        }
    }

    /// Returns the Annex bytes data (including first byte `0x50`)
    pub fn as_bytes(&self) -> &[u8] {
        self.0
    }
}

impl Encodable for Annex<'_> {
    fn consensus_encode<W: io::Write>(&self, writer: W) -> Result<usize, encode::Error> {
        encode::consensus_encode_with_size(self.0, writer)
    }
}

/// Hashtype of an input's signature, encoded in the last byte of the signature
/// Fixed values so they can be casted as integer types for encoding
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub enum SchnorrSighashType {
    /// 0x0: Used when not explicitly specified, defaulting to [`SchnorrSighashType::All`]
    Default = 0x00,
    /// 0x1: Sign all outputs
    All = 0x01,
    /// 0x2: Sign no outputs --- anyone can choose the destination
    None = 0x02,
    /// 0x3: Sign the output whose index matches this input's index. If none exists,
    /// sign the hash `0000000000000000000000000000000000000000000000000000000000000001`.
    /// (This rule is probably an unintentional C++ism, but it's consensus so we have
    /// to follow it.)
    Single = 0x03,
    /// 0x81: Sign all outputs but only this input
    AllPlusAnyoneCanPay = 0x81,
    /// 0x82: Sign no outputs and only this input
    NonePlusAnyoneCanPay = 0x82,
    /// 0x83: Sign one output and only this input (see `Single` for what "one output" means)
    SinglePlusAnyoneCanPay = 0x83,

    /// Reserved for future use, `#[non_exhaustive]` is not available with current MSRV
    Reserved = 0xFF,
}

serde_string_impl!(SchnorrSighashType, "a SchnorrSighashType data");

impl SchnorrSighashType {
    /// Break the sighash flag into the "real" sighash flag and the ANYONECANPAY boolean
    pub fn split_anyonecanpay_flag(self) -> (SchnorrSighashType, bool) {
        match self {
            SchnorrSighashType::Default => (SchnorrSighashType::Default, false),
            SchnorrSighashType::All => (SchnorrSighashType::All, false),
            SchnorrSighashType::None => (SchnorrSighashType::None, false),
            SchnorrSighashType::Single => (SchnorrSighashType::Single, false),
            SchnorrSighashType::AllPlusAnyoneCanPay => (SchnorrSighashType::All, true),
            SchnorrSighashType::NonePlusAnyoneCanPay => (SchnorrSighashType::None, true),
            SchnorrSighashType::SinglePlusAnyoneCanPay => (SchnorrSighashType::Single, true),
            SchnorrSighashType::Reserved => (SchnorrSighashType::Reserved, false),
        }
    }

    /// Create a [`SchnorrSighashType`] from raw u8
    pub fn from_u8(hash_ty: u8) -> Option<Self> {
        match hash_ty {
            0x00 => Some(SchnorrSighashType::Default),
            0x01 => Some(SchnorrSighashType::All),
            0x02 => Some(SchnorrSighashType::None),
            0x03 => Some(SchnorrSighashType::Single),
            0x81 => Some(SchnorrSighashType::AllPlusAnyoneCanPay),
            0x82 => Some(SchnorrSighashType::NonePlusAnyoneCanPay),
            0x83 => Some(SchnorrSighashType::SinglePlusAnyoneCanPay),
            _x => None,
        }
    }
}

impl fmt::Display for SchnorrSighashType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            SchnorrSighashType::Default => "SIGHASH_DEFAULT",
            SchnorrSighashType::All => "SIGHASH_ALL",
            SchnorrSighashType::None => "SIGHASH_NONE",
            SchnorrSighashType::Single => "SIGHASH_SINGLE",
            SchnorrSighashType::AllPlusAnyoneCanPay => "SIGHASH_ALL|SIGHASH_ANYONECANPAY",
            SchnorrSighashType::NonePlusAnyoneCanPay => "SIGHASH_NONE|SIGHASH_ANYONECANPAY",
            SchnorrSighashType::SinglePlusAnyoneCanPay => "SIGHASH_SINGLE|SIGHASH_ANYONECANPAY",
            SchnorrSighashType::Reserved => "SIGHASH_RESERVED",
        };
        f.write_str(s)
    }
}

impl std::str::FromStr for SchnorrSighashType {
    type Err = SighashTypeParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "SIGHASH_DEFAULT" => Ok(SchnorrSighashType::Default),
            "SIGHASH_ALL" => Ok(SchnorrSighashType::All),
            "SIGHASH_NONE" => Ok(SchnorrSighashType::None),
            "SIGHASH_SINGLE" => Ok(SchnorrSighashType::Single),
            "SIGHASH_ALL|SIGHASH_ANYONECANPAY" => Ok(SchnorrSighashType::AllPlusAnyoneCanPay),
            "SIGHASH_NONE|SIGHASH_ANYONECANPAY" => Ok(SchnorrSighashType::NonePlusAnyoneCanPay),
            "SIGHASH_SINGLE|SIGHASH_ANYONECANPAY" => Ok(SchnorrSighashType::SinglePlusAnyoneCanPay),
            "SIGHASH_RESERVED" => Ok(SchnorrSighashType::Reserved),
            _ => Err(SighashTypeParseError{ unrecognized: s.to_owned() }),
        }
    }
}


#[cfg(test)]
mod tests{
    use super::*;
    use crate::encode::deserialize;
    use std::str::FromStr;

    fn test_segwit_sighash_with_rangeproof_mode(
        tx: &str,
        script: &str,
        input_index: usize,
        value: &str,
        hash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
        expected_result: &str,
    ) {
        let tx: Transaction = deserialize(&hex::decode_to_vec(tx).unwrap()).unwrap();
        let script = Script::from(hex::decode_to_vec(script).unwrap());
        let raw_expected = hex::decode_to_array(expected_result).unwrap();
        let expected_result = Sighash::from_byte_array(raw_expected);

        let mut cache = SighashCache::new(&tx);
        let value : confidential::Value = deserialize(&hex::decode_to_vec(value).unwrap()).unwrap();
        let actual_result = cache.segwitv0_sighash_with_rangeproof_mode(
            input_index,
            &script,
            value,
            hash_type,
            rangeproof_mode,
        );
        assert_eq!(actual_result, expected_result);
    }

    fn test_segwit_sighash(tx: &str, script: &str, input_index: usize, value: &str, hash_type: EcdsaSighashType, expected_result: &str) {
        test_segwit_sighash_with_rangeproof_mode(
            tx,
            script,
            input_index,
            value,
            hash_type,
            SighashRangeproofMode::Enabled,
            expected_result,
        );
    }

    #[test]
    fn test_segwit_sighashes(){
        // generated by script(example_test.py) at https://github.com/sanket1729/elements/commit/8fb4eb9e6020adaf20f3ec25055ffa905ba5b5c4
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::All, "e201b4019129a03ca0304989731c6dccde232c854d86fce999b7411da1e90048");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::None, "bfc6599816673083334ae82ac3459a2d0fef478d3e580e3ae203a28347502cb4");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::Single, "4bc8546e32d31c5415444138184696e80f49e537a083bfcc89be2ab41d962e76");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::AllPlusAnyoneCanPay, "b70ba5f4a1c2c48cd7f2104b2baa6a5c97987eb560916d39a5d427deb8b1dc2a");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::NonePlusAnyoneCanPay, "6d6a4749c09ffd9a8df4c5de5d939325d896009e18f94bb095c9d7d695a8465e");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::SinglePlusAnyoneCanPay, "7fc34367b42bf0e2bb78d8c20f45a64b81b2d4fbb59cbff8649322f619e88a0f");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::All, "71141639d982f1a1a8901e32fb1a9e15a0ea168b37d33300a3c9619fc3767388");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::None, "00730922d0e1d55b4b5fffafd087b06aeb44c4cedb58d8e182cbb9b87382cddb");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::Single, "100063ea0923ef4432dd51c5756383530f28b31ffe9d50b59a11b94a63c84c78");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::AllPlusAnyoneCanPay, "e1c4ddf5f723759f7d99d4f162155119160b1c6b765fdbdb25aedb2059769b74");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::NonePlusAnyoneCanPay, "b0be275e0c69e89ef5c482fdf330038c3b2994ebce3e3639bb81456d15a95a7a");
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "010000000005f5e100", EcdsaSighashType::SinglePlusAnyoneCanPay, "27c293da7a0f08e161fa2a77aeefa6743c929905597b5bcb28f2015fe648aa0c");

        // Test a issuance test with only sighash all
        test_segwit_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000003e801000000000000000a0201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, "0850863ad64a87ae8a2fe83c1af1a8403cb53f53e486d8511dad8a04887e5b2352", EcdsaSighashType::All, "ea946ee417d5a16a1038b2c3b54d1b7b12a9f98c0dcb4684bf005eb1c27d0c92");
    }


    fn test_legacy_sighash_with_rangeproof_mode(
        tx: &str,
        script: &str,
        input_index: usize,
        hash_type: EcdsaSighashType,
        rangeproof_mode: SighashRangeproofMode,
        expected_result: &str,
    ) {
        let tx: Transaction = deserialize(&hex::decode_to_vec(tx).unwrap()).unwrap();
        let script = Script::from(hex::decode_to_vec(script).unwrap());
        let raw_expected = hex::decode_to_array(expected_result).unwrap();
        let expected_result = Sighash::from_byte_array(raw_expected);
        let sighash_cache = SighashCache::new(&tx);
        let actual_result = sighash_cache.legacy_sighash_with_rangeproof_mode(
            input_index,
            &script,
            hash_type,
            rangeproof_mode,
        );
        assert_eq!(actual_result, expected_result);
    }

    fn test_legacy_sighash(tx: &str, script: &str, input_index: usize, hash_type: EcdsaSighashType, expected_result: &str) {
        test_legacy_sighash_with_rangeproof_mode(
            tx,
            script,
            input_index,
            hash_type,
            SighashRangeproofMode::Enabled,
            expected_result,
        );
    }

    #[test]
    fn test_legacy_sighashes(){
        // generated by script(example_test.py) at https://github.com/sanket1729/elements/commit/5ddfb5a749e85b71c961d29d5689d692ef7cee4b
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::All, "769ad754a77282712895475eb17251bcb8f3cc35dc13406fa1188ef2707556cf");
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::None, "b399ca018b4fec7d94e47092b72d25983db2d0d16eaa6a672050add66077ef40");
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::Single, "4efef74996f840ed104c0b69461f33da2e364288f3015c55b2516a68e3ee60bc");
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::AllPlusAnyoneCanPay, "a70a59ae29f1d9f4461f12e730e5cb75d3a75312666e8d911584aebb8e4afc5c");
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::NonePlusAnyoneCanPay, "5f3694a35f3b994639d3fb1f6214ec166f9e0721c7ab3f216e465b9b2728d834");
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af0000000000000000000201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::SinglePlusAnyoneCanPay, "4c18486c473dc31c264c477c55e9c17d70fddb9f567c7d411ce922261577167c");

        // Test a issuance test with only sighash all
        test_legacy_sighash("010000000001715df5ccebaf02ff18d6fae7263fa69fed5de59c900f4749556eba41bc7bf2af000000800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000003e801000000000000000a0201230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000124101100001f5175517551755175517551755175517551755175517551755175517551755101230f4f5d4b7c6fa845806ee4f67713459e1b69e8e60fcee2e4940c7a0d5de1b2010000000005f5e100000000000000", "76a914f54a5851e9372b87810a8e60cdd2e7cfd80b6e3188ac", 0, EcdsaSighashType::All, "7df7980d94f19d1c7e4f64c1a5fa1da57d2fdeb2452bcf77feab35246aac8030");
    }

    #[test]
    fn legacy_sighash_omits_pegin_outpoint_flag() {
        let tx = Transaction {
            version: 2,
            lock_time: crate::LockTime::ZERO,
            input: vec![TxIn {
                previous_output: crate::OutPoint::new(crate::Txid::from_byte_array([0; 32]), 7),
                is_pegin: true,
                script_sig: Script::new(),
                sequence: Sequence::MAX,
                asset_issuance: crate::AssetIssuance::default(),
                witness: TxInWitness::default(),
            }],
            output: vec![],
        };
        let mut preimage = Vec::new();
        SighashCache::new(&tx)
            .encode_legacy_signing_data_to(
                &mut preimage,
                0,
                &Script::new(),
                EcdsaSighashType::All,
            )
            .unwrap();

        assert_eq!(&preimage[37..41], &[7, 0, 0, 0]);
    }

    #[test]
    fn legacy_sighash_single_returns_uint256_one() {
        let tx = Transaction {
            version: 2,
            lock_time: crate::LockTime::ZERO,
            input: vec![TxIn {
                previous_output: crate::OutPoint::new(crate::Txid::from_byte_array([0; 32]), 7),
                is_pegin: false,
                script_sig: Script::new(),
                sequence: Sequence::MAX,
                asset_issuance: crate::AssetIssuance::default(),
                witness: TxInWitness::default(),
            }],
            output: vec![],
        };
        let expected = Sighash::from_byte_array([
            1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ]);
        let hash_types = [
            EcdsaSighashType::Single,
            EcdsaSighashType::SinglePlusRangeproof,
            EcdsaSighashType::SinglePlusAnyoneCanPay,
            EcdsaSighashType::SinglePlusAnyoneCanPayPlusRangeproof,
        ];
        let modes = [
            SighashRangeproofMode::Disabled,
            SighashRangeproofMode::Enabled,
        ];

        for hash_type in hash_types {
            assert_eq!(
                SighashCache::new(&tx).legacy_sighash(0, &Script::new(), hash_type),
                expected,
            );

            for mode in modes {
                assert_eq!(
                    SighashCache::new(&tx).legacy_sighash_with_rangeproof_mode(
                        0,
                        &Script::new(),
                        hash_type,
                        mode,
                    ),
                    expected,
                );

                let mut preimage = Vec::new();
                let is_single_bug = SighashCache::new(&tx)
                    .legacy_encode_signing_data_to_with_rangeproof_mode(
                        &mut preimage,
                        0,
                        &Script::new(),
                        hash_type,
                        mode,
                    )
                    .is_sighash_single_bug()
                    .unwrap();
                assert!(is_single_bug);
                assert!(preimage.is_empty());
            }

            let mut compatibility_preimage = Vec::new();
            let error = SighashCache::new(&tx)
                .encode_legacy_signing_data_to(
                    &mut compatibility_preimage,
                    0,
                    &Script::new(),
                    hash_type,
                )
                .unwrap_err();
            assert!(matches!(
                error,
                encode::Error::Io(ref error) if error.kind() == io::ErrorKind::InvalidInput
            ));
            assert!(compatibility_preimage.is_empty());
        }
    }

    #[test]
    fn test_rangeproof_sighashes() {
        let tx = include_str!("../examples/test_vector/raw_blind/extracted_tx.hex").trim();
        let script = "76a9142d2186719dc0c245e7b4a30f17834f371ca7377c88ac";
        let value = "0980610bc88e4ab656c2e5ff6fe6c6a39967a1c0d386682240c5ff039148dc335d";
        let vectors = [
            (EcdsaSighashType::AllPlusRangeproof, "4d0a5d82ff74812f5235b42bfdf809864dd2695f13d1c5921a4606138da302eb", "c4a6b4bedfdc35eba3e5e1ccf270d20ccb4d3ac382b964a5d6be0367a7b6bcdf"),
            (EcdsaSighashType::NonePlusRangeproof, "87ab326e501e1431a99e3496aecf2d53876cc23f67f3ee533c013d64472d74f5", "cf9303742059d3a0a44ba4e21538aa2b39a976e53c62d7994615c7c990df94fa"),
            (EcdsaSighashType::SinglePlusRangeproof, "76b0078ad98f45574b87228c2f1b6986050c93fec4ba6c08fb762ed1277e4273", "578db085c8ae8ba0fe18623818fe7956ed68506b429fa9d528fdd8ffa93ac768"),
            (EcdsaSighashType::AllPlusAnyoneCanPayPlusRangeproof, "c1b39c7de724231badc251fa28635a716706b35577fd7765459bf7c56c1e3c56", "701b8a02ee58ce8e6a420cc5639f26087549f8232d8d5050eca603aa9a0163a4"),
            (EcdsaSighashType::NonePlusAnyoneCanPayPlusRangeproof, "182e33c3aee200d59ba71de16e034d3cc37b9e0f0317239235bd3d54baea97ec", "30543b573bb956e6e4cfaf2dfddad144cc37f6cdc9667031a3a5a224f566e101"),
            (EcdsaSighashType::SinglePlusAnyoneCanPayPlusRangeproof, "d40fee5bb66e2ad1e575e40d73bd542f9047eb76558a49738c5a34442df2e9b5", "d9ca5ff22b0d58b53e34d5bddcc6eec1fa161076332a2437311d8cb1592f45ec"),
        ];

        for (hash_type, expected_segwit, expected_legacy) in vectors {
            test_segwit_sighash(tx, script, 0, value, hash_type, expected_segwit);
            test_legacy_sighash(tx, script, 0, hash_type, expected_legacy);
        }

        // Elements Core omits proof fields after SINGLE placeholder outputs.
        let script_1 = "76a91403bb7619d51d2af2c5538d3908ead081a7ef2b2b88ac";
        test_legacy_sighash(tx, script_1, 1, EcdsaSighashType::SinglePlusRangeproof, "a5b3d854d7c2e1193aa2bad8f829a9c1c5b4bc71488e3b567b5724cc87ec065f");
        test_legacy_sighash(tx, script_1, 1, EcdsaSighashType::SinglePlusAnyoneCanPayPlusRangeproof, "718fdd392e3353cd36eed0124d325ed136e8946c62f11f529cde048697f1c33f");
    }

    #[test]
    fn test_rangeproof_sighashes_before_activation() {
        let tx = include_str!("../examples/test_vector/raw_blind/extracted_tx.hex").trim();
        let script = "76a9142d2186719dc0c245e7b4a30f17834f371ca7377c88ac";
        let value = "0980610bc88e4ab656c2e5ff6fe6c6a39967a1c0d386682240c5ff039148dc335d";
        let vectors = [
            (EcdsaSighashType::AllPlusRangeproof, "637f81c67055f744a16db2172d8beee003c9e0af9cad9f54255eab2c1d2dbaf8", "6aea604e49958abd016b6ec0058cf3e2ab4fe407a9dfec21d6ae81e1419a54ae"),
            (EcdsaSighashType::NonePlusRangeproof, "8aad97fefbf951fa220353a3b2c072600ab653583cb3eb77a27b4a8ed15963a7", "cf9303742059d3a0a44ba4e21538aa2b39a976e53c62d7994615c7c990df94fa"),
            (EcdsaSighashType::SinglePlusRangeproof, "47a9a287895b359dd1cc2c348af5976642697e8a4cdae6d95201cb9ca20c47d3", "efd64f12ba6b325017fefd642a83248adac4c2a15af0f52ddd27e6268838a5fd"),
            (EcdsaSighashType::AllPlusAnyoneCanPayPlusRangeproof, "d6c31419347bad60c908c023755b9e6ec7d8b68b4d414f59613d2ba040562c54", "fa4fa93e85028a6f1684e77971b45ce08cbf450119c909bd4a312b200ca039ef"),
            (EcdsaSighashType::NonePlusAnyoneCanPayPlusRangeproof, "17cf578244d0d75120feb82825290531bf59c660a22bbfef64261e898ad8ae0c", "30543b573bb956e6e4cfaf2dfddad144cc37f6cdc9667031a3a5a224f566e101"),
            (EcdsaSighashType::SinglePlusAnyoneCanPayPlusRangeproof, "d35dc5759ba7ec14ec43a6743f5a010363145c603c783299e70e47f7aa7e4871", "c7c375601508159a6832c430a7c554fc42e47268c27382f96065d8c7859b73c5"),
        ];

        for (hash_type, expected_segwit, expected_legacy) in vectors {
            test_segwit_sighash_with_rangeproof_mode(
                tx,
                script,
                0,
                value,
                hash_type,
                SighashRangeproofMode::Disabled,
                expected_segwit,
            );
            test_legacy_sighash_with_rangeproof_mode(
                tx,
                script,
                0,
                hash_type,
                SighashRangeproofMode::Disabled,
                expected_legacy,
            );
        }
    }

    #[test]
    fn rangeproof_sighash_with_issuance_and_pegin_matches_core() {
        let tx_hex = include_str!("../examples/test_vector/raw_blind/extracted_tx.hex").trim();
        let mut tx: Transaction = deserialize(&hex::decode_to_vec(tx_hex).unwrap()).unwrap();
        tx.input.truncate(1);
        tx.input[0].is_pegin = true;
        tx.input[0].asset_issuance = crate::AssetIssuance {
            asset_blinding_nonce: crate::AssetBlindingNonce::NEW_ISSUANCE,
            asset_entropy: crate::AssetEntropy::NEW_ISSUANCE,
            amount: confidential::Value::Explicit(1),
            inflation_keys: confidential::Value::Null,
        };
        let script = Script::from(
            hex::decode_to_vec("76a9142d2186719dc0c245e7b4a30f17834f371ca7377c88ac").unwrap()
        );
        let value: confidential::Value = deserialize(
            &hex::decode_to_vec("0980610bc88e4ab656c2e5ff6fe6c6a39967a1c0d386682240c5ff039148dc335d").unwrap()
        ).unwrap();
        let vectors = [
            (
                SighashRangeproofMode::Disabled,
                "2f7d731194e7932b8d12265cec15d94713138f30ea88ab98754df3d6d0558543",
                "29a16d4f9e7684f461da9050df14a5a46a4894c88c6afd735481560f5bfe3016",
            ),
            (
                SighashRangeproofMode::Enabled,
                "45ad6fac7312d3791194dab0aac049ae3b84cb44b8c2eedaf2effaf0570375cd",
                "2d26bb50748cc968da5a9e7187e0036e3acdf08344b978c9b05667ebfc087de3",
            ),
        ];

        for (mode, expected_segwit, expected_legacy) in vectors {
            let expected_segwit =
                Sighash::from_byte_array(hex::decode_to_array(expected_segwit).unwrap());
            let expected_legacy =
                Sighash::from_byte_array(hex::decode_to_array(expected_legacy).unwrap());
            assert_eq!(
                SighashCache::new(&tx).segwitv0_sighash_with_rangeproof_mode(
                    0,
                    &script,
                    value,
                    EcdsaSighashType::AllPlusRangeproof,
                    mode,
                ),
                expected_segwit,
            );
            assert_eq!(
                SighashCache::new(&tx).legacy_sighash_with_rangeproof_mode(
                    0,
                    &script,
                    EcdsaSighashType::AllPlusRangeproof,
                    mode,
                ),
                expected_legacy,
            );
        }
    }

    #[test]
    fn rangeproof_sighash_commits_to_selected_output_proofs() {
        let tx_hex = include_str!("../examples/test_vector/raw_blind/extracted_tx.hex").trim();
        let tx: Transaction = deserialize(&hex::decode_to_vec(tx_hex).unwrap()).unwrap();
        let script = Script::from(
            hex::decode_to_vec("76a9142d2186719dc0c245e7b4a30f17834f371ca7377c88ac").unwrap()
        );
        let value: confidential::Value = deserialize(
            &hex::decode_to_vec("0980610bc88e4ab656c2e5ff6fe6c6a39967a1c0d386682240c5ff039148dc335d").unwrap()
        ).unwrap();

        let plain = SighashCache::new(&tx)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::All);
        let protected = SighashCache::new(&tx)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::AllPlusRangeproof);
        let protected_legacy = SighashCache::new(&tx)
            .legacy_sighash(0, &script, EcdsaSighashType::AllPlusRangeproof);

        let mut selected_mutation = tx.clone();
        selected_mutation.output[0].witness.rangeproof = confidential::RangeProof::EMPTY;
        let mutated_plain = SighashCache::new(&selected_mutation)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::All);
        let mutated_protected = SighashCache::new(&selected_mutation)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::AllPlusRangeproof);
        let mutated_protected_legacy = SighashCache::new(&selected_mutation)
            .legacy_sighash(0, &script, EcdsaSighashType::AllPlusRangeproof);
        assert_eq!(plain, mutated_plain);
        assert_ne!(protected, mutated_protected);
        assert_ne!(protected_legacy, mutated_protected_legacy);

        let mut surjection_mutation = tx.clone();
        surjection_mutation.output[0].witness.surjection_proof =
            confidential::SurjectionProof::EMPTY;
        let mutated_plain = SighashCache::new(&surjection_mutation)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::All);
        let mutated_protected = SighashCache::new(&surjection_mutation)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::AllPlusRangeproof);
        let mutated_protected_legacy = SighashCache::new(&surjection_mutation)
            .legacy_sighash(0, &script, EcdsaSighashType::AllPlusRangeproof);
        assert_eq!(plain, mutated_plain);
        assert_ne!(protected, mutated_protected);
        assert_ne!(protected_legacy, mutated_protected_legacy);

        let pre_activation = SighashCache::new(&tx).segwitv0_sighash_with_rangeproof_mode(
            0,
            &script,
            value,
            EcdsaSighashType::AllPlusRangeproof,
            SighashRangeproofMode::Disabled,
        );
        let mutated_pre_activation =
            SighashCache::new(&surjection_mutation).segwitv0_sighash_with_rangeproof_mode(
                0,
                &script,
                value,
                EcdsaSighashType::AllPlusRangeproof,
                SighashRangeproofMode::Disabled,
            );
        assert_eq!(pre_activation, mutated_pre_activation);

        let single = SighashCache::new(&tx)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::SinglePlusRangeproof);
        let mut unselected_mutation = tx.clone();
        unselected_mutation.output[1].witness.rangeproof = confidential::RangeProof::EMPTY;
        let mutated_single = SighashCache::new(&unselected_mutation)
            .segwitv0_sighash(0, &script, value, EcdsaSighashType::SinglePlusRangeproof);
        assert_eq!(single, mutated_single);
    }

    #[test]
    fn rangeproof_mode_preserves_wrappers_and_ordinary_sighashes() {
        let tx_hex = include_str!("../examples/test_vector/raw_blind/extracted_tx.hex").trim();
        let tx: Transaction = deserialize(&hex::decode_to_vec(tx_hex).unwrap()).unwrap();
        let script = Script::from(
            hex::decode_to_vec("76a9142d2186719dc0c245e7b4a30f17834f371ca7377c88ac").unwrap()
        );
        let value: confidential::Value = deserialize(
            &hex::decode_to_vec("0980610bc88e4ab656c2e5ff6fe6c6a39967a1c0d386682240c5ff039148dc335d").unwrap()
        ).unwrap();

        let default = SighashCache::new(&tx).segwitv0_sighash(
            0,
            &script,
            value,
            EcdsaSighashType::AllPlusRangeproof,
        );
        let enabled = SighashCache::new(&tx).segwitv0_sighash_with_rangeproof_mode(
            0,
            &script,
            value,
            EcdsaSighashType::AllPlusRangeproof,
            SighashRangeproofMode::Enabled,
        );
        assert_eq!(default, enabled);
        assert_eq!(
            SighashCache::new(&tx)
                .legacy_sighash(0, &script, EcdsaSighashType::AllPlusRangeproof),
            SighashCache::new(&tx).legacy_sighash_with_rangeproof_mode(
                0,
                &script,
                EcdsaSighashType::AllPlusRangeproof,
                SighashRangeproofMode::Enabled,
            ),
        );

        let ordinary_types = [
            EcdsaSighashType::All,
            EcdsaSighashType::None,
            EcdsaSighashType::Single,
            EcdsaSighashType::AllPlusAnyoneCanPay,
            EcdsaSighashType::NonePlusAnyoneCanPay,
            EcdsaSighashType::SinglePlusAnyoneCanPay,
        ];
        for hash_type in ordinary_types {
            let enabled = SighashCache::new(&tx).segwitv0_sighash_with_rangeproof_mode(
                0,
                &script,
                value,
                hash_type,
                SighashRangeproofMode::Enabled,
            );
            let disabled = SighashCache::new(&tx).segwitv0_sighash_with_rangeproof_mode(
                0,
                &script,
                value,
                hash_type,
                SighashRangeproofMode::Disabled,
            );
            assert_eq!(enabled, disabled);

            let enabled = SighashCache::new(&tx).legacy_sighash_with_rangeproof_mode(
                0,
                &script,
                hash_type,
                SighashRangeproofMode::Enabled,
            );
            let disabled = SighashCache::new(&tx).legacy_sighash_with_rangeproof_mode(
                0,
                &script,
                hash_type,
                SighashRangeproofMode::Disabled,
            );
            assert_eq!(enabled, disabled);
        }
    }

    #[test]
    fn rangeproof_sighash_types_roundtrip_through_pset() {
        use crate::pset::PsbtSighashType;

        let vectors = [
            (0x41, EcdsaSighashType::AllPlusRangeproof, "SIGHASH_ALL|SIGHASH_RANGEPROOF"),
            (0x42, EcdsaSighashType::NonePlusRangeproof, "SIGHASH_NONE|SIGHASH_RANGEPROOF"),
            (0x43, EcdsaSighashType::SinglePlusRangeproof, "SIGHASH_SINGLE|SIGHASH_RANGEPROOF"),
            (0xc1, EcdsaSighashType::AllPlusAnyoneCanPayPlusRangeproof, "SIGHASH_ALL|SIGHASH_ANYONECANPAY|SIGHASH_RANGEPROOF"),
            (0xc2, EcdsaSighashType::NonePlusAnyoneCanPayPlusRangeproof, "SIGHASH_NONE|SIGHASH_ANYONECANPAY|SIGHASH_RANGEPROOF"),
            (0xc3, EcdsaSighashType::SinglePlusAnyoneCanPayPlusRangeproof, "SIGHASH_SINGLE|SIGHASH_ANYONECANPAY|SIGHASH_RANGEPROOF"),
        ];

        for (raw, hash_type, text) in vectors {
            assert_eq!(EcdsaSighashType::from_u32(raw), hash_type);
            assert_eq!(EcdsaSighashType::from_standard(raw), Ok(hash_type));
            assert_eq!(hash_type.to_string(), text);
            assert_eq!(EcdsaSighashType::from_str(text), Ok(hash_type));

            let pset_type = PsbtSighashType::from(hash_type);
            assert_eq!(pset_type.to_u32(), raw);
            assert_eq!(pset_type.ecdsa_hash_ty(), Some(hash_type));
            assert_eq!(pset_type.to_string(), text);
            assert_eq!(PsbtSighashType::from_str(text).unwrap(), pset_type);
        }
    }
}

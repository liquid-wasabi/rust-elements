// SPDX-License-Identifier: MIT OR Apache-2.0

//! Pegin Witnesses

use core::fmt;
use std::io;

// lol should these be accessible from a more convenient path?
use bitcoin::block::BlockHashDecoder as GenesisHashDecoder;
use bitcoin::block::{
    BlockHashDecoderError as GenesisHashDecoderError, BlockHashEncoder as GenesisHashEncoder,
};
use bitcoin::hashes::Hash as _;
use hashes::encoding::UnexpectedEofError;

use crate::confidential::{Asset, Nonce, Value};
use crate::{encode, encoding, AssetId, Script, TxOut, TxOutWitness};

const TOTAL_PEGIN_LENGTH: usize = 6;

/// A pegin witness, which must be either a stack of 6 well-formed pieces of pegin data, or an empty witness stack.
#[derive(Default, Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct PeginWitness {
    inner: Option<PeginData>,
}

impl PeginWitness {
    /// An empty pegin witness.
    pub const EMPTY: Self = Self { inner: None };

    /// A pegin witness containing the given data.
    pub fn new(data: PeginData) -> Self { Self { inner: Some(data) } }

    /// Accessor for the pegin witness data.
    pub fn data(&self) -> Option<&PeginData> { self.inner.as_ref() }

    /// Accessor for the pegin witness data.
    pub fn into_data(self) -> Option<PeginData> { self.inner }

    /// Whether this pegin witness is empty (no pegin).
    pub fn is_empty(&self) -> bool { self.inner.is_none() }

    /// The number of witness elements in the [`PeginWitness`].
    pub fn len(&self) -> usize {
        if self.inner.is_some() {
            TOTAL_PEGIN_LENGTH
        } else {
            0
        }
    }

    /// The number of bytes used to encode the [`PeginWitness`].
    pub fn encoded_size(&self) -> usize {
        use encoding::{Encode as _, ExactSizeEncoder as _};
        match self.inner {
            Some(ref data) => data.encoder().len(),
            None => 1,
        }
    }
}

/// Encoder for the [`PeginWitness`] type.
#[derive(Clone, Debug)]
pub struct PeginWitnessEncoder<'e>(PeginWitnessEncoderInner<'e>);

#[derive(Clone, Debug)]
#[allow(clippy::large_enum_variant)]
enum PeginWitnessEncoderInner<'e> {
    Pegin(PeginDataEncoder<'e>),
    Empty(encoding::CompactSizeEncoder),
}

impl encoding::Encoder for PeginWitnessEncoder<'_> {
    fn current_chunk(&self) -> &[u8] {
        use PeginWitnessEncoderInner as Inner;
        match self.0 {
            Inner::Pegin(ref enc) => enc.current_chunk(),
            Inner::Empty(ref enc) => enc.current_chunk(),
        }
    }

    fn advance(&mut self) -> encoding::EncoderStatus {
        use PeginWitnessEncoderInner as Inner;
        match self.0 {
            Inner::Pegin(ref mut enc) => enc.advance(),
            Inner::Empty(ref mut enc) => enc.advance(),
        }
    }
}

impl encoding::ExactSizeEncoder for PeginWitnessEncoder<'_> {
    fn len(&self) -> usize {
        use PeginWitnessEncoderInner as Inner;
        match self.0 {
            Inner::Pegin(ref enc) => enc.len(),
            Inner::Empty(ref enc) => enc.len(),
        }
    }
}

impl encoding::Encode for PeginWitness {
    type Encoder<'e> = PeginWitnessEncoder<'e>;

    fn encoder(&self) -> Self::Encoder<'_> {
        match self.inner {
            Some(ref data) => PeginWitnessEncoder(PeginWitnessEncoderInner::Pegin(data.encoder())),
            None => PeginWitnessEncoder(PeginWitnessEncoderInner::Empty(
                encoding::CompactSizeEncoder::new(0),
            )),
        }
    }
}

/// Decoder for the [`PeginWitness`] type.
#[derive(Default)]
pub struct PeginWitnessDecoder(PeginWitnessDecoderInner);

#[derive(Default)]
#[allow(clippy::large_enum_variant)]
enum PeginWitnessDecoderInner {
    #[default]
    Undetermined,
    Empty,
    Pegin(PeginDataDecoder),
}

impl encoding::Decoder for PeginWitnessDecoder {
    type Output = PeginWitness;
    type Error = PeginWitnessDecoderError;

    fn push_bytes(&mut self, bytes: &mut &[u8]) -> Result<encoding::DecoderStatus, Self::Error> {
        use PeginWitnessDecoderInner as Inner;
        loop {
            match self.0 {
                Inner::Undetermined => {
                    match bytes.first().copied().map(usize::from) {
                        None => return Ok(encoding::DecoderStatus::NeedsMore),
                        Some(0) => {
                            *bytes = &bytes[1..];
                            self.0 = Inner::Empty;
                        }
                        Some(TOTAL_PEGIN_LENGTH) => {
                            // don't advance `bytes`; the PeginDataDecoder will
                            self.0 = Inner::Pegin(PeginDataDecoder::default());
                        }
                        Some(x) => {
                            return Err(PeginWitnessDecoderError {
                                field: "pegin witness",
                                inner: PeginDataDecoderErrorInner::Length(
                                    ExactLengthDecoderError::IncorrectLength {
                                        expected: TOTAL_PEGIN_LENGTH,
                                        got: x,
                                    },
                                ),
                            });
                        }
                    }
                }
                Inner::Empty => return Ok(encoding::DecoderStatus::Ready),
                Inner::Pegin(ref mut decoder) => return decoder.push_bytes(bytes),
            }
        }
    }

    fn end(self) -> Result<Self::Output, Self::Error> {
        use PeginWitnessDecoderInner as Inner;
        match self.0 {
            Inner::Undetermined => Err(PeginWitnessDecoderError {
                field: "pegin witness",
                inner: PeginDataDecoderErrorInner::InsufficientLength { minimum: 1, got: 0 },
            }),
            Inner::Empty => Ok(PeginWitness { inner: None }),
            Inner::Pegin(decoder) => decoder.end().map(|inner| PeginWitness { inner: Some(inner) }),
        }
    }

    fn read_limit(&self) -> usize {
        use PeginWitnessDecoderInner as Inner;
        match self.0 {
            Inner::Undetermined => 1,
            Inner::Empty => 0,
            Inner::Pegin(ref decoder) => decoder.read_limit(),
        }
    }
}

impl encoding::Decode for PeginWitness {
    type Decoder = PeginWitnessDecoder;
}

/// Parsed data from a transaction input's pegin witness
#[derive(Clone, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub struct PeginData {
    /// The value, in satoshis, of the pegin
    pub value: u64,
    /// Asset type being pegged in
    pub asset_id: AssetId,
    /// Hash of genesis block of originating blockchain
    pub genesis_hash: bitcoin::BlockHash,
    /// The claim script that we should hash to tweak our address.
    pub claim_script: bitcoin::ScriptBuf,
    /// Mainchain transaction; not parsed to save time/memory since the
    /// parsed transaction is typically not useful without auxiliary
    /// data (e.g. knowing how to compute pegin addresses for the
    /// sidechain).
    pub transaction: Vec<u8>,
    /// Merkle proof of transaction inclusion. Also not parsed.
    pub merkle_proof: Vec<u8>,
    /// The Bitcoin block that the pegin output appears in; scraped
    /// from the transaction inclusion proof
    pub referenced_block: bitcoin::BlockHash,
}

impl PeginData {
    /// Reconstructs the Elements previous output claimed by this peg-in
    /// witness.
    ///
    /// This is the Rust equivalent of Elements' `GetPeginOutputFromWitness`:
    /// the asset, value, and claim script become one explicit output. It does
    /// This structural conversion performs no peg-in acceptance validation.
    /// Before treating the output as an accepted transaction input, callers
    /// must complete the full `IsValidPeginWitness`-equivalent validation for
    /// their bound network profile. That includes, but is not limited to,
    /// amount range, pegged-asset identity, claim-script size, parent
    /// transaction, inclusion proof and header rules, federation script,
    /// parent genesis, confirmation depth, and sidechain placement.
    pub fn to_claimed_previous_output(&self) -> TxOut {
        TxOut {
            asset: Asset::Explicit(self.asset_id),
            value: Value::Explicit(self.value),
            nonce: Nonce::Null,
            script_pubkey: Script::from(self.claim_script.as_bytes().to_vec()),
            witness: TxOutWitness::default(),
        }
    }

    /// Parse the mainchain tx provided as pegin data.
    pub fn parse_tx(&self) -> Result<bitcoin::Transaction, bitcoin::consensus::encode::Error> {
        bitcoin::consensus::encode::deserialize(&self.transaction)
    }

    /// Parse the merkle inclusion proof provided as pegin data.
    pub fn parse_merkle_proof(
        &self,
    ) -> Result<bitcoin::MerkleBlock, bitcoin::consensus::encode::Error> {
        bitcoin::consensus::encode::deserialize(&self.merkle_proof)
    }
}

encoding::encoder_newtype_exact! {
    /// An encoder for the [`PeginWitness`] type.
    #[derive(Clone, Debug)]
    pub struct PeginDataEncoder<'e>(
        encoding::Encoder3<
            // top-level compactsize
            encoding::CompactSizeEncoder,
            encoding::Encoder6<
                // value
                encoding::CompactSizeEncoder,
                encoding::ArrayEncoder<8>,
                // asset ID
                encoding::CompactSizeEncoder,
                encoding::ArrayRefEncoder<'e, 32>,
                // genesis hash
                encoding::CompactSizeEncoder,
                GenesisHashEncoder<'e>,
            >,
            encoding::Encoder3<
                // claim script
                bitcoin::blockdata::script::ScriptEncoder<'e>,
                // transaction
                encoding::PrefixedBytesEncoder<'e>,
                // merkle proof
                encoding::PrefixedBytesEncoder<'e>,

            >,
        >
    );
}

impl encoding::Encode for PeginData {
    type Encoder<'e> = PeginDataEncoder<'e>;

    fn encoder(&self) -> Self::Encoder<'_> {
        PeginDataEncoder::new(encoding::Encoder3::new(
            encoding::CompactSizeEncoder::new(TOTAL_PEGIN_LENGTH),
            encoding::Encoder6::new(
                encoding::CompactSizeEncoder::new(8),
                encoding::ArrayEncoder::without_length_prefix(self.value.to_le_bytes()),
                encoding::CompactSizeEncoder::new(32),
                encoding::ArrayRefEncoder::without_length_prefix(self.asset_id.as_byte_array()),
                encoding::CompactSizeEncoder::new(32),
                self.genesis_hash.encoder(),
            ),
            encoding::Encoder3::new(
                self.claim_script.encoder(),
                encoding::PrefixedBytesEncoder::new(&self.transaction),
                encoding::PrefixedBytesEncoder::new(&self.merkle_proof),
            ),
        ))
    }
}

struct ExactLengthDecoder {
    target: usize,
    inner: encoding::CompactSizeDecoder,
}

impl ExactLengthDecoder {
    fn new(target: usize) -> Self { Self { target, inner: encoding::CompactSizeDecoder::new() } }
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum ExactLengthDecoderError {
    IncorrectLength { expected: usize, got: usize },
    InvalidCompactSize(encoding::CompactSizeDecoderError),
}

impl fmt::Display for ExactLengthDecoderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self {
            Self::IncorrectLength { expected, got } => {
                write!(f, "expected length {expected} but got {got}")
            }
            Self::InvalidCompactSize(_) => f.write_str("failed to decode compact size"),
        }
    }
}

impl std::error::Error for ExactLengthDecoderError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match *self {
            Self::IncorrectLength { .. } => None,
            Self::InvalidCompactSize(ref error) => Some(error),
        }
    }
}

impl encoding::Decoder for ExactLengthDecoder {
    type Output = usize;
    type Error = ExactLengthDecoderError;

    fn push_bytes(&mut self, bytes: &mut &[u8]) -> Result<encoding::DecoderStatus, Self::Error> {
        self.inner.push_bytes(bytes).map_err(ExactLengthDecoderError::InvalidCompactSize)
    }

    fn end(self) -> Result<Self::Output, Self::Error> {
        let expected = self.target;
        let got = self.inner.end().map_err(ExactLengthDecoderError::InvalidCompactSize)?;

        if got == self.target {
            Ok(got)
        } else {
            Err(ExactLengthDecoderError::IncorrectLength { expected, got })
        }
    }

    fn read_limit(&self) -> usize { self.inner.read_limit() }
}

/// A decoder for the [`PeginData`] type.
#[allow(clippy::type_complexity)]
pub struct PeginDataDecoder {
    inner: encoding::Decoder3<
        // top-level compactsize
        ExactLengthDecoder,
        encoding::Decoder6<
            // value
            ExactLengthDecoder,
            encoding::ArrayDecoder<8>,
            // asset ID
            ExactLengthDecoder,
            crate::AssetIdDecoder,
            // genesis hash
            ExactLengthDecoder,
            GenesisHashDecoder,
        >,
        encoding::Decoder3<
            // claim script
            bitcoin::blockdata::script::ScriptBufDecoder,
            // transaction
            encoding::ByteVecDecoder,
            // merkle proof
            encoding::ByteVecDecoder,
        >,
    >,
}

impl Default for PeginDataDecoder {
    fn default() -> Self {
        Self {
            inner: encoding::Decoder3::new(
                ExactLengthDecoder::new(TOTAL_PEGIN_LENGTH),
                encoding::Decoder6::new(
                    ExactLengthDecoder::new(8),
                    encoding::ArrayDecoder::new(),
                    ExactLengthDecoder::new(32),
                    crate::AssetIdDecoder::default(),
                    ExactLengthDecoder::new(32),
                    GenesisHashDecoder::new(),
                ),
                encoding::Decoder3::new(
                    bitcoin::blockdata::script::ScriptBufDecoder::new(),
                    encoding::ByteVecDecoder::new(),
                    encoding::ByteVecDecoder::new(),
                ),
            ),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum PeginDataDecoderErrorInner {
    AssetId(crate::AssetIdDecoderError),
    ClaimScript(bitcoin::blockdata::script::ScriptBufDecoderError),
    GenesisHash(GenesisHashDecoderError),
    Length(ExactLengthDecoderError),
    InsufficientLength { minimum: usize, got: usize },
    Eof(encoding::UnexpectedEofError),
    ByteVec(encoding::ByteVecDecoderError),
}

/// Error type for the decoding of [`PeginData`] or [`PeginWitness`].
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct PeginWitnessDecoderError {
    field: &'static str,
    inner: PeginDataDecoderErrorInner,
}

impl fmt::Display for PeginWitnessDecoderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.field == "pegin witness" {
            f.write_str("error decoding pegin witness")?;
        } else {
            write!(f, "error decoding pegin witness field {}", self.field)?;
        }
        if let PeginDataDecoderErrorInner::InsufficientLength { minimum, got } = self.inner {
            write!(f, ": needed at least {minimum} bytes, got {got}")?;
        }
        Ok(())
    }
}

impl std::error::Error for PeginWitnessDecoderError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use PeginDataDecoderErrorInner as Inner;
        match self.inner {
            Inner::AssetId(ref e) => Some(e),
            Inner::ClaimScript(ref e) => Some(e),
            Inner::GenesisHash(ref e) => Some(e),
            Inner::Length(ref e) => Some(e),
            Inner::InsufficientLength { .. } => None,
            Inner::Eof(ref e) => Some(e),
            Inner::ByteVec(ref e) => Some(e),
        }
    }
}

impl PeginWitnessDecoderError {
    /// Private error conversion function.
    #[allow(clippy::type_complexity)]
    fn from(
        inner: encoding::Decoder3Error<
            ExactLengthDecoderError,
            encoding::Decoder6Error<
                ExactLengthDecoderError,
                UnexpectedEofError,
                ExactLengthDecoderError,
                crate::AssetIdDecoderError,
                ExactLengthDecoderError,
                GenesisHashDecoderError,
            >,
            encoding::Decoder3Error<
                bitcoin::blockdata::script::ScriptBufDecoderError,
                encoding::ByteVecDecoderError,
                encoding::ByteVecDecoderError,
            >,
        >,
    ) -> Self {
        use encoding::{Decoder3Error as Dec3Err, Decoder6Error as Dec6Err};

        match inner {
            Dec3Err::First(error) =>
                Self { field: "pegin witness", inner: PeginDataDecoderErrorInner::Length(error) },
            Dec3Err::Second(Dec6Err::First(error)) =>
                Self { field: "value", inner: PeginDataDecoderErrorInner::Length(error) },
            Dec3Err::Second(Dec6Err::Second(error)) =>
                Self { field: "value", inner: PeginDataDecoderErrorInner::Eof(error) },
            Dec3Err::Second(Dec6Err::Third(error)) =>
                Self { field: "asset ID", inner: PeginDataDecoderErrorInner::Length(error) },
            Dec3Err::Second(Dec6Err::Fourth(error)) =>
                Self { field: "asset ID", inner: PeginDataDecoderErrorInner::AssetId(error) },
            Dec3Err::Second(Dec6Err::Fifth(error)) =>
                Self { field: "genesis hash", inner: PeginDataDecoderErrorInner::Length(error) },
            Dec3Err::Second(Dec6Err::Sixth(error)) => Self {
                field: "genesis hash",
                inner: PeginDataDecoderErrorInner::GenesisHash(error),
            },
            Dec3Err::Third(Dec3Err::First(error)) => Self {
                field: "claim script",
                inner: PeginDataDecoderErrorInner::ClaimScript(error),
            },
            Dec3Err::Third(Dec3Err::Second(error)) =>
                Self { field: "transaction", inner: PeginDataDecoderErrorInner::ByteVec(error) },
            Dec3Err::Third(Dec3Err::Third(error)) =>
                Self { field: "merkle proof", inner: PeginDataDecoderErrorInner::ByteVec(error) },
        }
    }
}

impl encoding::Decoder for PeginDataDecoder {
    type Output = PeginData;
    type Error = PeginWitnessDecoderError;

    fn push_bytes(&mut self, bytes: &mut &[u8]) -> Result<encoding::DecoderStatus, Self::Error> {
        self.inner.push_bytes(bytes).map_err(PeginWitnessDecoderError::from)
    }

    fn end(self) -> Result<Self::Output, Self::Error> {
        use internals::slice::SliceExt;

        let (
            _,
            (_, value, _, asset_id, _, genesis_hash),
            (claim_script, transaction, merkle_proof),
        ) = self.inner.end().map_err(PeginWitnessDecoderError::from)?;

        let Some((block_header, _)) = SliceExt::split_first_chunk::<80>(merkle_proof.as_slice())
        else {
            return Err(PeginWitnessDecoderError {
                field: "merkle proof",
                inner: PeginDataDecoderErrorInner::InsufficientLength {
                    minimum: 80,
                    got: merkle_proof.len(),
                },
            });
        };
        let referenced_block = bitcoin::BlockHash::hash(block_header);

        Ok(PeginData {
            value: u64::from_le_bytes(value),
            asset_id,
            genesis_hash,
            claim_script,
            transaction,
            merkle_proof,
            referenced_block,
        })
    }

    fn read_limit(&self) -> usize { self.inner.read_limit() }
}

impl encoding::Decode for PeginData {
    type Decoder = PeginDataDecoder;
}

impl encode::Encodable for PeginData {
    fn consensus_encode<W: io::Write>(&self, e: W) -> Result<usize, encode::Error> {
        let mut counter = encode::ByteCounter::new(e);
        crate::encoding::encode_to_writer(self, &mut counter)?;
        Ok(counter.into_count())
    }
}

impl encode::Decodable for PeginWitness {
    fn consensus_decode<D: io::Read>(d: D) -> Result<Self, encode::Error> {
        match encoding::decode_from_read_unbuffered(d) {
            Ok(res) => Ok(res),
            Err(encoding::ReadError::Io(e)) => Err(encode::Error::Io(e)),
            Err(encoding::ReadError::Decode(e)) => Err(encode::Error::PeginWitness(e)),
        }
    }
}

impl encode::Encodable for PeginWitness {
    fn consensus_encode<W: io::Write>(&self, e: W) -> Result<usize, encode::Error> {
        match self.inner {
            Some(ref wit) => wit.consensus_encode(e),
            None => 0u8.consensus_encode(e),
        }
    }
}

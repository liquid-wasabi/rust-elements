// SPDX-License-Identifier: MIT OR Apache-2.0

//! Surjection Proofs

use core::fmt;
use std::io;

use secp256k1_zkp::rand::{CryptoRng, RngCore};
use secp256k1_zkp::{self, Generator, Secp256k1, Signing, Tweak, ZERO_TWEAK};
#[cfg(feature = "serde")]
use serde::{Deserializer, Serializer};

use crate::confidential::{AssetBlindingFactor, AssetId};
use crate::{encode, encoding};

/// A surjection proof, proving that an asset commitment commits to the same asset ID
/// as a commitment from a given set.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct SurjectionProof {
    inner: Option<Box<secp256k1_zkp::SurjectionProof>>,
}

impl SurjectionProof {
    /// No surjection proof.
    pub const EMPTY: Self = Self { inner: None };

    /// Constructs a new [`SurjectionProof`].
    pub fn new<R, C, S>(
        secp: &Secp256k1<C>,
        rng: &mut R,
        asset: AssetId,
        asset_bf: AssetBlindingFactor,
        inputs: S,
    ) -> Result<Self, secp256k1_zkp::Error>
    where
        R: RngCore + CryptoRng,
        C: Signing,
        S: AsRef<[(Generator, secp256k1_zkp::Tag, Tweak)]>,
    {
        secp256k1_zkp::SurjectionProof::new(
            secp,
            rng,
            asset.into_tag(),
            asset_bf.into_inner(),
            inputs.as_ref(),
        )
        .map(|inner| Self { inner: Some(Box::new(inner)) })
    }

    /// Constructs a new [`SurjectionProof`] selecting exactly `inputs_to_use`
    /// entries from `inputs` for the proof's ring.
    ///
    /// Passing the number of inputs selects every entry in the supplied domain.
    /// The underlying library rejects zero, a count greater than the domain, and
    /// domains or selected rings above its supported maximum.
    pub fn new_with_input_count<R, C, S>(
        secp: &Secp256k1<C>,
        rng: &mut R,
        asset: AssetId,
        asset_bf: AssetBlindingFactor,
        inputs: S,
        inputs_to_use: usize,
    ) -> Result<Self, secp256k1_zkp::Error>
    where
        R: RngCore + CryptoRng,
        C: Signing,
        S: AsRef<[(Generator, secp256k1_zkp::Tag, Tweak)]>,
    {
        secp256k1_zkp::SurjectionProof::new_with_input_count(
            secp,
            rng,
            asset.into_tag(),
            asset_bf.into_inner(),
            inputs.as_ref(),
            inputs_to_use,
        )
        .map(|inner| Self { inner: Some(Box::new(inner)) })
    }

    /// Parses a [`SurjectionProof`] from a byte slice (with no length prefix).
    pub fn from_slice(sl: &[u8]) -> Result<Self, secp256k1_zkp::Error> {
        if sl.is_empty() {
            Ok(Self { inner: None })
        } else {
            secp256k1_zkp::SurjectionProof::from_slice(sl)
                .map(|inner| Self { inner: Some(Box::new(inner)) })
        }
    }

    /// Serializes the surjection proof as a byte vector.
    pub fn to_vec(&self) -> Vec<u8> {
        match self.inner.as_deref() {
            Some(prf) => secp256k1_zkp::SurjectionProof::serialize(prf),
            None => Vec::new(),
        }
    }

    /// Returns the number of domain inputs encoded by this proof, or zero when
    /// the proof is absent.
    pub fn input_count(&self) -> usize {
        let bytes = self.to_vec();
        if bytes.len() < 2 {
            0
        } else {
            u16::from_le_bytes([bytes[0], bytes[1]]) as usize
        }
    }

    /// Returns the number of domain inputs selected in this proof's ring, or
    /// zero when the proof is absent.
    pub fn used_input_count(&self) -> usize {
        let bytes = self.to_vec();
        if bytes.len() < 2 {
            return 0;
        }
        let input_count = u16::from_le_bytes([bytes[0], bytes[1]]) as usize;
        let bitmap_len = input_count.div_ceil(8);
        if input_count == 0 || bytes.len() < 2 + bitmap_len {
            0
        } else {
            (0..input_count)
                .filter(|input_index| bytes[2 + input_index / 8] & (1 << (input_index % 8)) != 0)
                .count()
        }
    }

    /// Returns whether this non-empty proof selects every encoded domain input.
    ///
    /// Callers enforcing a final transaction domain must also compare
    /// [`Self::input_count`] with that final domain's expected length.
    pub fn uses_all_inputs(&self) -> bool {
        let bytes = self.to_vec();
        if bytes.len() < 3 {
            return false;
        }
        let input_count = u16::from_le_bytes([bytes[0], bytes[1]]) as usize;
        let bitmap_len = input_count.div_ceil(8);
        if input_count == 0 || bytes.len() < 2 + bitmap_len {
            return false;
        }
        let bitmap = &bytes[2..2 + bitmap_len];
        (0..input_count).all(|input_index| bitmap[input_index / 8] & (1 << (input_index % 8)) != 0)
            && (input_count..bitmap_len * 8)
                .all(|padding_index| bitmap[padding_index / 8] & (1 << (padding_index % 8)) == 0)
    }

    /// Outputs a [`SurjectionProof`] proving that an asset matches an exact asset ID.
    pub fn blind_asset_proof<C: secp256k1_zkp::Signing, R: RngCore + CryptoRng>(
        rng: &mut R,
        secp: &Secp256k1<C>,
        asset: AssetId,
        abf: AssetBlindingFactor,
    ) -> Result<Self, secp256k1_zkp::Error> {
        let gen = Generator::new_unblinded(secp, asset.into_tag());
        Self::new(secp, rng, asset, abf, [(gen, asset.into_tag(), ZERO_TWEAK)])
    }

    /// Verifies a [`SurjectionProof`] proving that an asset matches an exact asset ID.
    pub fn blind_asset_proof_verify(
        &self,
        secp: &Secp256k1<secp256k1_zkp::All>,
        asset: AssetId,
        asset_commit: Generator,
    ) -> bool {
        let gen = Generator::new_unblinded(secp, asset.into_tag());
        match self.inner.as_deref() {
            Some(inner) => inner.verify(secp, asset_commit, &[gen]),
            None => false,
        }
    }

    /// The length of the range proof (zero if it is empty/absent).
    pub fn len(&self) -> usize {
        self.inner.as_deref().map_or(0, secp256k1_zkp::SurjectionProof::len)
    }

    /// Whether the surjectionproof is absent.
    pub fn is_empty(&self) -> bool { self.inner.is_none() }

    /// Obtains a reference to the underlying secp256k1-zkp object.
    pub fn as_ref(&self) -> Option<&secp256k1_zkp::SurjectionProof> { self.inner.as_deref() }
}

impl crate::encode::Encodable for SurjectionProof {
    fn consensus_encode<W: io::Write>(&self, e: W) -> Result<usize, encode::Error> {
        match self.inner.as_ref() {
            Some(prf) => secp256k1_zkp::SurjectionProof::serialize(prf).consensus_encode(e),
            None => <[u8]>::consensus_encode(&[], e),
        }
    }
}

impl crate::encode::Decodable for SurjectionProof {
    fn consensus_decode<D: io::Read>(d: D) -> Result<Self, encode::Error> {
        let v = Vec::<u8>::consensus_decode(d)?;
        if v.is_empty() {
            Ok(Self { inner: None })
        } else {
            secp256k1_zkp::SurjectionProof::from_slice(&v)
                .map(|inner| Self { inner: Some(Box::new(inner)) })
                .map_err(encode::Error::Secp256k1zkp)
        }
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for SurjectionProof {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.inner.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for SurjectionProof {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Option::<secp256k1_zkp::SurjectionProof>::deserialize(deserializer)
            .map(|inner| Self { inner: inner.map(Box::new) })
    }
}

encoding::encoder_newtype_exact! {
    /// Encoder for the [`SurjectionProof`] type.
    #[derive(Clone, Debug)]
    pub struct Encoder<'e>(super::PrefixedByteVecEncoder);
}

impl encoding::Encode for SurjectionProof {
    type Encoder<'e> = Encoder<'e>;

    fn encoder(&self) -> Self::Encoder<'_> {
        Encoder::new(super::PrefixedByteVecEncoder::new(self.to_vec()))
    }
}

decoder_newtype! {
    /// Decoder for the [`SurjectionProof`] type.
    #[derive(Default)]
    pub struct Decoder(encoding::ByteVecDecoder);

    /// Decoder error for the [`SurjectionProof`] type.
    #[derive(Clone, PartialEq, Eq, Debug)]
    pub struct DecoderError(enum DecoderErrorInner {
        Decode(encoding::ByteVecDecoderError),
        SurjectionProof(secp256k1_zkp::Error),
    });

    impl Decode for SurjectionProof {
        fn convert_inner(v) -> Result<_, DecoderErrorInner> {
            Self::Output::from_slice(&v).map_err(DecoderErrorInner::SurjectionProof)
        }
    }
}

impl fmt::Display for DecoderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use DecoderErrorInner as Inner;
        match self.0 {
            Inner::Decode(..) => f.write_str("error decoding byte vector"),
            Inner::SurjectionProof(..) => f.write_str("error decoding surjection proof"),
        }
    }
}

impl std::error::Error for DecoderError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        use DecoderErrorInner as Inner;
        match self.0 {
            Inner::Decode(ref e) => Some(e),
            Inner::SurjectionProof(ref e) => Some(e),
        }
    }
}

//! This module defines our customized field trait.

use ff::Field;
use ff::FromUniformBytes;
use ff::PrimeField;
use halo2curves::serde::SerdeObject;
use rand_core::RngCore;
use serde::Serialize;

use crate::{fp2::GoldilocksExt2, Goldilocks, GoldilocksExt3};

pub trait SmallField: PrimeField + Serialize + SerdeObject {
    /// Base field
    type BaseField: SmallField + FromUniformBytes<64>;
    /// Extension degree of the Field
    const DEGREE: usize;
    /// Identifier string
    const NAME: &'static str;
    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self>;
    /// Convert a field elements to a u64 vector
    fn to_canonical_u64_vec(&self) -> Vec<u64>;
    /// Convert self to limbs of Goldilocks elements
    fn to_limbs(&self) -> Vec<Self::BaseField>;
    /// Convert limbs into self
    fn from_limbs(limbs: &[Self::BaseField]) -> Self;
    /// Sample a random over the base field
    fn sample_base(rng: impl RngCore) -> Self;
}

impl SmallField for Goldilocks {
    type BaseField = Self;

    const DEGREE: usize = 1;
    const NAME: &'static str = "Goldilocks";

    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        bytes
            .chunks(8)
            .map(|chunk| Self::from_raw_bytes_unchecked(chunk))
            .collect::<Vec<_>>()
    }

    fn to_canonical_u64_vec(&self) -> Vec<u64> {
        vec![self.to_canonical_u64()]
    }

    fn to_limbs(&self) -> Vec<Goldilocks> {
        vec![*self]
    }

    fn from_limbs(limbs: &[Goldilocks]) -> Self {
        limbs[0]
    }

    fn sample_base(mut rng: impl RngCore) -> Self {
        Self::random(&mut rng)
    }
}
impl SmallField for GoldilocksExt2 {
    type BaseField = Goldilocks;

    const DEGREE: usize = 2;
    const NAME: &'static str = "GoldilocksExt2";

    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        bytes
            .chunks(16)
            .map(|chunk| Self::from_raw_bytes_unchecked(chunk))
            .collect::<Vec<_>>()
    }

    fn to_canonical_u64_vec(&self) -> Vec<u64> {
        self.0
            .iter()
            .map(|a| a.to_canonical_u64())
            .collect::<Vec<u64>>()
            .try_into()
            .unwrap()
    }

    fn to_limbs(&self) -> Vec<Goldilocks> {
        self.0.to_vec()
    }

    fn from_limbs(limbs: &[Goldilocks]) -> Self {
        Self([limbs[0], limbs[1]])
    }

    fn sample_base(mut rng: impl RngCore) -> Self {
        Self::BaseField::random(&mut rng).into()
    }
}
impl SmallField for GoldilocksExt3 {
    type BaseField = Goldilocks;

    const DEGREE: usize = 3;
    const NAME: &'static str = "GoldilocksExt3";

    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        bytes
            .chunks(24)
            .map(|chunk| Self::from_raw_bytes_unchecked(chunk))
            .collect::<Vec<_>>()
    }

    fn to_canonical_u64_vec(&self) -> Vec<u64> {
        self.0
            .iter()
            .map(|a| a.to_canonical_u64())
            .collect::<Vec<u64>>()
            .try_into()
            .unwrap()
    }

    fn to_limbs(&self) -> Vec<Goldilocks> {
        self.0.to_vec()
    }

    fn from_limbs(limbs: &[Goldilocks]) -> Self {
        Self([limbs[0], limbs[1], limbs[2]])
    }

    fn sample_base(mut rng: impl RngCore) -> Self {
        Self::BaseField::random(&mut rng).into()
    }
}

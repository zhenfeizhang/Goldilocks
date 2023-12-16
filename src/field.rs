//! This module defines our customized field trait.

use ff::PrimeField;
use halo2curves::serde::SerdeObject;
use serde::Serialize;

use crate::{fp2::GoldilocksExt2, Goldilocks, GoldilocksExt3};

pub trait SmallField: PrimeField + Serialize + SerdeObject {
    /// Extension degree of the Field
    const DEGREE: usize;
    /// Identifier string
    const NAME: &'static str;
    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self>;
    /// Convert a field elements to a u64 vector
    fn to_canonical_u64_vec(&self) -> Vec<u64>;
    /// Convert self to limbs of Goldilocks elements
    fn to_limbs(&self) -> Vec<Goldilocks>;
}

impl SmallField for Goldilocks {
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
}
impl SmallField for GoldilocksExt2 {
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
}
impl SmallField for GoldilocksExt3 {
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
}

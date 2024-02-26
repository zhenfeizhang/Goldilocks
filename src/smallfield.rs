//! Small Field definitions.

use std::hash::Hash;

use ff::FromUniformBytes;
use halo2curves::serde::SerdeObject;
use serde::Serialize;

mod fp;

pub trait SmallField: Serialize + SerdeObject + FromUniformBytes<64> + Hash {
    /// MODULUS as u64
    const MODULUS_U64: u64 = 0xFFFFFFFF00000001;

    /// Identifier string
    const NAME: &'static str;

    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self>;

    /// Convert a field elements to a u64.
    fn to_canonical_u64(&self) -> u64;

    /// Convert a field elements to a u64. Do not normalize it.
    fn to_noncanonical_u64(&self) -> u64;
}

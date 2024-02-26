//! Extension Field definitions.

mod fp;
mod fp2;
mod fp3;

use std::hash::Hash;
use std::ops::Mul;
use std::ops::MulAssign;

use ff::Field;
use ff::FromUniformBytes;
use halo2curves::serde::SerdeObject;
use rand_core::RngCore;
use serde::Serialize;

use super::smallfield::SmallField;

pub trait ExtensionField:
    Serialize
    + SerdeObject
    + FromUniformBytes<64>
    + Hash
    + Mul<Self::BaseField>
    + MulAssign<Self::BaseField>
{
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

    /// Convert a field elements to a u64 vector. Do not normalize it.
    fn as_non_canonical_u64_slice(&self) -> &[u64];

    /// Convert self to limbs of Goldilocks elements
    fn to_limbs(&self) -> [Self::BaseField; Self::DEGREE];

    /// Reference to limbs
    fn as_limbs(&self) -> &[Self::BaseField];

    /// Convert limbs into self
    fn from_limbs(limbs: &[Self::BaseField]) -> Self;

    /// Sample a random over the base field
    fn sample_base(rng: impl RngCore) -> Self {
        Self::from_base(&Self::BaseField::random(rng))
    }

    /// Build a self from a base element; pad ext with 0s.
    fn from_base(b: &Self::BaseField) -> Self;
}

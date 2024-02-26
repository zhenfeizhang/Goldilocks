//! Extension Field implementation for Goldilocks

use crate::{Goldilocks, SmallField};

use super::ExtensionField;

impl ExtensionField for Goldilocks {
    /// Base field
    type BaseField = Self;

    /// Extension degree of the Field
    const DEGREE: usize = 1;

    /// Identifier string
    const NAME: &'static str = "GoldilocksExt1";

    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        <Self as SmallField>::bytes_to_field_elements(bytes)
    }

    /// Convert a field elements to a u64 vector
    fn to_canonical_u64_vec(&self) -> Vec<u64> {
        unimplemented!("use SmallField::to_canonical_u64() instead")
    }

    /// Convert a field elements to a u64 vector. Do not normalize it.
    fn as_non_canonical_u64_slice(&self) -> &[u64] {
        unimplemented!("use SmallField::to_canonical_u64() instead")
    }

    /// Convert self to limbs of Goldilocks elements
    fn to_limbs(&self) -> [Self::BaseField; <Self as ExtensionField>::DEGREE] {
        unimplemented!("use Vec<self> instead")
    }

    /// Reference to limbs
    fn as_limbs(&self) -> &[Self::BaseField] {
        unimplemented!("use &[*self] instead")
    }

    /// Convert limbs into self
    fn from_limbs(limbs: &[Self::BaseField]) -> Self {
        limbs[0]
    }

    /// Build a self from a base element; pad ext with 0s.
    fn from_base(b: &Self::BaseField) -> Self {
        *b
    }
}

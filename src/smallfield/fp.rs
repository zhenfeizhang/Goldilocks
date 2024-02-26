use halo2curves::serde::SerdeObject;

use crate::Goldilocks;

use super::SmallField;

impl SmallField for Goldilocks {
    /// Identifier string
    const NAME: &'static str = "Goldilocks";

    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        bytes
            .chunks(8)
            .map(Self::from_raw_bytes_unchecked)
            .collect::<Vec<_>>()
    }

    /// Convert a field elements to a u64.
    fn to_canonical_u64(&self) -> u64 {
        let mut c = self.0;
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        if c >= Self::MODULUS_U64 {
            c -= Self::MODULUS_U64;
        }
        c
    }

    /// Convert a field elements to a u64. Do not normalize it.
    fn to_noncanonical_u64(&self) -> u64 {
        self.0
    }
}

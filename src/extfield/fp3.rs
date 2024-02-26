//! This module implements Goldilocks cubic extension field mod x^3-x-1

use std::{
    mem::transmute,
    ops::{Mul, MulAssign},
};

use ff::Field;
use halo2curves::serde::SerdeObject;

use crate::{Goldilocks, GoldilocksExt3, SmallField};

use super::ExtensionField;

impl Mul<&Goldilocks> for &GoldilocksExt3 {
    type Output = GoldilocksExt3;

    fn mul(self, rhs: &Goldilocks) -> Self::Output {
        let mut res = *self;
        res.mul_assign(rhs);
        res
    }
}

impl Mul<Goldilocks> for GoldilocksExt3 {
    type Output = GoldilocksExt3;

    fn mul(self, rhs: Goldilocks) -> Self::Output {
        &self * &rhs
    }
}

impl MulAssign<&Goldilocks> for GoldilocksExt3 {
    fn mul_assign(&mut self, rhs: &Goldilocks) {
        self.0[0] *= rhs;
        self.0[1] *= rhs;
        self.0[2] *= rhs;
    }
}

impl MulAssign<Goldilocks> for GoldilocksExt3 {
    fn mul_assign(&mut self, rhs: Goldilocks) {
        self.mul_assign(&rhs)
    }
}

impl ExtensionField for GoldilocksExt3 {
    /// Base field
    type BaseField = Goldilocks;

    /// Extension degree of the Field
    const DEGREE: usize = 3;

    /// Identifier string
    const NAME: &'static str = "GoldilocksExt3";

    /// Convert a byte string into a list of field elements
    fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Self> {
        bytes
            .chunks(24)
            .map(Self::from_raw_bytes_unchecked)
            .collect::<Vec<_>>()
    }

    /// Convert a field elements to a u64 vector
    fn to_canonical_u64_vec(&self) -> Vec<u64> {
        self.0
            .iter()
            .map(|a| a.to_canonical_u64())
            .collect::<Vec<u64>>()
    }

    /// Unsafe function.
    /// Convert a field elements to a u64 vector. Do not normalize it.
    fn as_non_canonical_u64_slice(&self) -> &[u64] {
        unsafe { transmute::<&[Goldilocks], &[u64]>(self.0.as_slice()) }
    }

    /// Convert self to limbs of Goldilocks elements
    fn to_limbs(&self) -> [Self::BaseField; <Self as ExtensionField>::DEGREE] {
        self.0
    }

    /// Reference to limbs
    fn as_limbs(&self) -> &[Self::BaseField] {
        self.0.as_slice()
    }

    /// Convert limbs into self
    fn from_limbs(limbs: &[Self::BaseField]) -> Self {
        Self([limbs[0], limbs[1], limbs[2]])
    }

    /// Build a self from a base element; pad ext with 0s.
    fn from_base(b: &Self::BaseField) -> Self {
        Self([*b, Goldilocks::ZERO, Goldilocks::ZERO])
    }
}

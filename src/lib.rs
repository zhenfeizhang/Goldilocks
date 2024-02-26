//! This crate implements Goldilocks field with modulus 2^64 - 2^32 + 1
//! Credit: the majority of the code is borrowed or inspired from Plonky2 with modifications.
#![allow(incomplete_features)]
#![feature(generic_const_exprs)]

#[macro_use]
mod derive;

mod extfield;
mod primefield;
mod smallfield;
mod structs;
mod util;

pub use extfield::ExtensionField;
pub use smallfield::SmallField;
pub use structs::{Goldilocks, GoldilocksExt2, GoldilocksExt3, EPSILON, MODULUS};

#[cfg(test)]
mod tests;

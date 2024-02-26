use serde::Deserialize;
use serde::Serialize;

/// 2^64 - 2^32 + 1
pub const MODULUS: u64 = 0xffffffff00000001;
/// 2^32 - 1
pub const EPSILON: u64 = 0xffffffff;

/// Goldilocks field with modulus 2^64 - 2^32 + 1.
/// A Goldilocks field may store a non-canonical form of the element
/// where the value can be between 0 and 2^64.
/// For unique representation of its form, use `to_canonical_u64`
#[derive(Clone, Copy, Debug, Default, Serialize, Deserialize)]
pub struct Goldilocks(pub u64);

/// Degree 2 Goldilocks extension field mod x^2 - 7
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct GoldilocksExt2(pub [Goldilocks; 2]);

/// Degree 3 Goldilocks extension field mod x^3-x-1
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize, Hash)]
pub struct GoldilocksExt3(pub [Goldilocks; 3]);

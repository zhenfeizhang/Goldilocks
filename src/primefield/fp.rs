//! Implementing Halo2's PrimeField for Goldilocks

use core::iter::{Product, Sum};
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::fmt::{Display, Formatter};
use std::hash::{Hash, Hasher};
use std::io::{Read, Write};

use ff::{Field, FromUniformBytes, PrimeField};
use halo2curves::bn256::LegendreSymbol;
use halo2curves::serde::SerdeObject;
use itertools::Itertools;
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

// use crate::SmallField;
use crate::smallfield::SmallField;
use crate::util::{add_no_canonicalize_trashing_input, branch_hint, split, sqrt_tonelli_shanks};
use crate::util::{assume, try_inverse_u64};
use crate::{Goldilocks, EPSILON, MODULUS};

impl SerdeObject for Goldilocks {
    /// The purpose of unchecked functions is to read the internal memory representation
    /// of a type from bytes as quickly as possible. No sanitization checks are performed
    /// to ensure the bytes represent a valid object. As such this function should only be
    /// used internally as an extension of machine memory. It should not be used to deserialize
    /// externally provided data.
    fn from_raw_bytes_unchecked(bytes: &[u8]) -> Self {
        let mut tmp = u64::from_le_bytes(
            bytes
                .iter()
                .pad_using(8, |_| &0u8)
                .take(8)
                .cloned()
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap(),
        );
        if tmp >= MODULUS {
            tmp -= MODULUS
        }

        Self(tmp)
    }

    fn from_raw_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() > 8 {
            return None;
        }
        let tmp = u64::from_le_bytes(
            bytes
                .iter()
                .pad_using(8, |_| &0u8)
                .take(8)
                .cloned()
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap(),
        );
        if tmp >= MODULUS {
            None
        } else {
            Some(tmp.into())
        }
    }

    fn to_raw_bytes(&self) -> Vec<u8> {
        self.0.to_le_bytes().to_vec()
    }

    /// The purpose of unchecked functions is to read the internal memory representation
    /// of a type from disk as quickly as possible. No sanitization checks are performed
    /// to ensure the bytes represent a valid object. This function should only be used
    /// internally when some machine state cannot be kept in memory (e.g., between runs)
    /// and needs to be reloaded as quickly as possible.
    fn read_raw_unchecked<R: Read>(reader: &mut R) -> Self {
        let mut buf = [0u8; 8];
        reader.read_exact(&mut buf).unwrap();
        Self(u64::from_le_bytes(buf))
    }
    fn read_raw<R: Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut buf = [0u8; 8];
        reader.read_exact(&mut buf)?;
        let tmp = u64::from_le_bytes(buf);
        if tmp >= MODULUS {
            // todo: wrap the error
            panic!("Not a field element")
        } else {
            Ok(tmp.into())
        }
    }

    fn write_raw<W: Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(self.as_ref())
    }
}

impl PartialEq for Goldilocks {
    fn eq(&self, other: &Goldilocks) -> bool {
        self.to_canonical_u64() == other.to_canonical_u64()
    }
}

impl Eq for Goldilocks {}

impl Hash for Goldilocks {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.to_canonical_u64().hash(hasher);
    }
}

impl Display for Goldilocks {
    fn fmt(&self, w: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(w, "{}", self.0)
    }
}

impl FromUniformBytes<64> for Goldilocks {
    fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        <Self as FromUniformBytes<32>>::from_uniform_bytes(bytes[0..32].try_into().unwrap())
    }
}

impl FromUniformBytes<32> for Goldilocks {
    fn from_uniform_bytes(bytes: &[u8; 32]) -> Self {
        // FIXME: this is biased.
        Goldilocks(u64::from_le_bytes(bytes[..8].try_into().unwrap()))
    }
}

impl FromUniformBytes<16> for Goldilocks {
    fn from_uniform_bytes(bytes: &[u8; 16]) -> Self {
        // FIXME: this is also biased.
        Goldilocks(u64::from_le_bytes(bytes[..8].try_into().unwrap()))
    }
}

impl Field for Goldilocks {
    /// The zero element of the field, the additive identity.
    const ZERO: Self = Self(0);

    /// The one element of the field, the multiplicative identity.
    const ONE: Self = Self(1);

    /// Returns an element chosen uniformly at random using a user-provided RNG.
    /// Note: this sampler is not constant time!
    fn random(mut rng: impl RngCore) -> Self {
        let mut res = rng.next_u64();
        while res >= MODULUS {
            res = rng.next_u64();
        }
        Self(res)
    }

    /// Squares this element.
    #[must_use]
    fn square(&self) -> Self {
        *self * *self
    }

    /// Cubes this element.
    #[must_use]
    fn cube(&self) -> Self {
        self.square() * self
    }

    /// Doubles this element.
    #[must_use]
    fn double(&self) -> Self {
        *self + *self
    }

    /// Computes the multiplicative inverse of this element,
    /// failing if the element is zero.
    fn invert(&self) -> CtOption<Self> {
        match try_inverse_u64(&self.0) {
            Some(p) => CtOption::new(Self(p), Choice::from(1)),
            None => CtOption::new(Self(0), Choice::from(0)),
        }
    }

    /// Returns the square root of the field element, if it is
    /// quadratic residue.
    fn sqrt(&self) -> CtOption<Self> {
        // TODO: better algorithm taking advantage of (t-1)/2 has a nice structure
        sqrt_tonelli_shanks(self, 0x7fffffff)
    }

    /// Computes:
    ///
    /// - $(\textsf{true}, \sqrt{\textsf{num}/\textsf{div}})$, if $\textsf{num}$ and
    ///   $\textsf{div}$ are nonzero and $\textsf{num}/\textsf{div}$ is a square in the
    ///   field;
    /// - $(\textsf{true}, 0)$, if $\textsf{num}$ is zero;
    /// - $(\textsf{false}, 0)$, if $\textsf{num}$ is nonzero and $\textsf{div}$ is zero;
    /// - $(\textsf{false}, \sqrt{G_S \cdot \textsf{num}/\textsf{div}})$, if
    ///   $\textsf{num}$ and $\textsf{div}$ are nonzero and $\textsf{num}/\textsf{div}$ is
    ///   a nonsquare in the field;
    ///
    /// where $G_S$ is a non-square.
    ///
    /// # Warnings
    ///
    /// - The choice of root from `sqrt` is unspecified.
    /// - The value of $G_S$ is unspecified, and cannot be assumed to have any specific
    ///   value in a generic context.
    fn sqrt_ratio(_: &Self, _: &Self) -> (Choice, Self) {
        unimplemented!()
    }
}

impl AsRef<u64> for Goldilocks {
    fn as_ref(&self) -> &u64 {
        &self.0
    }
}

impl AsMut<[u8]> for Goldilocks {
    fn as_mut(&mut self) -> &mut [u8] {
        let ptr = self as *mut Self as *mut u8;
        // SAFETY Self is repr(transparent) and u64 is 8 bytes wide,
        // with alignment greater than that of u8
        unsafe { std::slice::from_raw_parts_mut(ptr, 8) }
    }
}

impl AsRef<[u8]> for Goldilocks {
    fn as_ref(&self) -> &[u8] {
        let ptr = self as *const Self as *const u8;
        // SAFETY Self is repr(transparent) and u64 is 8 bytes wide,
        // with alignment greater than that of u8
        unsafe { std::slice::from_raw_parts(ptr, 8) }
    }
}

/// This represents an element of a prime field.
impl PrimeField for Goldilocks {
    /// The prime field can be converted back and forth into this binary
    /// representation.
    type Repr = Self;

    /// Modulus of the field written as a string for debugging purposes.
    ///
    /// The encoding of the modulus is implementation-specific. Generic users of the
    /// `PrimeField` trait should treat this string as opaque.
    const MODULUS: &'static str = "0xffffffff00000001";

    /// How many bits are needed to represent an element of this field.
    const NUM_BITS: u32 = 64;

    /// How many bits of information can be reliably stored in the field element.
    ///
    /// This is usually `Self::NUM_BITS - 1`.
    const CAPACITY: u32 = 63;

    /// An integer `s` satisfying the equation `2^s * t = modulus - 1` with `t` odd.
    ///
    /// This is the number of leading zero bits in the little-endian bit representation of
    /// `modulus - 1`.
    const S: u32 = 32;

    /// Inverse of $2$ in the field.
    const TWO_INV: Self = Self(0x7fffffff80000001);

    /// A fixed multiplicative generator of `modulus - 1` order. This element must also be
    /// a quadratic nonresidue.
    ///
    /// It can be calculated using [SageMath] as `GF(modulus).primitive_element()`.
    ///
    /// Implementations of this trait MUST ensure that this is the generator used to
    /// derive `Self::ROOT_OF_UNITY`.
    ///
    /// [SageMath]: https://www.sagemath.org/
    const MULTIPLICATIVE_GENERATOR: Self = Self(7);

    /// The `2^s` root of unity.
    ///
    /// It can be calculated by exponentiating `Self::MULTIPLICATIVE_GENERATOR` by `t`,
    /// where `t = (modulus - 1) >> Self::S`.
    const ROOT_OF_UNITY: Self = Self(0x185629dcda58878c);

    /// Inverse of [`Self::ROOT_OF_UNITY`].
    const ROOT_OF_UNITY_INV: Self = Self(0x76b6b635b6fc8719);

    /// Generator of the `t-order` multiplicative subgroup.
    ///
    /// It can be calculated by exponentiating [`Self::MULTIPLICATIVE_GENERATOR`] by `2^s`,
    /// where `s` is [`Self::S`].
    const DELTA: Self = Self(0xaa5b2509f86bb4d4);

    /// Attempts to convert a byte representation of a field element into an element of
    /// this prime field, failing if the input is not canonical (is not smaller than the
    /// field's modulus).
    ///
    /// The byte representation is interpreted with the same endianness as elements
    /// returned by [`PrimeField::to_repr`].
    fn from_repr(repr: Self::Repr) -> CtOption<Self> {
        CtOption::new(repr, Choice::from(1))
    }

    /// Attempts to convert a byte representation of a field element into an element of
    /// this prime field, failing if the input is not canonical (is not smaller than the
    /// field's modulus).
    ///
    /// The byte representation is interpreted with the same endianness as elements
    /// returned by [`PrimeField::to_repr`].
    ///
    /// # Security
    ///
    /// This method provides **no** constant-time guarantees. Implementors of the
    /// `PrimeField` trait **may** optimise this method using non-constant-time logic.
    fn from_repr_vartime(repr: Self::Repr) -> Option<Self> {
        Self::from_repr(repr).into()
    }

    /// Converts an element of the prime field into the standard byte representation for
    /// this field.
    ///
    /// The endianness of the byte representation is implementation-specific. Generic
    /// encodings of field elements should be treated as opaque.
    fn to_repr(&self) -> Self::Repr {
        *self
    }

    /// Returns true iff this element is odd.
    fn is_odd(&self) -> Choice {
        Choice::from((self.0 & 1) as u8)
    }
}

impl From<u64> for Goldilocks {
    fn from(input: u64) -> Self {
        Self(if input >= MODULUS {
            input - MODULUS
        } else {
            input
        })
    }
}

impl From<Goldilocks> for u64 {
    fn from(input: Goldilocks) -> Self {
        input.0
    }
}

impl ConditionallySelectable for Goldilocks {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self(u64::conditional_select(&a.0, &b.0, choice))
    }
}

impl ConstantTimeEq for Goldilocks {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.to_canonical_u64().ct_eq(&other.to_canonical_u64())
    }
}

impl Neg for Goldilocks {
    type Output = Self;

    #[inline]
    fn neg(self) -> Self {
        if self.0 == 0 {
            self
        } else {
            Self(MODULUS - self.to_canonical_u64())
        }
    }
}

impl Add for Goldilocks {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn add(self, rhs: Self) -> Self::Output {
        let (sum, over) = self.0.overflowing_add(rhs.0);
        let (mut sum, over) = sum.overflowing_add((over as u64) * EPSILON);
        if over {
            // NB: self.0 > Self::ORDER && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-overflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 or rhs.0 <= ORDER, then it can skip this
            //     check.
            //  2. Hints to the compiler how rare this double-overflow is (thus handled better with
            //     a branch).
            assume(self.0 > MODULUS && rhs.0 > MODULUS);
            branch_hint();
            sum += EPSILON; // Cannot overflow.
        }
        Self(sum)
    }
}

impl<'a> Add<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &'a Goldilocks) -> Self::Output {
        self + *rhs
    }
}

impl AddAssign for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<'a> AddAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn add_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self + *rhs;
    }
}

impl Sub for Goldilocks {
    type Output = Self;

    #[inline]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn sub(self, rhs: Self) -> Self {
        let (diff, under) = self.0.overflowing_sub(rhs.0);
        let (mut diff, under) = diff.overflowing_sub((under as u64) * EPSILON);
        if under {
            // NB: self.0 < EPSILON - 1 && rhs.0 > Self::ORDER is necessary but not sufficient for
            // double-underflow.
            // This assume does two things:
            //  1. If compiler knows that either self.0 >= EPSILON - 1 or rhs.0 <= ORDER, then it
            //     can skip this check.
            //  2. Hints to the compiler how rare this double-underflow is (thus handled better
            //     with a branch).
            assume(self.0 < EPSILON - 1 && rhs.0 > MODULUS);
            branch_hint();
            diff -= EPSILON; // Cannot underflow.
        }
        Self(diff)
    }
}

impl<'a> Sub<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &'a Goldilocks) -> Self::Output {
        self - *rhs
    }
}

impl SubAssign for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<'a> SubAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn sub_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self - *rhs;
    }
}

impl<T: ::core::borrow::Borrow<Goldilocks>> Sum<T> for Goldilocks {
    fn sum<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, item| acc + item.borrow())
    }
}

impl Mul for Goldilocks {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: Self) -> Self {
        reduce128((self.0 as u128) * (rhs.0 as u128))
    }
}

impl<'a> Mul<&'a Goldilocks> for Goldilocks {
    type Output = Self;

    #[inline]
    fn mul(self, rhs: &'a Goldilocks) -> Self::Output {
        self * *rhs
    }
}

impl MulAssign for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<'a> MulAssign<&'a Goldilocks> for Goldilocks {
    #[inline]
    fn mul_assign(&mut self, rhs: &'a Goldilocks) {
        *self = *self * *rhs;
    }
}

impl<T: ::core::borrow::Borrow<Goldilocks>> Product<T> for Goldilocks {
    fn product<I: Iterator<Item = T>>(iter: I) -> Self {
        iter.fold(Self::ONE, |acc, item| acc * item.borrow())
    }
}

/// Reduces to a 64-bit value. The result might not be in canonical form; it could be in between the
/// field order and `2^64`.
#[inline]
fn reduce128(x: u128) -> Goldilocks {
    let (x_lo, x_hi) = split(x); // This is a no-op
    let x_hi_hi = x_hi >> 32;
    let x_hi_lo = x_hi & EPSILON;

    let (mut t0, borrow) = x_lo.overflowing_sub(x_hi_hi);
    if borrow {
        branch_hint(); // A borrow is exceedingly rare. It is faster to branch.
        t0 -= EPSILON; // Cannot underflow.
    }
    let t1 = x_hi_lo * EPSILON;
    let t2 = unsafe { add_no_canonicalize_trashing_input(t0, t1) };
    Goldilocks(t2)
}

impl Goldilocks {
    #[inline]
    pub fn to_noncanonical_u64(&self) -> u64 {
        self.0
    }

    pub const fn size() -> usize {
        8
    }

    pub fn legendre(&self) -> LegendreSymbol {
        // s = self^((modulus - 1) // 2)
        // 9223372034707292160
        let s = 0x7fffffff80000000;
        let s = self.pow_vartime([s]);
        if s == Self::ZERO {
            LegendreSymbol::Zero
        } else if s == Self::ONE {
            LegendreSymbol::QuadraticResidue
        } else {
            LegendreSymbol::QuadraticNonResidue
        }
    }
}
const MULTIPLE_OF_EPSILON: [u64; 8] = [
    0,
    0xffffffff,
    0x1fffffffe,
    0x2fffffffd,
    0x3fffffffc,
    0x4fffffffb,
    0x5fffffffa,
    0x6fffffff9,
];

impl Goldilocks {
    #[inline]
    pub fn sum_5(
        a: &Goldilocks,
        b: &Goldilocks,
        c: &Goldilocks,
        d: &Goldilocks,
        e: &Goldilocks,
    ) -> Self {
        let (sum, over_b) = a.0.overflowing_add(b.0);
        let (sum, over_c) = sum.overflowing_add(c.0);
        let (sum, over_d) = sum.overflowing_add(d.0);
        let (sum, over_e) = sum.overflowing_add(e.0);
        let over = over_b as u8 + over_c as u8 + over_d as u8 + over_e as u8;

        let (mut sum, over) = sum.overflowing_add(MULTIPLE_OF_EPSILON[over as usize]);
        if over {
            sum += EPSILON; // Cannot overflow.
        }
        Self(sum)
    }
}

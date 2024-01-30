use crate::arithmetic::sbb;
use crate::ff::{Field, PrimeField, WithSmallOrderMulGroup};
use crate::utils::{assume, branch_hint};
use crate::{
    impl_add_binop_specify_output, impl_binops_additive, impl_binops_additive_specify_output,
    impl_binops_multiplicative, impl_binops_multiplicative_mixed, impl_sub_binop_specify_output,
    impl_sum_prod,
};
use core::fmt;
use core::ops::{Add, Mul, Neg, Sub};
use ff::{FieldBits, PrimeFieldBits};
use rand::RngCore;
use std::hash::Hash;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};

/// Goldilocks field
///
/// This represents an element of $\mathbb{F}_r$ where `r = 2^64 - 2^32 + 1`
///
/// Most implementation are port from
/// [plonky2](https://github.com/0xPolygonZero/plonky2/blob/main/field/src/goldilocks_field.rs)
#[derive(Default, Copy, Clone)]
pub struct Fp(pub(crate) u64);

#[cfg(feature = "derive_serde")]
crate::serialize_deserialize_bytes_primefield!(Fp, 8);

const EPSILON: u64 = (1 << 32) - 1;

const MODULUS: Fp = Fp(0xffff_ffff_0000_0001);

/// The modulus as u32 limbs.
#[cfg(not(target_pointer_width = "64"))]
const MODULUS_LIMBS_32: [u32; 2] = [0x0000_0001, 0xffff_ffff];

const MODULUS_STR: &str = "0xffffffff00000001";

const GENERATOR: Fp = Fp(7);

const S: u32 = 32;

/// hex(Fr(1).nth_root(2**32))
const ROOT_OF_UNITY: Fp = Fp(0x1856_29dc_da58_878c);

const TWO_INV: Fp = Fp(0x7fff_ffff_8000_0001);

const ROOT_OF_UNITY_INV: Fp = Fp(0x76b6_b635_b6fc_8719);

const DELTA: Fp = Fp(0xaa5b_2509_f86b_b4d4);

const ZETA: Fp = Fp(0xffff_fffe_0000_0001);

impl_binops_additive!(Fp, Fp);
impl_binops_multiplicative!(Fp, Fp);
impl_sum_prod!(Fp);

impl fmt::Debug for Fp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Fp").field(&self.to_canonical_u64()).finish()
    }
}

impl fmt::Display for Fp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Fp").field(&self.to_canonical_u64()).finish()
    }
}

impl Eq for Fp {}

impl PartialEq for Fp {
    fn eq(&self, other: &Self) -> bool {
        self.to_canonical_u64_vartime() == other.to_canonical_u64_vartime()
    }
}

impl ConstantTimeEq for Fp {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.to_canonical_u64().ct_eq(&other.to_canonical_u64())
    }
}

impl Hash for Fp {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.to_canonical_u64().hash(state);
    }
}

impl core::cmp::Ord for Fp {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.to_canonical_u64_vartime()
            .cmp(&other.to_canonical_u64_vartime())
    }
}

impl core::cmp::PartialOrd for Fp {
    fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl ConditionallySelectable for Fp {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Fp(u64::conditional_select(&a.0, &b.0, choice))
    }
}

impl<'a, 'b> Sub<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn sub(self, rhs: &'b Fp) -> Fp {
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
            assume(self.0 < EPSILON - 1 && rhs.0 > MODULUS.0);
            branch_hint();
            diff -= EPSILON; // Cannot underflow.
        }
        Fp(diff)
    }
}

impl<'a, 'b> Add<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn add(self, rhs: &'b Fp) -> Fp {
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
            assume(self.0 > MODULUS.0 && rhs.0 > MODULUS.0);
            branch_hint();
            sum += EPSILON; // Cannot overflow.
        }
        Fp(sum)
    }
}

impl<'a, 'b> Mul<&'b Fp> for &'a Fp {
    type Output = Fp;

    #[inline]
    fn mul(self, rhs: &'b Fp) -> Fp {
        reduce128((self.0 as u128) * (rhs.0 as u128))
    }
}

impl<'a> Neg for &'a Fp {
    type Output = Fp;

    #[inline]
    fn neg(self) -> Fp {
        Fp::conditional_select(
            &Fp(MODULUS.0 - self.to_canonical_u64()),
            &Fp::ZERO,
            self.is_zero(),
        )
    }
}

impl Neg for Fp {
    type Output = Fp;

    #[inline]
    fn neg(self) -> Fp {
        -&self
    }
}

impl From<bool> for Fp {
    fn from(bit: bool) -> Fp {
        Fp(bit as u64)
    }
}

impl From<u64> for Fp {
    fn from(digit: u64) -> Self {
        Self(digit)
    }
}

impl From<Fp> for [u8; 8] {
    fn from(value: Fp) -> [u8; 8] {
        value.to_repr()
    }
}

impl<'a> From<&'a Fp> for [u8; 8] {
    fn from(value: &'a Fp) -> [u8; 8] {
        value.to_repr()
    }
}

impl Fp {
    /// Returns zero, the additive identity.
    #[inline]
    pub const fn zero() -> Fp {
        Fp(0)
    }

    /// Returns one, the multiplicative identity.
    #[inline]
    pub const fn one() -> Fp {
        Fp(1)
    }

    #[inline]
    pub fn to_canonical(self) -> Fp {
        Fp::from(self.to_canonical_u64())
    }

    #[inline]
    pub fn to_canonical_vartime(self) -> Fp {
        Fp::from(self.to_canonical_u64_vartime())
    }

    #[inline]
    pub fn to_canonical_u64(self) -> u64 {
        // We only need one condition subtraction, since 2 * ORDER would not fit in a u64.
        let (sub, _) = self.0.overflowing_sub(MODULUS.0);
        let choice = Choice::from((self.0 >= MODULUS.0) as u8);
        u64::conditional_select(&self.0, &sub, choice)
    }

    #[inline]
    pub fn to_canonical_u64_vartime(self) -> u64 {
        let mut c = self.0;
        if c >= MODULUS.0 {
            c -= MODULUS.0;
        }
        c
    }
}

impl Field for Fp {
    const ZERO: Self = Self::zero();
    const ONE: Self = Self::one();

    fn random(mut rng: impl RngCore) -> Self {
        Self(rng.next_u64())
    }

    #[inline(always)]
    fn double(&self) -> Self {
        self + self
    }

    #[inline(always)]
    fn square(&self) -> Self {
        self * self
    }

    fn invert(&self) -> CtOption<Self> {
        // compute base^(P - 2) using 72 multiplications
        // The exponent P - 2 is represented in binary as:
        // 0b1111111111111111111111111111111011111111111111111111111111111111

        // compute base^11
        let t2 = self.square() * self;

        // compute base^111
        let t3 = t2.square() * self;

        // compute base^111111 (6 ones)
        // repeatedly square t3 3 times and multiply by t3
        let t6 = exp_acc::<3>(t3, t3);

        // compute base^111111111111 (12 ones)
        // repeatedly square t6 6 times and multiply by t6
        let t12 = exp_acc::<6>(t6, t6);

        // compute base^111111111111111111111111 (24 ones)
        // repeatedly square t12 12 times and multiply by t12
        let t24 = exp_acc::<12>(t12, t12);

        // compute base^1111111111111111111111111111111 (31 ones)
        // repeatedly square t24 6 times and multiply by t6 first. then square t30 and
        // multiply by base
        let t30 = exp_acc::<6>(t24, t6);
        let t31 = t30.square() * self;

        // compute base^111111111111111111111111111111101111111111111111111111111111111
        // repeatedly square t31 32 times and multiply by t31
        let t63 = exp_acc::<32>(t31, t31);

        // compute base^1111111111111111111111111111111011111111111111111111111111111111
        let res = t63.square() * self;

        CtOption::new(res, !self.is_zero())
    }

    fn sqrt(&self) -> CtOption<Self> {
        const T_MINUS1_OVER2: [u64; 1] = [0x7fffffffffffffff];
        ff::helpers::sqrt_tonelli_shanks(self, T_MINUS1_OVER2)
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        ff::helpers::sqrt_ratio_generic(num, div)
    }
}

impl PrimeField for Fp {
    type Repr = [u8; 8];

    const NUM_BITS: u32 = 64;
    const CAPACITY: u32 = 63;
    const MODULUS: &'static str = MODULUS_STR;
    const MULTIPLICATIVE_GENERATOR: Self = GENERATOR;
    const ROOT_OF_UNITY: Self = ROOT_OF_UNITY;
    const ROOT_OF_UNITY_INV: Self = ROOT_OF_UNITY_INV;
    const TWO_INV: Self = TWO_INV;
    const DELTA: Self = DELTA;
    const S: u32 = S;

    fn from_repr(r: Self::Repr) -> CtOption<Self> {
        let r = u64::from_le_bytes(r);
        let (_, borrow) = sbb(r, MODULUS.0, 0);
        let is_some = (borrow as u8) & 1;

        CtOption::new(Self(r), Choice::from(is_some))
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_canonical_u64().to_le_bytes()
    }

    fn is_odd(&self) -> Choice {
        Choice::from(self.to_repr()[0] & 1)
    }
}

#[cfg(feature = "bits")]
#[cfg_attr(docsrs, doc(cfg(feature = "bits")))]
#[cfg(target_pointer_width = "64")]
impl PrimeFieldBits for Fp {
    type ReprBits = [u64; 1];

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        FieldBits::new([self.to_canonical_u64()])
    }

    fn char_le_bits() -> ::ff::FieldBits<Self::ReprBits> {
        FieldBits::new([MODULUS.0])
    }
}

#[cfg(feature = "bits")]
#[cfg_attr(docsrs, doc(cfg(feature = "bits")))]
#[cfg(not(target_pointer_width = "64"))]
impl PrimeFieldBits for Fp {
    type ReprBits = [u32; 2];

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        let bytes = self.to_repr();

        let limbs = [
            u32::from_le_bytes(bytes[0..4].try_into().unwrap()),
            u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
        ];

        FieldBits::new(limbs)
    }

    fn char_le_bits() -> ::ff::FieldBits<Self::ReprBits> {
        FieldBits::new(MODULUS_LIMBS_32)
    }
}

impl WithSmallOrderMulGroup<3> for Fp {
    const ZETA: Self = ZETA;
}

/// Fast addition modulo ORDER for x86-64.
/// This function is marked unsafe for the following reasons:
///   - It is only correct if x + y < 2**64 + ORDER = 0x1ffffffff00000001.
///   - It is only faster in some circumstances. In particular, on x86 it overwrites both inputs in
///     the registers, so its use is not recommended when either input will be used again.
#[inline(always)]
#[cfg(target_arch = "x86_64")]
unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    let res_wrapped: u64;
    let adjustment: u64;
    core::arch::asm!(
        "add {0}, {1}",
        // Trick. The carry flag is set iff the addition overflowed.
        // sbb x, y does x := x - y - CF. In our case, x and y are both {1:e}, so it simply does
        // {1:e} := 0xffffffff on overflow and {1:e} := 0 otherwise. {1:e} is the low 32 bits of
        // {1}; the high 32-bits are zeroed on write. In the end, we end up with 0xffffffff in {1}
        // on overflow; this happens be EPSILON.
        // Note that the CPU does not realize that the result of sbb x, x does not actually depend
        // on x. We must write the result to a register that we know to be ready. We have a
        // dependency on {1} anyway, so let's use it.
        "sbb {1:e}, {1:e}",
        inlateout(reg) x => res_wrapped,
        inlateout(reg) y => adjustment,
        options(pure, nomem, nostack),
    );
    assume(x != 0 || (res_wrapped == y && adjustment == 0));
    assume(y != 0 || (res_wrapped == x && adjustment == 0));
    // Add EPSILON == subtract ORDER.
    // Cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
    res_wrapped + adjustment
}

#[inline(always)]
#[cfg(not(target_arch = "x86_64"))]
const unsafe fn add_no_canonicalize_trashing_input(x: u64, y: u64) -> u64 {
    let (res_wrapped, carry) = x.overflowing_add(y);
    // Below cannot overflow unless the assumption if x + y < 2**64 + ORDER is incorrect.
    res_wrapped + EPSILON * (carry as u64)
}

/// Reduces to a 64-bit value. The result might not be in canonical form; it could be in between the
/// field order and `2^64`.
#[inline]
fn reduce128(x: u128) -> Fp {
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
    Fp(t2)
}

#[inline]
const fn split(x: u128) -> (u64, u64) {
    (x as u64, (x >> 64) as u64)
}

/// Squares the base N number of times and multiplies the result by the tail value.
#[inline(always)]
fn exp_acc<const N: usize>(base: Fp, tail: Fp) -> Fp {
    let mut res = base;
    for _ in 0..N {
        res = res.square();
    }
    res * tail
}

#[cfg(test)]
mod test {
    use super::*;
    use rand_core::OsRng;

    #[test]
    fn test_sqrt() {
        let v = (Fp::TWO_INV).square().sqrt().unwrap().to_canonical();
        assert!(v == Fp::TWO_INV || (-v) == Fp::TWO_INV);

        for _ in 0..10000 {
            let a = Fp::random(OsRng);
            let mut b = a;
            b = b.square();

            let b = b.sqrt().unwrap();
            let mut negb = b;
            negb = negb.neg();

            assert!(a == b || a == negb);
        }
    }

    #[test]
    fn test_field() {
        crate::tests::field::random_field_tests::<Fp>("goldilocks".to_string());
    }

    #[test]
    fn test_delta() {
        assert_eq!(Fp::DELTA, GENERATOR.pow([1u64 << Fp::S]));
        assert_eq!(Fp::DELTA, Fp::MULTIPLICATIVE_GENERATOR.pow([1u64 << Fp::S]));
    }

    #[test]
    fn test_conversion() {
        crate::tests::field::random_conversion_tests::<Fp, 8>("fr".to_string());
    }

    #[test]
    #[cfg(feature = "bits")]
    fn test_bits() {
        crate::tests::field::random_bits_tests::<Fp>("fr".to_string());
    }
}

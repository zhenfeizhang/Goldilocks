use crate::{ExtensionField, Goldilocks, GoldilocksExt2};

use super::avx2::Avx2GoldilocksField;

pub trait EvalHelper: ExtensionField {
    fn eval_helper(x: &Self, y: &Self, p: &Self) -> Self {
        *p * (*y - *x) + x
    }
}

impl EvalHelper for GoldilocksExt2 {
    fn eval_helper(x: &Self, y: &Self, p: &Self) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
        {
            eval_avx2(x, y, p)
        }

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64")))]
        {
            *p * (*y - *x) + x
        }
    }
}

fn eval_avx2<F: ExtensionField>(x: &F, y: &F, p: &F) -> F {
    // =======================================
    // WARNING: the following code is only tested for Ext2.
    // It has not been tested for Ext3.
    // =======================================

    // We want to compute p * (y - x) + x
    // which is (p0 + p1 X) * ( y0 - x0 + y1 X - x1 X) + (x0 + x1 X)
    // we compute two AVX2 MULs:
    //
    // 1. r1 = p0 * [ y0,  -x0, y1, -x1]
    // 2. r2 = p1 * [7y1, -7x1, y0, -x0]
    // 3. r3 = r1 + r2
    // 4. res = [r3[0] + r3[1] + x0, r3[2] + r3[3] + x1
    //
    // NOTE: further optimization may SIMD this `mul by 7` operation

    let seven = Goldilocks(7);

    let x = x.as_non_canonical_u64_slice();
    let y = y.as_non_canonical_u64_slice();
    let p = p.as_non_canonical_u64_slice();

    let first_part = {
        // r1 = p0 * [ y0,  -x0, y1, -x1]
        let x0_x1_neg_y0_neg_y1 = [
            Goldilocks(y[0]),
            -Goldilocks(x[0]),
            Goldilocks(y[1]),
            -Goldilocks(x[1]),
        ];
        let x0_x1_neg_y0_neg_y1 = Avx2GoldilocksField::from_slice(x0_x1_neg_y0_neg_y1.as_slice());

        let p0 = Goldilocks::from(p[0]);

        *x0_x1_neg_y0_neg_y1 * p0
    };

    let second_part = {
        // 2. r2 = p1 * [7y1, -7x1, y0, -x0]
        let x1_x0_neg_y1_neg_y0 = [
            Goldilocks(y[1]) * seven,
            -Goldilocks(x[1]) * seven,
            Goldilocks(y[0]),
            -Goldilocks(x[0]),
        ];
        let x1_x0_neg_y1_neg_y0 = Avx2GoldilocksField::from_slice(x1_x0_neg_y1_neg_y0.as_slice());

        let p1 = Goldilocks::from(p[1]);

        *x1_x0_neg_y1_neg_y0 * p1
    };

    // 3. r3 = r1 + r2
    let r3 = (first_part + second_part).0;

    // 4. res = [r3[0] + r3[1] + x0, r3[2] + r3[3] + x1
    F::from_limbs(&[
        F::BaseField::from((r3[0] + r3[1] + Goldilocks(x[0])).0),
        F::BaseField::from((r3[2] + r3[3] + Goldilocks(x[1])).0),
    ])
}

#[cfg(test)]
mod test {
    use crate::util::mle_helper::eval_avx2;
    use crate::GoldilocksExt2;
    use ark_std::test_rng;
    use ff::Field;

    #[test]
    fn test_eval() {
        let x = GoldilocksExt2([1.into(), 2.into()]);
        let y = GoldilocksExt2([3.into(), 4.into()]);
        let p = GoldilocksExt2([5.into(), 6.into()]);

        let res = eval_avx2(&x, &y, &p);
        let res2 = p * (y - x) + x;
        assert_eq!(res, res2);

        let mut rng = test_rng();
        for _ in 0..100 {
            let x = GoldilocksExt2::random(&mut rng);
            let y = GoldilocksExt2::random(&mut rng);
            let p = GoldilocksExt2::random(&mut rng);

            let res = eval_avx2(&x, &y, &p);
            let res2 = p * (y - x) + x;
            assert_eq!(res, res2);
        }
    }
}

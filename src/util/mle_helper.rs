use std::slice::from_raw_parts;

use crate::{ExtensionField, Goldilocks, GoldilocksExt2};

use super::avx2::Avx2GoldilocksField;

pub trait EvalHelper: ExtensionField {
    fn eval_helper(x_and_y: &[Self], p: &Self) -> Self {
        *p * (x_and_y[1] - x_and_y[0]) + x_and_y[0]
    }
}

impl EvalHelper for GoldilocksExt2 {
    fn eval_helper(x_and_y: &[Self], p: &Self) -> Self {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_feature = "avx2"))]
        {
            eval_avx2(x_and_y, p)
        }

        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_feature = "avx2")))]
        {
            *p * (x_and_y[1] - x_and_y[0]) + x_and_y[0]
        }
    }
}

fn eval_avx2(x_and_y: &[GoldilocksExt2], p: &GoldilocksExt2) -> GoldilocksExt2 {
    // =======================================
    // WARNING: the following code supports only Ext2.
    // It does not support Ext3.
    // =======================================

    // We want to compute p * (y - x) + x
    // which is (p0 + p1 X) * ( y0 - x0 + y1 X - x1 X) + (x0 + x1 X)
    // we compute two AVX2 MULs:
    //
    // 1. r1 = [ x0, x1,  y0, y1 ] \circ [ -p0,  -p0, p0,  p0]
    // 2. r2 = [ x0, x1,  y0, y1 ] \circ [ -p1, -7p1, p1, 7p1]
    // 3. res[0] = r1[0] + r1[2] + r2[1] + r2[3] + x0
    //    res[1] = r1[1] + r1[3] + r2[0] + r2[2] + x1
    let neg_p0 = -p.0[0];
    let neg_p1 = -p.0[1];
    let seven_p1 = p.0[1] * Goldilocks(7);
    let neg_seven_p1 = -seven_p1;

    let x0_x1_y0_y1 = unsafe { from_raw_parts(x_and_y.as_ptr() as *const Goldilocks, 4) };
    let x0_x1_y0_y1 = Avx2GoldilocksField::from_slice(x0_x1_y0_y1);
    let p0_multiplicand = Avx2GoldilocksField([neg_p0, neg_p0, p.0[0], p.0[0]]);
    let p1_multiplicand = Avx2GoldilocksField([neg_p1, neg_seven_p1, p.0[1], seven_p1]);

    let r1 = *x0_x1_y0_y1 * p0_multiplicand;
    let r2 = *x0_x1_y0_y1 * p1_multiplicand;

    GoldilocksExt2([
        Goldilocks::sum_5(&r1.0[0], &r1.0[2], &r2.0[1], &r2.0[3], &x_and_y[0].0[0]),
        Goldilocks::sum_5(&r1.0[1], &r1.0[3], &r2.0[0], &r2.0[2], &x_and_y[0].0[1]),
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

        let res = eval_avx2(&[x, y], &p);
        let res2 = p * (y - x) + x;
        assert_eq!(res, res2);

        let mut rng = test_rng();
        for _ in 0..100 {
            let x = GoldilocksExt2::random(&mut rng);
            let y = GoldilocksExt2::random(&mut rng);
            let p = GoldilocksExt2::random(&mut rng);

            let res = eval_avx2(&[x, y], &p);
            let res2 = p * (y - x) + x;
            assert_eq!(res, res2);
        }
    }
}

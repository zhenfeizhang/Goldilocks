use std::{ops::Mul, slice::from_raw_parts};

use crate::{ExtensionField, Goldilocks, GoldilocksExt2};

use super::avx2::Avx2GoldilocksField;

pub trait EvalHelper: ExtensionField {
    fn eval_helper(x_and_y: &[Self], p: &Self) -> Self {
        *p * (x_and_y[1] - x_and_y[0]) + x_and_y[0]
    }

    fn eval_helper_4(_x_and_ys: &[Self], _ps: &[Self]) -> [Self; 4] {
        unimplemented!("Only supports Goldilocks degree 2 Extensions")
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

    fn eval_helper_4(x_and_ys: &[Self], ps: &[Self]) -> [Self; 4] {
        assert_eq!(x_and_ys.len(), 8);
        assert_eq!(ps.len(), 4);
        eval_4_avx2(x_and_ys, ps)
    }
}

fn eval_4_avx2(x_and_y: &[GoldilocksExt2], p: &[GoldilocksExt2]) -> [GoldilocksExt2; 4] {
    // y coord of all p-s
    let p_ys = [p[0].0[1], p[1].0[1], p[2].0[1], p[3].0[1]];
    let p_ys = Avx2GoldilocksField::from_slice(&p_ys);

    let neg_pys = -*p_ys;
    let seven_p_ys = p_ys.mul(Goldilocks(7));
    let neg_seven_p_ys = -seven_p_ys;

    let res1 = eval_avx2_internal(
        &x_and_y[..2],
        &p[0].0[0],
        &p[0].0[1],
        &neg_pys.0[0],
        &seven_p_ys.0[0],
        &neg_seven_p_ys.0[0],
    );

    let res2 = eval_avx2_internal(
        &x_and_y[2..4],
        &p[1].0[0],
        &p[1].0[1],
        &neg_pys.0[1],
        &seven_p_ys.0[1],
        &neg_seven_p_ys.0[1],
    );

    let res3 = eval_avx2_internal(
        &x_and_y[4..6],
        &p[2].0[0],
        &p[2].0[1],
        &neg_pys.0[2],
        &seven_p_ys.0[2],
        &neg_seven_p_ys.0[2],
    );

    let res4 = eval_avx2_internal(
        &x_and_y[6..],
        &p[3].0[0],
        &p[3].0[1],
        &neg_pys.0[3],
        &seven_p_ys.0[3],
        &neg_seven_p_ys.0[3],
    );

    [res1, res2, res3, res4]
}

fn eval_avx2(x_and_y: &[GoldilocksExt2], p: &GoldilocksExt2) -> GoldilocksExt2 {
    let neg_p1 = -p.0[1];
    let seven_p1 = p.0[1] * Goldilocks(7);
    let neg_seven_p1 = -seven_p1;

    eval_avx2_internal(x_and_y, &p.0[0], &p.0[1], &neg_p1, &seven_p1, &neg_seven_p1)
}

fn eval_avx2_internal(
    x_and_y: &[GoldilocksExt2],
    p0: &Goldilocks,
    p1: &Goldilocks,
    neg_p1: &Goldilocks,
    seven_p1: &Goldilocks,
    neg_seven_p1: &Goldilocks,
) -> GoldilocksExt2 {
    let neg_p0 = -*p0;

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

    let x0_x1_y0_y1 = unsafe { from_raw_parts(x_and_y.as_ptr() as *const Goldilocks, 4) };
    let x0_x1_y0_y1 = Avx2GoldilocksField::from_slice(x0_x1_y0_y1);
    let p0_multiplicand = Avx2GoldilocksField([neg_p0, neg_p0, *p0, *p0]);
    let p1_multiplicand = Avx2GoldilocksField([*neg_p1, *neg_seven_p1, *p1, *seven_p1]);

    let r1 = *x0_x1_y0_y1 * p0_multiplicand;
    let r2 = *x0_x1_y0_y1 * p1_multiplicand;

    GoldilocksExt2([
        Goldilocks::sum_5(&r1.0[0], &r1.0[2], &r2.0[1], &r2.0[3], &x_and_y[0].0[0]),
        Goldilocks::sum_5(&r1.0[1], &r1.0[3], &r2.0[0], &r2.0[2], &x_and_y[0].0[1]),
    ])
}

#[cfg(test)]
mod test {
    use crate::util::mle_helper::{eval_4_avx2, eval_avx2};
    use crate::GoldilocksExt2;
    use ark_std::test_rng;
    use ff::Field;

    #[test]
    fn test_eval() {
        {
            let x = GoldilocksExt2([1.into(), 2.into()]);
            let y = GoldilocksExt2([3.into(), 4.into()]);
            let p = GoldilocksExt2([5.into(), 6.into()]);

            let res = eval_avx2(&[x, y], &p);
            let res2 = p * (y - x) + x;
            assert_eq!(res, res2);
        }

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

    #[test]
    fn test_eval_4() {
        {
            let x_and_y = [
                GoldilocksExt2([1.into(), 2.into()]),
                GoldilocksExt2([3.into(), 4.into()]),
                GoldilocksExt2([5.into(), 6.into()]),
                GoldilocksExt2([7.into(), 8.into()]),
                GoldilocksExt2([9.into(), 10.into()]),
                GoldilocksExt2([11.into(), 12.into()]),
                GoldilocksExt2([13.into(), 14.into()]),
                GoldilocksExt2([15.into(), 16.into()]),
            ];
            let p = [
                GoldilocksExt2([17.into(), 18.into()]),
                GoldilocksExt2([19.into(), 20.into()]),
                GoldilocksExt2([21.into(), 22.into()]),
                GoldilocksExt2([23.into(), 24.into()]),
            ];

            let res = eval_4_avx2(&x_and_y, &p);
            let res2: [GoldilocksExt2; 4] = x_and_y
                .chunks(2)
                .zip(p.iter())
                .map(|(x_and_y, &p)| p * (x_and_y[1] - x_and_y[0]) + x_and_y[0])
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();

            assert_eq!(res, res2);
        }

        let mut rng = test_rng();
        for _ in 0..100 {
            let x_and_ys = (0..8)
                .map(|_| GoldilocksExt2::random(&mut rng))
                .collect::<Vec<_>>();
            let ps = (0..4)
                .map(|_| GoldilocksExt2::random(&mut rng))
                .collect::<Vec<_>>();

            let res = eval_4_avx2(&x_and_ys, &ps);
            let res2: [GoldilocksExt2; 4] = x_and_ys
                .chunks(2)
                .zip(ps.iter())
                .map(|(x_and_y, &p)| p * (x_and_y[1] - x_and_y[0]) + x_and_y[0])
                .collect::<Vec<_>>()
                .try_into()
                .unwrap();
            assert_eq!(res, res2);
        }
    }
}

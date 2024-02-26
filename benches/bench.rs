use ark_std::test_rng;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ff::Field;
use goldilocks::{
    EvalHelper, ExtensionField, Goldilocks, GoldilocksExt2, GoldilocksExt3, SmallField,
};
use halo2curves::bn256::Fr;
use rand_core::SeedableRng;
use rand_xorshift::XorShiftRng;

const SIZE: usize = 1000;

criterion_main!(bench);

criterion_group!(bench, bench_avx2, bench_sum_5, bench_fields);

fn bench_sum_5(crit: &mut Criterion) {
    let mut rng = test_rng();
    let a = (0..SIZE)
        .map(|_| Goldilocks::random(&mut rng))
        .collect::<Vec<_>>();
    let b = (0..SIZE)
        .map(|_| Goldilocks::random(&mut rng))
        .collect::<Vec<_>>();
    let c = (0..SIZE)
        .map(|_| Goldilocks::random(&mut rng))
        .collect::<Vec<_>>();
    let d = (0..SIZE)
        .map(|_| Goldilocks::random(&mut rng))
        .collect::<Vec<_>>();
    let e = (0..SIZE)
        .map(|_| Goldilocks::random(&mut rng))
        .collect::<Vec<_>>();

    let bench_str = format!("{} sum 5", SIZE);
    crit.bench_function(&bench_str, |bencher| {
        bencher.iter(|| {
            a.iter()
                .zip(b.iter().zip(c.iter().zip(d.iter().zip(e.iter()))))
                .map(|(ai, (bi, (ci, (di, ei))))| Goldilocks::sum_5(ai, bi, ci, di, ei))
                .collect::<Vec<_>>()
        })
    });
}

fn bench_avx2(c: &mut Criterion) {
    let mut rng = test_rng();

    {
        let x_and_y = (0..SIZE << 1)
            .map(|_| GoldilocksExt2::random(&mut rng))
            .collect::<Vec<_>>();
        let z = (0..SIZE)
            .map(|_| GoldilocksExt2::random(&mut rng))
            .collect::<Vec<_>>();

        let id = "eval single non-avx2";
        c.bench_function(id, |b| {
            b.iter(|| {
                black_box(x_and_y.chunks(2).zip(z.iter()).for_each(|(x_and_yi, zi)| {
                    let _ = *zi * (x_and_yi[1] - x_and_yi[0]) + x_and_yi[0];
                }))
            })
        });

        let id = "eval single avx2";
        c.bench_function(id, |b| {
            b.iter(|| {
                black_box(x_and_y.chunks(2).zip(z.iter()).for_each(|(x_and_yi, zi)| {
                    let _ = <GoldilocksExt2 as EvalHelper>::eval_helper(x_and_yi, zi);
                }))
            })
        });
    }

    {
        let x_and_y = (0..SIZE << 1)
            .map(|_| {
                (0..8)
                    .map(|_| GoldilocksExt2::random(&mut rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        let z = (0..SIZE)
            .map(|_| {
                (0..4)
                    .map(|_| GoldilocksExt2::random(&mut rng))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        let id = "eval batch 4 non-avx2";
        c.bench_function(id, |b| {
            b.iter(|| {
                black_box(x_and_y.iter().zip(z.iter()).for_each(|(x_and_ys, zis)| {
                    x_and_ys
                        .chunks(2)
                        .zip(zis.iter())
                        .for_each(|(x_and_y, &p)| {
                            let _ = p * (x_and_y[1] - x_and_y[0]) + x_and_y[0];
                        });
                }))
            })
        });

        let id = "eval batch 4  avx2";
        c.bench_function(id, |b| {
            b.iter(|| {
                black_box(x_and_y.iter().zip(z.iter()).for_each(|(x_and_yi, zi)| {
                    let _ = <GoldilocksExt2 as EvalHelper>::eval_helper_4(x_and_yi, zi);
                }))
            })
        });
    }
}

fn bench_fields(c: &mut Criterion) {
    bench_field::<Goldilocks>(c, <Goldilocks as SmallField>::NAME);
    bench_field::<GoldilocksExt2>(c, GoldilocksExt2::NAME);
    bench_field::<GoldilocksExt3>(c, GoldilocksExt3::NAME);
    bench_field::<Fr>(c, "Bn256 scalar")
}

fn bench_field<F: Field>(c: &mut Criterion, field_name: &str) {
    let mut bench_group = c.benchmark_group(format!("{}", field_name));

    let mut rng = XorShiftRng::from_seed([
        0x59, 0x62, 0xbe, 0x5d, 0x76, 0x3d, 0x31, 0x8d, 0x17, 0xdb, 0x37, 0x32, 0x54, 0x06, 0xbc,
        0xe5,
    ]);
    let a = (0..SIZE).map(|_| F::random(&mut rng)).collect::<Vec<_>>();
    let b = (0..SIZE).map(|_| F::random(&mut rng)).collect::<Vec<_>>();

    let bench_str = format!("{} additions", SIZE);
    bench_group.bench_function(bench_str, |bencher| {
        bencher.iter(|| {
            a.iter()
                .zip(b.iter())
                .map(|(&ai, &bi)| ai + bi)
                .collect::<Vec<_>>()
        })
    });

    let bench_str = format!("{} multiplications", SIZE);
    bench_group.bench_function(bench_str, |bencher| {
        bencher.iter(|| {
            a.iter()
                .zip(b.iter())
                .map(|(&ai, &bi)| ai * bi)
                .collect::<Vec<_>>()
        })
    });
    bench_group.finish();
}

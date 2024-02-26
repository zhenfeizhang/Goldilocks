Implementation of Goldilocks and its extension fields
------

This repo implements 
- Goldilocks Field mod `2^64 - 2^32 + 1`
- Goldilocks quadratic extension over `x^2 - 7`
- Goldilocks cubic extension over `x^3 - x - 1`
- AVX2 acceleration for core operation inMLE 

Traits are compatible with `ff 0.13.0`.

### Benchmark
Without AVX2
```
cargo bench
```

With AVX2
```
RUSTFLAGS='-C target-feature=+avx2' cargo bench
```
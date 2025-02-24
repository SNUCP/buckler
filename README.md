# Buckler: Fast Zero Knowledge Proofs for MGHE Keys & Ciphertexts

You need to install nightly toolchain of rustc to run the code.

```
$ RUSTFLAGS="-C target-cpu=native" cargo run --release
Log N: 14
Log n: 13
Log Q: 429
prove_pkenc: 148.252989802s
verify_pkenc: 19.143085714s
pkenc_vf: true
prove_ddec: 154.905826912s
verify_ddec: 18.418313079s
ddist_vf: true
prove_pk: 29.855548753s
verify_pk: 3.884327661s
pk_vf: true
prove_rlk: 203.280604575s
verify_rlk: 24.013340283s
rlk_vf: true
prove_evk: 338.974928306s
verify_evk: 41.223845127s
evk_vf: true
```

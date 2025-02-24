#![allow(non_snake_case)]

use std::time::Instant;

use buckler::{celpc, rlwe, *};

fn main() {
    let params = Parameters::log_n_14();
    println!("Log N: {}", params.rlwe.n.ilog2());
    println!("Log n: {}", params.pcs.n.ilog2());
    println!("Log Q: {}", params.rlwe.q.significant_bits());

    let mut kg = rlwe::KeyGenerator::new(&params.rlwe);
    let sk = kg.gen_secret_key();
    let pk = kg.gen_public_key(&sk);
    let rlk = kg.gen_relin_key(&sk);
    let atk_0 = kg.gen_aut_key(&sk, 5);
    let atk_1 = kg.gen_aut_key(&sk, 2 * params.rlwe.n - 1);

    let m_ntt = vec![rug::Integer::from(2); params.rlwe.n];
    let ct = kg.gen_pk_encryption(&pk, &m_ntt, &params.rlwe.delta);
    let pd = kg.gen_dist_decryption(&sk, &ct);

    let ck = celpc::CommitKey::new(&params.pcs, &[0, 0, 0, 0]);

    let mut prover = Prover::new(&params, &ck);
    let mut verifier = Verifier::new(&params, &ck);

    let now = Instant::now();
    let pkenc_pf = prover.prove_pkenc(&pk, &ct);
    println!("prove_pkenc: {:?}", now.elapsed());

    let now = Instant::now();
    let pkenc_vf = verifier.verify_pkenc(&pk, &ct, &pkenc_pf);
    println!("verify_pkenc: {:?}", now.elapsed());
    println!("pkenc_vf: {:?}", pkenc_vf);

    let now = Instant::now();
    let ddist_pf = prover.prove_ddec(&sk, &pk, &ct, &pd);
    println!("prove_ddec: {:?}", now.elapsed());

    let now = Instant::now();
    let ddist_vf = verifier.verify_ddec(&pk, &ct, &pd, &ddist_pf);
    println!("verify_ddec: {:?}", now.elapsed());
    println!("ddist_vf: {:?}", ddist_vf);

    let now = Instant::now();
    let pk_pf = prover.prove_pk(&sk, &pk);
    println!("prove_pk: {:?}", now.elapsed());

    let now = Instant::now();
    let pk_vf = verifier.verify_pk(&pk, &pk_pf);
    println!("verify_pk: {:?}", now.elapsed());
    println!("pk_vf: {:?}", pk_vf);

    let now = Instant::now();
    let rlk_pf = prover.prove_evk(&sk, &pk, &rlk, vec![]);
    println!("prove_rlk: {:?}", now.elapsed());

    let now = Instant::now();
    let rlk_vf = verifier.verify_evk(&pk, &rlk, vec![], &rlk_pf);
    println!("verify_rlk: {:?}", now.elapsed());
    println!("rlk_vf: {:?}", rlk_vf);

    let now = Instant::now();
    let evk_pf = prover.prove_evk(&sk, &pk, &rlk, vec![&atk_0, &atk_1]);
    println!("prove_evk: {:?}", now.elapsed());

    let now = Instant::now();
    let evk_vf = verifier.verify_evk(&pk, &rlk, vec![&atk_0, &atk_1], &evk_pf);
    println!("verify_evk: {:?}", now.elapsed());
    println!("evk_vf: {:?}", evk_vf);
}

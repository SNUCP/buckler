#![allow(non_snake_case)]

use std::time::Instant;

use buckler::{celpc, *};

fn main() {
    let params = Parameters::log_n_14_pk();
    println!("LogN: {}", params.bfv.n.ilog2());
    println!("Logn: {}", params.pcs.n.ilog2());

    let ck = celpc::CommitKey::new(&params.pcs, &[0, 0, 0, 0]);

    let now = Instant::now();
    let mut kg = bfv::KeyGenerator::new(&params.bfv);
    let sk = kg.gen_secret_key();
    let pk = kg.gen_public_key(&sk);
    // let rlk = kg.gen_relin_key(&sk);
    // let atk0 = kg.gen_aut_key(&sk, 5);
    // let atk1 = kg.gen_aut_key(&sk, 2 * params.bfv.n - 1);
    println!("gen_key: {:?}", now.elapsed());

    let now = Instant::now();
    let mut prover = Prover::new(&params, &ck);
    println!("new_prover: {:?}", now.elapsed());

    let now = Instant::now();
    let mut verifier = Verifier::new(&params, &ck);
    println!("new_verifier: {:?}", now.elapsed());

    let now = Instant::now();
    let pf = prover.ternary_pk_proof(&sk, &pk);
    println!("ternary_pk_proof: {:?}", now.elapsed());

    let now = Instant::now();
    let v = verifier.ternary_pk_proof(&pf, &pk);
    println!("verify_ternary_pk_proof: {:?}", now.elapsed());
    println!("verify_ternary_pk_proof result: {}", v);

    // let now = Instant::now();
    // let apf = prover.ternary_pk_rlk_atk_proof(&sk, &pk, &rlk, &[&atk0, &atk1]);
    // println!("ternary_pk_rlk_atk_proof: {:?}", now.elapsed());

    // let now = Instant::now();
    // let v = verifier.ternary_pk_rlk_atk_proof(&apf, &pk, &rlk, &[&atk0, &atk1]);
    // println!("verify_ternary_pk_rlk_atk_proof: {:?}", now.elapsed());
    // println!("verify_ternary_pk_rlk_atk_proof result: {}", v);
}

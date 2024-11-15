use celpc::{
    BatchEvaluationProof, BatchOpenProof, BatchPolynomialCommitment, CommitKey,
    PolynomialCommitment,
};
use csprng::Oracle;
use rug::{Assign, Complete, Integer};

use crate::*;

#[derive(Clone)]
pub enum LinCheckType {
    NTT,
    Automorphism(usize),
}

#[derive(Clone)]
pub struct RowCheckProof {
    /// Usually denoted as k
    pub input_len: usize,
    /// 0 ~ k-1: ai_alpha,
    /// k: q_alpha
    pub eval_alpha: Vec<Integer>,

    pub poly_commit: BatchPolynomialCommitment,
    pub eval_pf: BatchEvaluationProof,
    pub open_pf: BatchOpenProof,
}

#[derive(Clone)]
pub struct LinCheckProof {
    /// Usually denoted as k
    pub input_len: usize,
    /// 0 ~ k-1: ai_alpha,
    /// k ~ 2k-1: bi_alpha,
    /// 2k: g_alpha,
    pub eval_alpha_1: Vec<Integer>,
    /// 0: q_alpha,
    /// 1: r_alpha
    pub eval_alpha_2: Vec<Integer>,

    pub mu: Integer,

    pub poly_commit_1: BatchPolynomialCommitment,
    pub eval_pf_1: BatchEvaluationProof,
    pub open_pf_1: BatchOpenProof,

    pub poly_commit_2: BatchPolynomialCommitment,
    pub eval_pf_2: BatchEvaluationProof,
    pub open_pf_2: BatchOpenProof,

    pub check_type: LinCheckType,
}

#[derive(Clone)]
pub struct GeneralizedRowCheckProof {
    /// Usually denoted as k
    pub input_len: usize,
    /// 0 ~ k-1: ai_alpha,
    /// k: q_alpha
    pub eval_alpha: Vec<Integer>,

    pub poly_commit: BatchPolynomialCommitment,
    pub eval_pf: BatchEvaluationProof,
    pub open_pf: BatchOpenProof,
}

#[derive(Clone)]
pub struct TernaryPublicKeyProof {
    pub ntt_linear_check_pf: LinCheckProof,

    pub sk_norm_row_check_pf: RowCheckProof,
    pub epk_norm_row_check_pf: RowCheckProof,

    pub pk_gen_row_check_pf: GeneralizedRowCheckProof,
}

#[derive(Clone)]
pub struct TenaryPublicRelinKeyProof {
    pub ntt_linear_check_pf: LinCheckProof,

    pub sk_norm_row_check_pf: RowCheckProof,
    pub pk_gen_row_check_pf: GeneralizedRowCheckProof,
    pub epk_norm_row_check_pf: RowCheckProof,

    pub rlk_gen_row_check_pf_1: Vec<GeneralizedRowCheckProof>,
    pub rlk_gen_row_check_pf_2: Vec<GeneralizedRowCheckProof>,
    pub rlk_gen_row_check_pf_3: Vec<GeneralizedRowCheckProof>,

    pub erlk_norm_row_check_pf: Vec<Vec<RowCheckProof>>,
    pub frlk_norm_row_check_pf: RowCheckProof,
}

#[derive(Clone)]
pub struct TenaryPublicRelinAutKeyProof {
    pub ntt_linear_check_pf: LinCheckProof,

    pub sk_norm_row_check_pf: RowCheckProof,
    pub pk_gen_row_check_pf: GeneralizedRowCheckProof,
    pub epk_norm_row_check_pf: RowCheckProof,

    pub rlk_gen_row_check_pf_1: Vec<GeneralizedRowCheckProof>,
    pub rlk_gen_row_check_pf_2: Vec<GeneralizedRowCheckProof>,
    pub rlk_gen_row_check_pf_3: Vec<GeneralizedRowCheckProof>,

    pub erlk_norm_row_check_pf: Vec<Vec<RowCheckProof>>,
    pub frlk_norm_row_check_pf: RowCheckProof,
    pub aut_linear_check_pf: Vec<LinCheckProof>,
    pub eatk_norm_row_check_pf: Vec<RowCheckProof>,
    pub atk_gen_row_check_pf: Vec<Vec<GeneralizedRowCheckProof>>,
}

impl Oracle {
    pub fn write_polynomial_commitment(&mut self, pc: &PolynomialCommitment) {
        pc.eta.iter().flatten().for_each(|p| self.write_poly(p));
        pc.h.iter().flatten().for_each(|p| self.write_poly(p));
        pc.h_commit
            .iter()
            .flatten()
            .for_each(|p| self.write_poly(p));
    }
}

pub struct Prover<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_prover: celpc::PolynomialProver<'a>,

    pub oracle: Oracle,

    pub ringp: BigRing,
    pub neg_transformer: bfv::NegacyclicTransformer,
}

impl<'a> Prover<'a> {
    pub fn new(params: &'a Parameters, ck: &'a CommitKey) -> Self {
        let encoder = Encoder::new(params);

        Prover {
            params: params,
            encoder: encoder,

            celpc_prover: celpc::PolynomialProver::new(&params.pcs, ck),
            oracle: Oracle::new(),

            ringp: BigRing::new(params.embedding_n, &params.bfv.q),
            neg_transformer: bfv::NegacyclicTransformer::new(params.bfv.n, &params.bfv.q),
        }
    }

    pub fn row_check(&mut self, vec_ai: &[&[Integer]], c: &BigMultiVariatePoly) -> RowCheckProof {
        let k = vec_ai.len();

        // Move 1
        let mut ai_coeffs = Vec::with_capacity(k);
        let mut ai_ntt = Vec::with_capacity(k);
        for i in 0..k {
            ai_coeffs.push(self.encoder.encode_randomize(&vec_ai[i]));
            ai_ntt.push(ai_coeffs[i].clone());
            self.ringp.ntt(&mut ai_ntt[i]);
        }

        let mut ca = self.ringp.evaluate_multivariate_poly(c, &ai_ntt);
        self.ringp.intt(&mut ca);

        let (q, _) = self.ringp.quo_rem_zero(&ca, self.params.bfv.n);

        // ai has degree 2N
        // q has degree (2 * c.degree - 1) * N
        let mut poly_batch = Vec::with_capacity(k + 1);
        for i in 0..k {
            poly_batch.push(&ai_coeffs[i].coeffs[..2 * self.params.bfv.n]);
        }
        poly_batch.push(&q.coeffs[..2 * c.max_degree * self.params.bfv.n]);

        let poly_commit = self.celpc_prover.commit_batch(&poly_batch);
        let open_pf = self.celpc_prover.prove_batch(&poly_commit);

        self.oracle
            .write_polynomial_commitment(&poly_commit.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        // Move 2
        let mut eval_alpha = Vec::with_capacity(k + 1);
        for i in 0..k {
            eval_alpha.push(self.ringp.evaluate(&ai_coeffs[i], &alpha));
        }
        eval_alpha.push(self.ringp.evaluate(&q, &alpha));

        let eval_pf =
            self.celpc_prover
                .evaluate_batch(&alpha, &alpha_combine, &eval_alpha, &poly_commit);

        return RowCheckProof {
            input_len: k,
            eval_alpha: eval_alpha,

            poly_commit: poly_commit,
            eval_pf: eval_pf,
            open_pf: open_pf,
        };
    }

    pub fn lin_check(
        &mut self,
        vec_ai: &[&[Integer]],
        vec_bi: &[&[Integer]],
        check_type: LinCheckType,
    ) -> LinCheckProof {
        let k = vec_ai.len();

        // Move 1
        let mut ai_coeffs = Vec::with_capacity(k);
        let mut ai_ntt = Vec::with_capacity(k);
        let mut bi_coeffs = Vec::with_capacity(k);
        let mut bi_ntt = Vec::with_capacity(k);
        for i in 0..k {
            ai_coeffs.push(self.encoder.encode_randomize(&vec_ai[i]));
            ai_ntt.push(ai_coeffs[i].clone());
            self.ringp.ntt(&mut ai_ntt[i]);

            bi_coeffs.push(self.encoder.encode_randomize(&vec_bi[i]));
            bi_ntt.push(bi_coeffs[i].clone());
            self.ringp.ntt(&mut bi_ntt[i]);
        }

        let mut g = self.ringp.new_poly();
        for i in 0..self.params.bfv.n {
            g.coeffs[i] = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.bfv.q);
        }

        let mut g = self.ringp.new_poly();
        for i in 0..self.params.bfv.n {
            g.coeffs[i] = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.bfv.q);
        }
        let mu = g.coeffs[0].clone();
        for i in 0..2 * self.params.bfv.n {
            let c = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.bfv.q);

            // Add c * X^i * (X^N - 1)
            g.coeffs[i] -= &c;
            if g.coeffs[i].is_negative() {
                g.coeffs[i] += &self.params.bfv.q;
            }

            g.coeffs[i + self.params.bfv.n] += &c;
            if g.coeffs[i + self.params.bfv.n] >= self.params.bfv.q {
                g.coeffs[i + self.params.bfv.n] -= &self.params.bfv.q;
            }
        }

        // ai has degree 2N
        // bi has degree 2N
        // g has degree 3N
        let mut poly_batch_1 = Vec::with_capacity(2 * k + 1);
        for i in 0..k {
            poly_batch_1.push(&ai_coeffs[i].coeffs[..2 * self.params.bfv.n]);
        }
        for i in 0..k {
            poly_batch_1.push(&bi_coeffs[i].coeffs[..2 * self.params.bfv.n]);
        }
        poly_batch_1.push(&g.coeffs[..3 * self.params.bfv.n]);

        let poly_commit_1 = self.celpc_prover.commit_batch(&poly_batch_1);
        let open_pf_1 = self.celpc_prover.prove_batch(&poly_commit_1);

        // Move 2
        self.oracle
            .write_polynomial_commitment(&poly_commit_1.poly_commit);
        self.oracle.write_bigint(&mu);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.bfv.q);
        let v_big = self.oracle.read_range_bigint(&self.params.bfv.q);

        // Move 3
        let mut vec_v = Vec::with_capacity(self.params.bfv.n);
        vec_v.push(Integer::from(1));
        for i in 1..self.params.bfv.n {
            vec_v.push(vec_v[i - 1].clone());
            vec_v[i] *= &v_big;
            vec_v[i].modulo_mut(&self.params.bfv.q);
        }

        let mut vec_w;
        match check_type {
            LinCheckType::NTT => {
                vec_w = vec_v.clone();
                vec_w.reverse();
                self.neg_transformer.intt_without_normalize(&mut vec_w);
            }
            LinCheckType::Automorphism(d) => {
                vec_w = self.neg_transformer.automorphism(
                    &vec_v,
                    modinverse::modinverse(d, 2 * self.params.bfv.n).unwrap(),
                );
            }
        }

        let mut v = self.encoder.encode(&vec_v);
        self.ringp.ntt(&mut v);
        let mut w = self.encoder.encode(&vec_w);
        self.ringp.ntt(&mut w);

        let mut f = self.ringp.new_ntt_poly();
        let mut aw = self.ringp.new_ntt_poly();
        let mut bv = self.ringp.new_ntt_poly();
        let mut beta_pow = beta.clone();
        for i in 0..k {
            self.ringp.mul_assign(&ai_ntt[i], &w, &mut aw);
            self.ringp.mul_assign(&bi_ntt[i], &v, &mut bv);
            self.ringp.sub_inplace(&bv, &mut aw);
            self.ringp.mul_const_inplace(&beta_pow, &mut aw);
            self.ringp.add_inplace(&aw, &mut f);
            beta_pow *= &beta;
            beta_pow.modulo_mut(&self.params.bfv.q);
        }
        self.ringp.intt(&mut f);
        self.ringp.add_inplace(&g, &mut f);

        let (q, mut r) = self.ringp.quo_rem_zero(&f, self.params.bfv.n);
        r.coeffs.drain(0..1);
        r.coeffs.push(Integer::ZERO);

        // q has degree 2N
        // r has degree N
        let poly_batch_2 = vec![
            &q.coeffs[..2 * self.params.bfv.n],
            &r.coeffs[..self.params.bfv.n],
        ];
        let poly_commit_2 = self.celpc_prover.commit_batch(&poly_batch_2);
        let open_pf_2 = self.celpc_prover.prove_batch(&poly_commit_2);

        // Move 4
        self.oracle
            .write_polynomial_commitment(&poly_commit_2.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        let mut eval_alpha_1 = Vec::with_capacity(2 * k + 1);
        for i in 0..k {
            eval_alpha_1.push(self.ringp.evaluate(&ai_coeffs[i], &alpha));
        }
        for i in 0..k {
            eval_alpha_1.push(self.ringp.evaluate(&bi_coeffs[i], &alpha));
        }
        eval_alpha_1.push(self.ringp.evaluate(&g, &alpha));
        let eval_pf_1 =
            self.celpc_prover
                .evaluate_batch(&alpha, &alpha_combine, &eval_alpha_1, &poly_commit_1);

        let eval_alpha_2 = vec![
            self.ringp.evaluate(&q, &alpha),
            self.ringp.evaluate(&r, &alpha),
        ];
        let eval_pf_2 =
            self.celpc_prover
                .evaluate_batch(&alpha, &alpha_combine, &eval_alpha_2, &poly_commit_2);

        return LinCheckProof {
            input_len: k,

            eval_alpha_1: eval_alpha_1,
            eval_alpha_2: eval_alpha_2,

            mu: mu,

            poly_commit_1: poly_commit_1,
            eval_pf_1: eval_pf_1,
            open_pf_1: open_pf_1,

            poly_commit_2: poly_commit_2,
            eval_pf_2: eval_pf_2,
            open_pf_2: open_pf_2,

            check_type: check_type,
        };
    }

    pub fn generalized_row_check(
        &mut self,
        vec_ai: &[&[Integer]],
        c: &PolyMultiVariatePoly,
    ) -> GeneralizedRowCheckProof {
        let k = vec_ai.len();

        // Move 1
        let mut ai_coeffs = Vec::with_capacity(k);
        let mut ai_ntt = Vec::with_capacity(k);
        for i in 0..k {
            ai_coeffs.push(self.encoder.encode_randomize(&vec_ai[i]));
            ai_ntt.push(ai_coeffs[i].clone());
            self.ringp.ntt(&mut ai_ntt[i]);
        }

        let mut ca = self.ringp.evaluate_poly_multivariate_poly(c, &ai_ntt);
        self.ringp.intt(&mut ca);

        let (q, _) = self.ringp.quo_rem_zero(&ca, self.params.bfv.n);

        // ai has degree 2N
        // q has degree (2 * c.degree - 1) * N
        let mut poly_batch = Vec::with_capacity(k + 1);
        for i in 0..k {
            poly_batch.push(&ai_coeffs[i].coeffs[..2 * self.params.bfv.n]);
        }
        poly_batch.push(&q.coeffs[..2 * c.max_degree * self.params.bfv.n]);

        let poly_commit = self.celpc_prover.commit_batch(&poly_batch);
        let open_pf = self.celpc_prover.prove_batch(&poly_commit);

        self.oracle
            .write_polynomial_commitment(&poly_commit.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        // Move 2
        let mut eval_alpha = Vec::with_capacity(k + 1);
        for i in 0..k {
            eval_alpha.push(self.ringp.evaluate(&ai_coeffs[i], &alpha));
        }
        eval_alpha.push(self.ringp.evaluate(&q, &alpha));

        let eval_pf =
            self.celpc_prover
                .evaluate_batch(&alpha, &alpha_combine, &eval_alpha, &poly_commit);

        return GeneralizedRowCheckProof {
            input_len: k,

            eval_alpha: eval_alpha,

            poly_commit: poly_commit,
            eval_pf: eval_pf,
            open_pf: open_pf,
        };
    }

    pub fn ternary_pk_proof(
        &mut self,
        sk: &bfv::SecretKey,
        pk: &bfv::PublicKey,
    ) -> TernaryPublicKeyProof {
        let ntt_linear_check_pf = self.lin_check(
            &[&sk.coeffs, &pk.epk_coeffs],
            &[&sk.ntt, &pk.epk_ntt],
            LinCheckType::NTT,
        );

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };

        let sk_norm_row_check_pf = self.row_check(&[&sk.coeffs], &norm_row_check_c);
        let epk_norm_row_check_pf = self.row_check(&[&pk.epk_coeffs], &norm_row_check_c);

        let mut p_ecd = self.encoder.encode(&pk.p_ntt);
        let mut u_ecd = self.encoder.encode(&pk.u_ntt);
        let mut neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        self.ringp.ntt(&mut p_ecd);
        self.ringp.ntt(&mut u_ecd);
        self.ringp.ntt(&mut neg_one_ecd);

        let gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };

        let pk_gen_row_check_pf =
            self.generalized_row_check(&[&sk.ntt, &pk.epk_ntt], &gen_row_check_c);

        return TernaryPublicKeyProof {
            ntt_linear_check_pf: ntt_linear_check_pf,

            sk_norm_row_check_pf,
            epk_norm_row_check_pf,

            pk_gen_row_check_pf: pk_gen_row_check_pf,
        };
    }

    pub fn ternary_pk_rlk_proof(
        &mut self,
        sk: &bfv::SecretKey,
        pk: &bfv::PublicKey,
        rlk: &bfv::RelinKey,
    ) -> TenaryPublicRelinKeyProof {
        let level = self.params.bfv.gadget.len();

        let mut linear_check_coeffs: Vec<&[Integer]> =
            vec![&sk.coeffs, &pk.epk_coeffs, &rlk.f_coeffs];
        let mut linear_check_ntt: Vec<&[Integer]> = vec![&sk.ntt, &pk.epk_ntt, &rlk.f_ntt];
        for i in 0..level {
            linear_check_coeffs.push(&rlk.e_coeffs[0][i]);
            linear_check_coeffs.push(&rlk.e_coeffs[1][i]);
            linear_check_coeffs.push(&rlk.e_coeffs[2][i]);

            linear_check_ntt.push(&rlk.e_ntt[0][i]);
            linear_check_ntt.push(&rlk.e_ntt[1][i]);
            linear_check_ntt.push(&rlk.e_ntt[2][i]);
        }

        let ntt_linear_check_pf =
            self.lin_check(&linear_check_coeffs, &linear_check_ntt, LinCheckType::NTT);

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c_1 = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };

        let sk_norm_row_check_pf = self.row_check(&[&sk.coeffs], &norm_row_check_c_1);
        let epk_norm_row_check_pf = self.row_check(&[&pk.epk_coeffs], &norm_row_check_c_1);

        let mut erlk_norm_row_check_pf = Vec::with_capacity(3);
        for i in 0..3 {
            erlk_norm_row_check_pf.push(Vec::with_capacity(self.params.bfv.q_rns.len()));
            for j in 0..level {
                erlk_norm_row_check_pf[i]
                    .push(self.row_check(&[&rlk.e_coeffs[i][j]], &norm_row_check_c_1));
            }
        }
        let frlk_norm_row_check_pf = self.row_check(&[&rlk.f_coeffs], &norm_row_check_c_1);

        let mut p_ecd = self.encoder.encode(&pk.p_ntt);
        let mut u_ecd = self.encoder.encode(&pk.u_ntt);
        let mut neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        self.ringp.ntt(&mut p_ecd);
        self.ringp.ntt(&mut u_ecd);
        self.ringp.ntt(&mut neg_one_ecd);

        let pk_gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };

        let pk_gen_row_check_pf =
            self.generalized_row_check(&[&sk.ntt, &pk.epk_ntt], &pk_gen_row_check_c);

        let mut rlk_gen_row_check_pf_1 = Vec::with_capacity(self.params.bfv.q_rns.len());
        let mut rlk_gen_row_check_pf_2 = Vec::with_capacity(self.params.bfv.q_rns.len());
        let mut rlk_gen_row_check_pf_3 = Vec::with_capacity(self.params.bfv.q_rns.len());
        for i in 0..level {
            let mut u0_ecd = self.encoder.encode(&rlk.u_ntt[0][i]);
            let mut u1_ecd = self.encoder.encode(&rlk.u_ntt[1][i]);

            let mut r0_ecd = self.encoder.encode(&rlk.r_ntt[0][i]);
            let mut r1_ecd = self.encoder.encode(&rlk.r_ntt[1][i]);
            let mut r2_ecd = self.encoder.encode(&rlk.r_ntt[2][i]);

            self.ringp.ntt(&mut u0_ecd);
            self.ringp.ntt(&mut u1_ecd);

            self.ringp.ntt(&mut r0_ecd);
            self.ringp.ntt(&mut r1_ecd);
            self.ringp.ntt(&mut r2_ecd);

            let gi = vec![self.params.bfv.gadget[i].clone(); self.params.bfv.n];
            let mut gi_ecd = self.encoder.encode(&gi);
            self.ringp.ntt(&mut gi_ecd);

            let neg_gi = vec![
                self.params.bfv.q.clone() - self.params.bfv.gadget[i].clone();
                self.params.bfv.n
            ];
            let mut neg_gi_ecd = self.encoder.encode(&neg_gi);
            self.ringp.ntt(&mut neg_gi_ecd);

            let rlk_gen_row_check_c_1 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ecd, vec![0, 0]),
                    (u0_ecd.clone(), vec![1, 0]),
                    (neg_one_ecd.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_2 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ecd, vec![0, 0, 0]),
                    (u0_ecd, vec![1, 0, 0]),
                    (neg_gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_3 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ecd, vec![0, 0, 0]),
                    (u1_ecd, vec![1, 0, 0]),
                    (gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            rlk_gen_row_check_pf_1.push(
                self.generalized_row_check(&[&sk.ntt, &rlk.e_ntt[0][i]], &rlk_gen_row_check_c_1),
            );
            rlk_gen_row_check_pf_2.push(self.generalized_row_check(
                &[&rlk.f_ntt, &sk.ntt, &rlk.e_ntt[1][i]],
                &rlk_gen_row_check_c_2,
            ));
            rlk_gen_row_check_pf_3.push(self.generalized_row_check(
                &[&sk.ntt, &rlk.f_ntt, &rlk.e_ntt[2][i]],
                &rlk_gen_row_check_c_3,
            ));
        }

        return TenaryPublicRelinKeyProof {
            ntt_linear_check_pf: ntt_linear_check_pf,

            sk_norm_row_check_pf: sk_norm_row_check_pf,
            epk_norm_row_check_pf: epk_norm_row_check_pf,
            erlk_norm_row_check_pf: erlk_norm_row_check_pf,
            frlk_norm_row_check_pf: frlk_norm_row_check_pf,

            pk_gen_row_check_pf: pk_gen_row_check_pf,
            rlk_gen_row_check_pf_1: rlk_gen_row_check_pf_1,
            rlk_gen_row_check_pf_2: rlk_gen_row_check_pf_2,
            rlk_gen_row_check_pf_3: rlk_gen_row_check_pf_3,
        };
    }

    pub fn ternary_pk_rlk_atk_proof(
        &mut self,
        sk: &bfv::SecretKey,
        pk: &bfv::PublicKey,
        rlk: &bfv::RelinKey,
        atks: &[&bfv::AutomorphismKey],
    ) -> TenaryPublicRelinAutKeyProof {
        let level = self.params.bfv.gadget.len();
        let auts = atks.len();

        let mut linear_check_coeffs: Vec<&[Integer]> =
            vec![&sk.coeffs, &pk.epk_coeffs, &rlk.f_coeffs];
        let mut linear_check_ntt: Vec<&[Integer]> = vec![&sk.ntt, &pk.epk_ntt, &rlk.f_ntt];
        for i in 0..level {
            linear_check_coeffs.push(&rlk.e_coeffs[0][i]);
            linear_check_coeffs.push(&rlk.e_coeffs[1][i]);
            linear_check_coeffs.push(&rlk.e_coeffs[2][i]);

            linear_check_ntt.push(&rlk.e_ntt[0][i]);
            linear_check_ntt.push(&rlk.e_ntt[1][i]);
            linear_check_ntt.push(&rlk.e_ntt[2][i]);

            for j in 0..auts {
                linear_check_coeffs.push(&atks[j].e_coeffs[i]);
                linear_check_ntt.push(&atks[j].e_ntt[i]);
            }
        }
        let ntt_linear_check_pf =
            self.lin_check(&linear_check_coeffs, &linear_check_ntt, LinCheckType::NTT);

        let mut aut_lin_check_pf = Vec::with_capacity(auts);
        for i in 0..auts {
            aut_lin_check_pf.push(self.lin_check(
                &[&sk.ntt],
                &[&atks[i].sk_d_ntt],
                LinCheckType::Automorphism(atks[i].d),
            ));
        }

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c_1 = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };

        let sk_norm_row_check_pf = self.row_check(&[&sk.coeffs], &norm_row_check_c_1);
        let epk_norm_row_check_pf = self.row_check(&[&pk.epk_coeffs], &norm_row_check_c_1);

        let mut erlk_norm_row_check_pf = Vec::with_capacity(3);
        for i in 0..3 {
            erlk_norm_row_check_pf.push(Vec::with_capacity(self.params.bfv.q_rns.len()));
            for j in 0..level {
                erlk_norm_row_check_pf[i]
                    .push(self.row_check(&[&rlk.e_coeffs[i][j]], &norm_row_check_c_1));
            }
        }
        let frlk_norm_row_check_pf = self.row_check(&[&rlk.f_coeffs], &norm_row_check_c_1);

        let mut eatk_norm_row_check_pf = Vec::with_capacity(auts);
        for i in 0..auts {
            for j in 0..level {
                eatk_norm_row_check_pf
                    .push(self.row_check(&[&atks[i].e_coeffs[j]], &norm_row_check_c_1));
            }
        }

        let mut p_ecd = self.encoder.encode(&pk.p_ntt);
        let mut u_ecd = self.encoder.encode(&pk.u_ntt);
        let mut neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        self.ringp.ntt(&mut p_ecd);
        self.ringp.ntt(&mut u_ecd);
        self.ringp.ntt(&mut neg_one_ecd);

        let pk_gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };

        let pk_gen_row_check_pf =
            self.generalized_row_check(&[&sk.ntt, &pk.epk_ntt], &pk_gen_row_check_c);

        let mut rlk_gen_row_check_pf_1 = Vec::with_capacity(level);
        let mut rlk_gen_row_check_pf_2 = Vec::with_capacity(level);
        let mut rlk_gen_row_check_pf_3 = Vec::with_capacity(level);
        let mut atk_gen_row_check_pf = Vec::with_capacity(auts);
        for _ in 0..auts {
            atk_gen_row_check_pf.push(Vec::with_capacity(level));
        }
        for i in 0..level {
            let mut u0_ecd = self.encoder.encode(&rlk.u_ntt[0][i]);
            let mut u1_ecd = self.encoder.encode(&rlk.u_ntt[1][i]);

            let mut r0_ecd = self.encoder.encode(&rlk.r_ntt[0][i]);
            let mut r1_ecd = self.encoder.encode(&rlk.r_ntt[1][i]);
            let mut r2_ecd = self.encoder.encode(&rlk.r_ntt[2][i]);

            self.ringp.ntt(&mut u0_ecd);
            self.ringp.ntt(&mut u1_ecd);

            self.ringp.ntt(&mut r0_ecd);
            self.ringp.ntt(&mut r1_ecd);
            self.ringp.ntt(&mut r2_ecd);

            let gi = vec![self.params.bfv.gadget[i].clone(); self.params.bfv.n];
            let mut gi_ecd = self.encoder.encode(&gi);
            self.ringp.ntt(&mut gi_ecd);

            let neg_gi = vec![
                self.params.bfv.q.clone() - self.params.bfv.gadget[i].clone();
                self.params.bfv.n
            ];
            let mut neg_gi_ecd = self.encoder.encode(&neg_gi);
            self.ringp.ntt(&mut neg_gi_ecd);

            let rlk_gen_row_check_c_1 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ecd, vec![0, 0]),
                    (u0_ecd.clone(), vec![1, 0]),
                    (neg_one_ecd.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_2 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ecd, vec![0, 0, 0]),
                    (u0_ecd, vec![1, 0, 0]),
                    (neg_gi_ecd.clone(), vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_3 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ecd, vec![0, 0, 0]),
                    (u1_ecd, vec![1, 0, 0]),
                    (gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            rlk_gen_row_check_pf_1.push(
                self.generalized_row_check(&[&sk.ntt, &rlk.e_ntt[0][i]], &rlk_gen_row_check_c_1),
            );
            rlk_gen_row_check_pf_2.push(self.generalized_row_check(
                &[&rlk.f_ntt, &sk.ntt, &rlk.e_ntt[1][i]],
                &rlk_gen_row_check_c_2,
            ));
            rlk_gen_row_check_pf_3.push(self.generalized_row_check(
                &[&sk.ntt, &rlk.f_ntt, &rlk.e_ntt[2][i]],
                &rlk_gen_row_check_c_3,
            ));

            for j in 0..auts {
                let mut a_ecd = self.encoder.encode(&atks[j].a_ntt[i]);
                let mut u_ecd = self.encoder.encode(&atks[j].u_ntt[i]);

                self.ringp.ntt(&mut a_ecd);
                self.ringp.ntt(&mut u_ecd);

                let atk_gen_row_check_c = PolyMultiVariatePoly {
                    coeffs: vec![
                        (a_ecd, vec![0, 0, 0]),
                        (u_ecd, vec![1, 0, 0]),
                        (neg_gi_ecd.clone(), vec![0, 1, 0]),
                        (neg_one_ecd.clone(), vec![0, 0, 1]),
                    ],
                    max_degree: 1,
                };
                atk_gen_row_check_pf[j].push(self.generalized_row_check(
                    &[&sk.ntt, &atks[j].sk_d_ntt, &atks[j].e_ntt[i]],
                    &atk_gen_row_check_c,
                ));
            }
        }

        return TenaryPublicRelinAutKeyProof {
            ntt_linear_check_pf: ntt_linear_check_pf,

            sk_norm_row_check_pf: sk_norm_row_check_pf,
            epk_norm_row_check_pf: epk_norm_row_check_pf,
            erlk_norm_row_check_pf: erlk_norm_row_check_pf,
            frlk_norm_row_check_pf: frlk_norm_row_check_pf,

            pk_gen_row_check_pf: pk_gen_row_check_pf,
            rlk_gen_row_check_pf_1: rlk_gen_row_check_pf_1,
            rlk_gen_row_check_pf_2: rlk_gen_row_check_pf_2,
            rlk_gen_row_check_pf_3: rlk_gen_row_check_pf_3,

            eatk_norm_row_check_pf: eatk_norm_row_check_pf,
            aut_linear_check_pf: aut_lin_check_pf,
            atk_gen_row_check_pf: atk_gen_row_check_pf,
        };
    }
}

pub struct Verifier<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_verifier: celpc::PolynomialVerifier<'a>,

    pub oracle: Oracle,

    pub ringp: BigRing,
    pub neg_transformer: bfv::NegacyclicTransformer,
}

impl<'a> Verifier<'a> {
    pub fn new(params: &'a Parameters, ck: &'a CommitKey) -> Verifier<'a> {
        let encoder = Encoder::new(params);
        let celpc_verifier = celpc::PolynomialVerifier::new(&params.pcs, ck);

        Verifier {
            params: params,
            encoder: encoder,
            celpc_verifier: celpc_verifier,

            oracle: Oracle::new(),

            ringp: BigRing::new(params.embedding_n, &params.bfv.q),
            neg_transformer: bfv::NegacyclicTransformer::new(params.bfv.n, &params.bfv.q),
        }
    }

    pub fn row_check(&mut self, c: &BigMultiVariatePoly, row_check_pf: &RowCheckProof) -> bool {
        self.oracle
            .write_polynomial_commitment(&row_check_pf.poly_commit.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        if !self
            .celpc_verifier
            .verify_batch(&row_check_pf.poly_commit, &row_check_pf.open_pf)
        {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &row_check_pf.poly_commit,
            &row_check_pf.eval_pf,
        ) {
            return false;
        }

        let k = row_check_pf.input_len;

        let ai_alpha = &row_check_pf.eval_alpha[0..k];
        let q_alpha = &row_check_pf.eval_alpha[k];

        let mut z_alpha = alpha
            .pow_mod_ref(&Integer::from(self.params.bfv.n), &self.params.bfv.q)
            .unwrap()
            .complete();
        z_alpha -= Integer::ONE;
        z_alpha *= q_alpha;
        z_alpha.modulo_mut(&self.params.bfv.q);

        let mut y = self.ringp.evaluate_multivariate(c, ai_alpha);
        y -= &z_alpha;

        if !y.is_zero() {
            return false;
        }
        return true;
    }

    pub fn lin_check(&mut self, lin_check_ntt_pf: &LinCheckProof) -> bool {
        let k = lin_check_ntt_pf.input_len;

        self.oracle
            .write_polynomial_commitment(&lin_check_ntt_pf.poly_commit_1.poly_commit);
        self.oracle.write_bigint(&lin_check_ntt_pf.mu);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.bfv.q);
        let v_big = self.oracle.read_range_bigint(&self.params.bfv.q);
        let mut vec_v = Vec::with_capacity(self.params.bfv.n);
        vec_v.push(Integer::from(1));
        for i in 1..self.params.bfv.n {
            vec_v.push(vec_v[i - 1].clone());
            vec_v[i] *= &v_big;
            vec_v[i].modulo_mut(&self.params.bfv.q);
        }

        let mut vec_w;
        match lin_check_ntt_pf.check_type {
            LinCheckType::NTT => {
                vec_w = vec_v.clone();
                vec_w.reverse();
                self.neg_transformer.intt_without_normalize(&mut vec_w);
            }
            LinCheckType::Automorphism(d) => {
                vec_w = self.neg_transformer.automorphism(
                    &vec_v,
                    modinverse::modinverse(d, 2 * self.params.bfv.n).unwrap(),
                );
            }
        }

        let v = self.encoder.encode(&vec_v);
        let w = self.encoder.encode(&vec_w);

        self.oracle
            .write_polynomial_commitment(&lin_check_ntt_pf.poly_commit_2.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        if !self
            .celpc_verifier
            .verify_batch(&lin_check_ntt_pf.poly_commit_1, &lin_check_ntt_pf.open_pf_1)
        {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &lin_check_ntt_pf.poly_commit_1,
            &lin_check_ntt_pf.eval_pf_1,
        ) {
            return false;
        }

        if !self
            .celpc_verifier
            .verify_batch(&lin_check_ntt_pf.poly_commit_2, &lin_check_ntt_pf.open_pf_2)
        {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &lin_check_ntt_pf.poly_commit_2,
            &lin_check_ntt_pf.eval_pf_2,
        ) {
            return false;
        }

        let v_alpha = self.ringp.evaluate(&v, &alpha);
        let w_alpha = self.ringp.evaluate(&w, &alpha);

        let ai_alpha = &lin_check_ntt_pf.eval_alpha_1[0..k];
        let bi_alpha = &lin_check_ntt_pf.eval_alpha_1[k..2 * k];
        let g_alpha = &lin_check_ntt_pf.eval_alpha_1[2 * k];
        let q_alpha = &lin_check_ntt_pf.eval_alpha_2[0];
        let r_alpha = &lin_check_ntt_pf.eval_alpha_2[1];

        let mut lhs = g_alpha.clone();
        let mut beta_pow = beta.clone();
        let mut aw = Integer::ZERO;
        let mut bv = Integer::ZERO;
        for i in 0..k {
            aw.assign(&ai_alpha[i]);
            aw *= &w_alpha;

            bv.assign(&bi_alpha[i]);
            bv *= &v_alpha;

            aw -= &bv;
            aw.modulo_mut(&self.params.bfv.q);

            aw *= &beta_pow;
            aw.modulo_mut(&self.params.bfv.q);

            lhs += &aw;

            beta_pow *= &beta;
            beta_pow.modulo_mut(&self.params.bfv.q);
        }
        lhs.modulo_mut(&self.params.bfv.q);

        let mut buf = Integer::ZERO;
        let mut rhs = lin_check_ntt_pf.mu.clone();

        buf.assign(&alpha);
        buf *= r_alpha;
        rhs += buf;

        let mut z_alpha = alpha
            .pow_mod_ref(&Integer::from(self.params.bfv.n), &self.params.bfv.q)
            .unwrap()
            .complete();
        z_alpha -= Integer::ONE;
        z_alpha *= q_alpha;
        rhs += z_alpha;
        rhs.modulo_mut(&self.params.bfv.q);

        lhs -= &rhs;
        if !lhs.is_zero() {
            return false;
        }

        return true;
    }

    pub fn generalized_row_check(
        &mut self,
        c: &PolyMultiVariatePoly,
        generalized_row_check_pf: &GeneralizedRowCheckProof,
    ) -> bool {
        self.oracle
            .write_polynomial_commitment(&generalized_row_check_pf.poly_commit.poly_commit);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.bfv.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.bfv.q);

        if !self.celpc_verifier.verify_batch(
            &generalized_row_check_pf.poly_commit,
            &generalized_row_check_pf.open_pf,
        ) {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &generalized_row_check_pf.poly_commit,
            &generalized_row_check_pf.eval_pf,
        ) {
            return false;
        }

        let k = generalized_row_check_pf.input_len;

        let ai_alpha = &generalized_row_check_pf.eval_alpha[0..k];
        let q_alpha = &generalized_row_check_pf.eval_alpha[k];

        let mut c_big = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(c.coeffs.len()),
            max_degree: c.max_degree,
        };
        for i in 0..c.coeffs.len() {
            c_big.coeffs.push((
                self.ringp.evaluate(&c.coeffs[i].0, &alpha),
                c.coeffs[i].1.clone(),
            ));
        }
        let mut y = self.ringp.evaluate_multivariate(&c_big, &ai_alpha);

        let mut z_alpha = alpha
            .pow_mod_ref(&Integer::from(self.params.bfv.n), &self.params.bfv.q)
            .unwrap()
            .complete();
        z_alpha -= Integer::ONE;
        z_alpha *= q_alpha;
        z_alpha.modulo_mut(&self.params.bfv.q);
        y -= &z_alpha;

        if !y.is_zero() {
            return false;
        }
        return true;
    }

    pub fn ternary_pk_proof(
        &mut self,
        pk_proof: &TernaryPublicKeyProof,
        pk: &bfv::PublicKey,
    ) -> bool {
        if !self.lin_check(&pk_proof.ntt_linear_check_pf) {
            return false;
        }

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c_1 = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };
        if !self.row_check(&norm_row_check_c_1, &pk_proof.sk_norm_row_check_pf) {
            return false;
        }

        if !self.row_check(&norm_row_check_c_1, &pk_proof.epk_norm_row_check_pf) {
            return false;
        }

        let p_ecd = self.encoder.encode(&pk.p_ntt);
        let u_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        let gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.generalized_row_check(&gen_row_check_c, &pk_proof.pk_gen_row_check_pf) {
            return false;
        }

        return true;
    }

    pub fn ternary_pk_rlk_proof(
        &mut self,
        pk_rlk_proof: &TenaryPublicRelinKeyProof,
        pk: &bfv::PublicKey,
        rlk: &bfv::RelinKey,
    ) -> bool {
        let level = self.params.bfv.gadget.len();

        if !self.lin_check(&pk_rlk_proof.ntt_linear_check_pf) {
            return false;
        }

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c_1 = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };
        if !self.row_check(&norm_row_check_c_1, &pk_rlk_proof.sk_norm_row_check_pf) {
            return false;
        }
        if !self.row_check(&norm_row_check_c_1, &pk_rlk_proof.epk_norm_row_check_pf) {
            return false;
        }

        for i in 0..3 {
            for j in 0..level {
                if !self.row_check(
                    &norm_row_check_c_1,
                    &pk_rlk_proof.erlk_norm_row_check_pf[i][j],
                ) {
                    return false;
                }
            }
        }

        if !self.row_check(&norm_row_check_c_1, &pk_rlk_proof.frlk_norm_row_check_pf) {
            return false;
        }

        let p_ecd = self.encoder.encode(&pk.p_ntt);
        let u_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        let gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.generalized_row_check(&gen_row_check_c, &pk_rlk_proof.pk_gen_row_check_pf) {
            return false;
        }

        for i in 0..level {
            let u0_ecd = self.encoder.encode(&rlk.u_ntt[0][i]);
            let u1_ecd = self.encoder.encode(&rlk.u_ntt[1][i]);

            let r0_ecd = self.encoder.encode(&rlk.r_ntt[0][i]);
            let r1_ecd = self.encoder.encode(&rlk.r_ntt[1][i]);
            let r2_ecd = self.encoder.encode(&rlk.r_ntt[2][i]);

            let gi = vec![self.params.bfv.gadget[i].clone(); self.params.bfv.n];
            let gi_ecd = self.encoder.encode(&gi);

            let neg_gi = vec![
                self.params.bfv.q.clone() - self.params.bfv.gadget[i].clone();
                self.params.bfv.n
            ];
            let neg_gi_ecd = self.encoder.encode(&neg_gi);

            let rlk_gen_row_check_c_1 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ecd, vec![0, 0]),
                    (u0_ecd.clone(), vec![1, 0]),
                    (neg_one_ecd.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_2 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ecd, vec![0, 0, 0]),
                    (u0_ecd, vec![1, 0, 0]),
                    (neg_gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_3 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ecd, vec![0, 0, 0]),
                    (u1_ecd, vec![1, 0, 0]),
                    (gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            if !self.generalized_row_check(
                &rlk_gen_row_check_c_1,
                &pk_rlk_proof.rlk_gen_row_check_pf_1[i],
            ) {
                return false;
            }
            if !self.generalized_row_check(
                &rlk_gen_row_check_c_2,
                &pk_rlk_proof.rlk_gen_row_check_pf_2[i],
            ) {
                return false;
            }
            if !self.generalized_row_check(
                &rlk_gen_row_check_c_3,
                &pk_rlk_proof.rlk_gen_row_check_pf_3[i],
            ) {
                return false;
            }
        }

        return true;
    }

    pub fn ternary_pk_rlk_atk_proof(
        &mut self,
        pk_rlk_atk_proof: &TenaryPublicRelinAutKeyProof,
        pk: &bfv::PublicKey,
        rlk: &bfv::RelinKey,
        atks: &[&bfv::AutomorphismKey],
    ) -> bool {
        let level = self.params.bfv.gadget.len();
        let auts = atks.len();

        if !self.lin_check(&pk_rlk_atk_proof.ntt_linear_check_pf) {
            return false;
        }
        for i in 0..auts {
            if !self.lin_check(&pk_rlk_atk_proof.aut_linear_check_pf[i]) {
                return false;
            }
        }

        let neg_one = self.params.bfv.q.clone() - Integer::from(1);
        let norm_row_check_c_1 = BigMultiVariatePoly {
            coeffs: vec![(neg_one.clone(), vec![1]), (Integer::from(1), vec![3])],
            max_degree: 3,
        };
        if !self.row_check(&norm_row_check_c_1, &pk_rlk_atk_proof.sk_norm_row_check_pf) {
            return false;
        }
        if !self.row_check(&norm_row_check_c_1, &pk_rlk_atk_proof.epk_norm_row_check_pf) {
            return false;
        }

        for i in 0..3 {
            for j in 0..level {
                if !self.row_check(
                    &norm_row_check_c_1,
                    &pk_rlk_atk_proof.erlk_norm_row_check_pf[i][j],
                ) {
                    return false;
                }
            }
        }

        if !self.row_check(
            &norm_row_check_c_1,
            &pk_rlk_atk_proof.frlk_norm_row_check_pf,
        ) {
            return false;
        }

        for i in 0..auts {
            if !self.row_check(
                &norm_row_check_c_1,
                &pk_rlk_atk_proof.eatk_norm_row_check_pf[i],
            ) {
                return false;
            }
        }

        let p_ecd = self.encoder.encode(&pk.p_ntt);
        let u_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self.encoder.encode(&vec![neg_one; self.params.bfv.n]);

        let gen_row_check_c = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ecd, vec![0, 0]),
                (u_ecd, vec![1, 0]),
                (neg_one_ecd.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.generalized_row_check(&gen_row_check_c, &pk_rlk_atk_proof.pk_gen_row_check_pf) {
            return false;
        }

        for i in 0..level {
            let u0_ecd = self.encoder.encode(&rlk.u_ntt[0][i]);
            let u1_ecd = self.encoder.encode(&rlk.u_ntt[1][i]);

            let r0_ecd = self.encoder.encode(&rlk.r_ntt[0][i]);
            let r1_ecd = self.encoder.encode(&rlk.r_ntt[1][i]);
            let r2_ecd = self.encoder.encode(&rlk.r_ntt[2][i]);

            let gi = vec![self.params.bfv.gadget[i].clone(); self.params.bfv.n];
            let gi_ecd = self.encoder.encode(&gi);

            let neg_gi = vec![
                self.params.bfv.q.clone() - self.params.bfv.gadget[i].clone();
                self.params.bfv.n
            ];
            let neg_gi_ecd = self.encoder.encode(&neg_gi);

            let rlk_gen_row_check_c_1 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ecd, vec![0, 0]),
                    (u0_ecd.clone(), vec![1, 0]),
                    (neg_one_ecd.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_2 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ecd, vec![0, 0, 0]),
                    (u0_ecd, vec![1, 0, 0]),
                    (neg_gi_ecd.clone(), vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            let rlk_gen_row_check_c_3 = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ecd, vec![0, 0, 0]),
                    (u1_ecd, vec![1, 0, 0]),
                    (gi_ecd, vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };

            if !self.generalized_row_check(
                &rlk_gen_row_check_c_1,
                &pk_rlk_atk_proof.rlk_gen_row_check_pf_1[i],
            ) {
                return false;
            }
            if !self.generalized_row_check(
                &rlk_gen_row_check_c_2,
                &pk_rlk_atk_proof.rlk_gen_row_check_pf_2[i],
            ) {
                return false;
            }
            if !self.generalized_row_check(
                &rlk_gen_row_check_c_3,
                &pk_rlk_atk_proof.rlk_gen_row_check_pf_3[i],
            ) {
                return false;
            }

            for j in 0..auts {
                let a_ecd = self.encoder.encode(&atks[j].a_ntt[i]);
                let u_ecd = self.encoder.encode(&atks[j].u_ntt[i]);

                let atk_gen_row_check_c = PolyMultiVariatePoly {
                    coeffs: vec![
                        (a_ecd, vec![0, 0, 0]),
                        (u_ecd, vec![1, 0, 0]),
                        (neg_gi_ecd.clone(), vec![0, 1, 0]),
                        (neg_one_ecd.clone(), vec![0, 0, 1]),
                    ],
                    max_degree: 1,
                };

                if !self.generalized_row_check(
                    &atk_gen_row_check_c,
                    &pk_rlk_atk_proof.atk_gen_row_check_pf[j][i],
                ) {
                    return false;
                }
            }
        }

        return true;
    }
}

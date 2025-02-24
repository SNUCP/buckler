use super::*;
use crate::csprng::Oracle;
use crate::rlwe;
use crate::{celpc, utils::signed_decompose};
use rug::ops::NegAssign;
use rug::{Assign, Complete, Integer};

pub struct Prover<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_prover: celpc::PolynomialProver<'a>,

    pub oracle: Oracle,

    pub ringq: BigRing,
    pub neg_transformer: rlwe::NegacyclicTransformer,
}

impl<'a> Prover<'a> {
    pub fn new(params: &'a Parameters, ck: &'a celpc::CommitKey) -> Self {
        let encoder = Encoder::new(params);

        Prover {
            params: params,
            encoder: encoder,

            celpc_prover: celpc::PolynomialProver::new(&params.pcs, ck),
            oracle: Oracle::new(),

            ringq: BigRing::new(params.embedding_n, &params.rlwe.q),
            neg_transformer: rlwe::NegacyclicTransformer::new(params.rlwe.n, &params.rlwe.q),
        }
    }

    pub fn row_check_oracle(
        &mut self,
        a_ntt: &[&BigPoly],
        c: &BigMultiVariatePoly,
    ) -> RowCheckOracle {
        let mut c_a = self.ringq.evaluate_multivariate_poly(c, a_ntt);
        self.ringq.intt_inplace(&mut c_a);

        let quo_degree = c.max_degree * 2 * self.params.rlwe.n;
        let (quo, _) = self.ringq.quo_rem_zero(&c_a, self.params.rlwe.n);
        let quo_oracle = self.celpc_prover.gen_poly_oracle(&quo.coeffs[..quo_degree]);

        return RowCheckOracle { quo_oracle };
    }

    pub fn row_check_eval(
        &mut self,
        alpha: &Integer,
        rc_oracle: &RowCheckOracle,
    ) -> RowCheckEvalProof {
        let quo_eval_proof = self
            .celpc_prover
            .evaluate(alpha, &rc_oracle.quo_oracle.commitment);
        return RowCheckEvalProof {
            quo_eval_pf: quo_eval_proof,
        };
    }
    pub fn gen_row_check_oracle(
        &mut self,
        a_ntt: &[&BigPoly],
        c_ntt: &PolyMultiVariatePoly,
    ) -> GenRowCheckOracle {
        let mut c_a = self.ringq.evaluate_poly_multivariate_poly(c_ntt, a_ntt);
        self.ringq.intt_inplace(&mut c_a);

        let quo_degree = c_ntt.max_degree * 2 * self.params.rlwe.n;
        let (quo, _) = self.ringq.quo_rem_zero(&c_a, self.params.rlwe.n);
        let quo_oracle = self.celpc_prover.gen_poly_oracle(&quo.coeffs[..quo_degree]);

        return GenRowCheckOracle { quo_oracle };
    }

    pub fn gen_row_check_eval(
        &mut self,
        alpha: &Integer,
        grc_oracle: &GenRowCheckOracle,
    ) -> GenRowCheckEvalProof {
        let quo_eval_proof = self
            .celpc_prover
            .evaluate(alpha, &grc_oracle.quo_oracle.commitment);
        return GenRowCheckEvalProof {
            quo_eval_pf: quo_eval_proof,
        };
    }

    pub fn lin_check_oracle(
        &mut self,
        a_ntt: &[&BigPoly],
        b_ntt: &[&BigPoly],
        lin_type: LinCheckType,
    ) -> (LinCheckPoly, LinCheckOracle) {
        let g_degree = 3 * self.params.rlwe.n;
        let mut g = self.ringq.new_poly();
        for i in 0..self.params.rlwe.n {
            g.coeffs[i] = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.rlwe.q);
        }
        let mu = g.coeffs[0].clone();
        for i in 0..g_degree - self.params.rlwe.n {
            let c = self
                .encoder
                .uniform_sampler
                .sample_range_bigint(&self.params.rlwe.q);

            // Add c * X^i * (X^N - 1)
            g.coeffs[i] -= &c;
            if g.coeffs[i].is_negative() {
                g.coeffs[i] += &self.params.rlwe.q;
            }

            g.coeffs[i + self.params.rlwe.n] += &c;
            if g.coeffs[i + self.params.rlwe.n] >= self.params.rlwe.q {
                g.coeffs[i + self.params.rlwe.n] -= &self.params.rlwe.q;
            }
        }

        let g_oracle = self.celpc_prover.gen_poly_oracle(&g.coeffs[..g_degree]);

        self.oracle.write_polynomial_oracle(&g_oracle);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let v_big = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let mut v = vec![Integer::from(1); self.params.rlwe.n];
        for i in 1..v.len() {
            v[i] = v[i - 1].clone() * &v_big;
            v[i].modulo_mut(&self.params.rlwe.q);
        }

        let mut w;
        match lin_type {
            LinCheckType::NTT => {
                w = v.clone();
                w.reverse();
                self.neg_transformer.intt_without_normalize(&mut w);
            }
            LinCheckType::Automorphism(d) => {
                let d_inv = modinverse::modinverse(d, 2 * &self.params.rlwe.n).unwrap();
                w = self.neg_transformer.automorphism(&v, d_inv);
            }
        }

        let mut v_ecd = self.encoder.encode(&v);
        let mut w_ecd = self.encoder.encode(&w);
        self.ringq.ntt_inplace(&mut v_ecd);
        self.ringq.ntt_inplace(&mut w_ecd);

        let mut check = self.ringq.new_ntt_poly();
        let mut aw = self.ringq.new_ntt_poly();
        let mut bv = self.ringq.new_ntt_poly();
        let mut beta_pow = beta.clone();
        for i in 0..a_ntt.len() {
            self.ringq.mul_assign(&a_ntt[i], &w_ecd, &mut aw);
            self.ringq.mul_assign(&b_ntt[i], &v_ecd, &mut bv);
            self.ringq.sub_inplace(&bv, &mut aw);
            self.ringq.mul_const_inplace(&beta_pow, &mut aw);
            self.ringq.add_inplace(&aw, &mut check);

            beta_pow *= &beta;
            beta_pow.modulo_mut(&self.params.rlwe.q);
        }
        self.ringq.intt_inplace(&mut check);
        self.ringq.add_inplace(&g, &mut check);

        let (quo_degree, rem_degree) = (2 * self.params.rlwe.n, self.params.rlwe.n);
        let (quo, mut rem) = self.ringq.quo_rem_zero(&check, self.params.rlwe.n);
        rem.coeffs[0] = Integer::ZERO;
        let quo_rem_oracle = self
            .celpc_prover
            .gen_batch_poly_oracle(&[&quo.coeffs[..quo_degree], &rem.coeffs[..rem_degree]]);

        return (
            LinCheckPoly { g, quo, rem },
            LinCheckOracle {
                lin_type,
                g_oracle,
                mu,
                quo_rem_oracle,
            },
        );
    }

    pub fn norm_check_oracle(
        &mut self,
        a_dcd: &[Integer],
        a_ntt: &BigPoly,
        log_bound: usize,
    ) -> (Vec<BigPoly>, NormCheckOracle) {
        let mut decomposed = vec![vec![Integer::ZERO; self.params.rlwe.n]; log_bound + 1];
        for i in 0..self.params.rlwe.n {
            let coeffs_decomposed = signed_decompose(&a_dcd[i], log_bound);
            for j in 0..log_bound + 1 {
                decomposed[j][i].assign(&coeffs_decomposed[j]);
            }
        }

        let mut decomposed_ecd = Vec::with_capacity(log_bound + 1);
        let mut decomposed_ecd_ntt = Vec::with_capacity(log_bound + 1);
        for i in 0..log_bound + 1 {
            decomposed_ecd.push(self.encoder.encode(&decomposed[i]));
            decomposed_ecd_ntt.push(self.ringq.ntt(&decomposed_ecd[i]));
        }
        let mut decomposed_ref = Vec::with_capacity(decomposed.len());
        for i in 0..decomposed.len() {
            decomposed_ref.push(&decomposed_ecd[i].coeffs[..]);
        }

        let decomposed_oracle = self.celpc_prover.gen_batch_poly_oracle(&decomposed_ref);

        let norm_check_circuit_dcmp = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };

        let mut rc_oracle = Vec::with_capacity(log_bound + 2);
        for i in 0..log_bound + 1 {
            rc_oracle
                .push(self.row_check_oracle(&[&decomposed_ecd_ntt[i]], &norm_check_circuit_dcmp));
        }

        let mut norm_check_circuit = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(log_bound + 2),
            max_degree: 1,
        };
        let mut deg = vec![0; log_bound + 2];
        deg[0] = 1;
        norm_check_circuit
            .coeffs
            .push((Integer::from(1), deg.clone()));

        deg.fill(0);
        deg[1] = 1;
        norm_check_circuit
            .coeffs
            .push((Integer::from(-1), deg.clone()));
        for i in 2..log_bound + 2 {
            deg.fill(0);
            deg[i] = 1;
            norm_check_circuit
                .coeffs
                .push((Integer::from(-(1i64 << (i - 2))), deg.clone()));
        }

        let mut norm_check_input = Vec::with_capacity(log_bound + 2);
        norm_check_input.push(a_ntt);
        for i in 0..log_bound + 1 {
            norm_check_input.push(&decomposed_ecd_ntt[i]);
        }

        rc_oracle.push(self.row_check_oracle(&norm_check_input, &norm_check_circuit));

        return (
            decomposed_ecd,
            NormCheckOracle {
                decomposed_oracle,
                rc_oracle,
                log_bound,
            },
        );
    }

    pub fn norm_check_eval(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        decomposed_ecd: &[BigPoly],
        nm_oracle: &NormCheckOracle,
    ) -> NormCheckEvalProof {
        let mut rc_eval_proof = Vec::with_capacity(nm_oracle.rc_oracle.len());
        for i in 0..nm_oracle.rc_oracle.len() {
            rc_eval_proof.push(self.row_check_eval(alpha, &nm_oracle.rc_oracle[i]));
        }

        let mut decomposed_eval = Vec::with_capacity(decomposed_ecd.len());
        for i in 0..decomposed_ecd.len() {
            decomposed_eval.push(self.ringq.evaluate(&decomposed_ecd[i], alpha));
        }

        let decomposed_eval_proof = self.celpc_prover.evaluate_batch(
            alpha,
            alpha_combine,
            &decomposed_eval,
            &nm_oracle.decomposed_oracle.commitment,
        );

        return NormCheckEvalProof {
            decomposed_eval_pf: decomposed_eval_proof,
            rc_eval_pf: rc_eval_proof,
        };
    }

    pub fn lin_check_eval(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        lc_poly: &LinCheckPoly,
        lc_oracle: &LinCheckOracle,
    ) -> LinCheckEvalProof {
        let quo_eval = self.ringq.evaluate(&lc_poly.quo, &alpha);
        let rem_eval = self.ringq.evaluate(&lc_poly.rem, &alpha);

        let mut z = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        z -= Integer::ONE;

        let g_eval_proof = self
            .celpc_prover
            .evaluate(alpha, &lc_oracle.g_oracle.commitment);

        let quo_rem_eval_proof = self.celpc_prover.evaluate_batch(
            alpha,
            alpha_combine,
            &[quo_eval, rem_eval],
            &lc_oracle.quo_rem_oracle.commitment,
        );

        return LinCheckEvalProof {
            g_eval_pf: g_eval_proof,
            quo_rem_eval_pf: quo_rem_eval_proof,
        };
    }

    pub fn prove_pkenc(&mut self, pk: &rlwe::PublicKey, ct: &rlwe::PkCiphertext) -> PkEncProof {
        let e0_coeffs_ecd = self.encoder.encode_randomize(&ct.e0_coeffs);
        let e0_ntt_ecd = self.encoder.encode_randomize(&ct.e0_ntt);
        let e1_coeffs_ecd = self.encoder.encode_randomize(&ct.e1_coeffs);
        let e1_ntt_ecd = self.encoder.encode_randomize(&ct.e1_ntt);
        let f_coeffs_ecd = self.encoder.encode_randomize(&ct.f_coeffs);
        let f_ntt_ecd = self.encoder.encode_randomize(&ct.f_ntt);
        let m_coeffs_ecd = self.encoder.encode_randomize(&ct.m_coeffs);
        let m_ntt_ecd = self.encoder.encode_randomize(&ct.m_ntt);

        let e0_coeffs_ecd_ntt = self.ringq.ntt(&e0_coeffs_ecd);
        let e0_ntt_ecd_ntt = self.ringq.ntt(&e0_ntt_ecd);
        let e1_coeffs_ecd_ntt = self.ringq.ntt(&e1_coeffs_ecd);
        let e1_ntt_ecd_ntt = self.ringq.ntt(&e1_ntt_ecd);
        let f_coeffs_ecd_ntt = self.ringq.ntt(&f_coeffs_ecd);
        let f_ntt_ecd_ntt = self.ringq.ntt(&f_ntt_ecd);
        let m_coeffs_ecd_ntt = self.ringq.ntt(&m_coeffs_ecd);
        let m_ntt_ecd_ntt = self.ringq.ntt(&m_ntt_ecd);

        let pkenc_oracle = self.celpc_prover.gen_batch_poly_oracle(&[
            &e0_coeffs_ecd.coeffs[..],
            &e0_ntt_ecd.coeffs[..],
            &e1_coeffs_ecd.coeffs[..],
            &e1_ntt_ecd.coeffs[..],
            &f_coeffs_ecd.coeffs[..],
            &f_ntt_ecd.coeffs[..],
            &m_coeffs_ecd.coeffs[..],
            &m_ntt_ecd.coeffs[..],
        ]);

        let (ntt_poly, ntt_oracle) = self.lin_check_oracle(
            &[
                &e0_coeffs_ecd_ntt,
                &e1_coeffs_ecd_ntt,
                &f_coeffs_ecd_ntt,
                &m_coeffs_ecd_ntt,
            ],
            &[
                &e0_ntt_ecd_ntt,
                &e1_ntt_ecd_ntt,
                &f_ntt_ecd_ntt,
                &m_ntt_ecd_ntt,
            ],
            LinCheckType::NTT,
        );

        let c_ntt_ecd = self.encoder.encode(&ct.c_ntt);
        let u_ntt_ecd = self.encoder.encode(&ct.u_ntt);
        let p_ntt_ecd = self.encoder.encode(&pk.p_ntt);
        let upk_ntt_ecd = self.encoder.encode(&pk.u_ntt);

        let c_ntt_ecd_ntt = self.ringq.ntt(&c_ntt_ecd);
        let mut neg_p_ntt_ecd = p_ntt_ecd.clone();
        for i in 0..self.encoder.embedding_n {
            neg_p_ntt_ecd.coeffs[i].neg_assign();
        }
        let neg_p_ntt_ecd_ntt = self.ringq.ntt(&neg_p_ntt_ecd);
        let mut neg_one_ecd_ntt = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_one_ecd_ntt);
        let mut neg_delta_ecd_ntt = self
            .encoder
            .encode(&vec![-self.params.rlwe.delta.clone(); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_delta_ecd_ntt);

        // c = pf + Delta m + e0
        let c_circuit_ntt = PolyMultiVariatePoly {
            coeffs: vec![
                (c_ntt_ecd_ntt, vec![0, 0, 0]),
                (neg_p_ntt_ecd_ntt, vec![1, 0, 0]),
                (neg_delta_ecd_ntt, vec![0, 1, 0]),
                (neg_one_ecd_ntt.clone(), vec![0, 0, 1]),
            ],
            max_degree: 1,
        };

        let c0_grc_oracle = self.gen_row_check_oracle(
            &[&f_ntt_ecd_ntt, &m_ntt_ecd_ntt, &e0_ntt_ecd_ntt],
            &c_circuit_ntt,
        );

        let u_ntt_ecd_ntt = self.ringq.ntt(&u_ntt_ecd);
        let mut neg_upk_ntt_ecd = upk_ntt_ecd.clone();
        for i in 0..self.encoder.embedding_n {
            neg_upk_ntt_ecd.coeffs[i].neg_assign();
        }
        let neg_upk_ntt_ecd_ntt = self.ringq.ntt(&neg_upk_ntt_ecd);

        // u = upk*f + e1
        let u_circuit_ntt = PolyMultiVariatePoly {
            coeffs: vec![
                (u_ntt_ecd_ntt, vec![0, 0]),
                (neg_upk_ntt_ecd_ntt, vec![1, 0]),
                (neg_one_ecd_ntt, vec![0, 1]),
            ],
            max_degree: 1,
        };

        let c1_grc_oracle =
            self.gen_row_check_oracle(&[&f_ntt_ecd_ntt, &e1_ntt_ecd_ntt], &u_circuit_ntt);

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };

        let e0_norm_oracle = self.row_check_oracle(&[&e0_coeffs_ecd_ntt], &ternary_check_circuit);
        let e1_norm_oracle = self.row_check_oracle(&[&e1_coeffs_ecd_ntt], &ternary_check_circuit);
        let f_norm_oracle = self.row_check_oracle(&[&f_coeffs_ecd_ntt], &ternary_check_circuit);

        let (m_norm_poly, m_norm_oracle) =
            self.norm_check_oracle(&ct.m_coeffs, &m_coeffs_ecd_ntt, 16);

        self.oracle.write_batch_polynomial_oracle(&pkenc_oracle);
        self.oracle.write_lincheck_oracle(&ntt_oracle);
        self.oracle.write_genrowcheck_oracle(&c0_grc_oracle);
        self.oracle.write_genrowcheck_oracle(&c1_grc_oracle);
        self.oracle.write_rowcheck_oracle(&e0_norm_oracle);
        self.oracle.write_rowcheck_oracle(&e1_norm_oracle);
        self.oracle.write_rowcheck_oracle(&f_norm_oracle);
        self.oracle.write_normcheck_oracle(&m_norm_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let e0_coeffs_ecd_eval = self.ringq.evaluate(&e0_coeffs_ecd, &alpha);
        let e0_ntt_ecd_eval = self.ringq.evaluate(&e0_ntt_ecd, &alpha);
        let e1_coeffs_ecd_eval = self.ringq.evaluate(&e1_coeffs_ecd, &alpha);
        let e1_ntt_ecd_eval = self.ringq.evaluate(&e1_ntt_ecd, &alpha);
        let f_coeffs_ecd_eval = self.ringq.evaluate(&f_coeffs_ecd, &alpha);
        let f_ntt_ecd_eval = self.ringq.evaluate(&f_ntt_ecd, &alpha);
        let m_coeffs_ecd_eval = self.ringq.evaluate(&m_coeffs_ecd, &alpha);
        let m_ntt_ecd_eval = self.ringq.evaluate(&m_ntt_ecd, &alpha);

        let pkenc_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &[
                e0_coeffs_ecd_eval,
                e0_ntt_ecd_eval,
                e1_coeffs_ecd_eval,
                e1_ntt_ecd_eval,
                f_coeffs_ecd_eval,
                f_ntt_ecd_eval,
                m_coeffs_ecd_eval,
                m_ntt_ecd_eval,
            ],
            &pkenc_oracle.commitment,
        );

        let ntt_eval_pf = self.lin_check_eval(&alpha, &alpha_combine, &ntt_poly, &ntt_oracle);
        let c0_grc_eval_pf = self.gen_row_check_eval(&alpha, &c0_grc_oracle);
        let c1_grc_eval_pf = self.gen_row_check_eval(&alpha, &c1_grc_oracle);

        let e0_norm_eval_pf = self.row_check_eval(&alpha, &e0_norm_oracle);
        let e1_norm_eval_pf = self.row_check_eval(&alpha, &e1_norm_oracle);
        let f_norm_eval_pf = self.row_check_eval(&alpha, &f_norm_oracle);
        let m_norm_eval_pf =
            self.norm_check_eval(&alpha, &alpha_combine, &m_norm_poly, &m_norm_oracle);

        return PkEncProof {
            pkenc_oracle,
            pkenc_eval_pf,

            ntt_oracle,
            ntt_eval_pf,

            c0_grc_oracle,
            c0_grc_eval_pf,
            c1_grc_oracle,
            c1_grc_eval_pf,

            e0_norm_oracle,
            e0_norm_eval_pf,
            e1_norm_oracle,
            e1_norm_eval_pf,
            f_norm_oracle,
            f_norm_eval_pf,
            m_norm_oracle,
            m_norm_eval_pf,
        };
    }

    pub fn prove_ddec(
        &mut self,
        sk: &rlwe::SecretKey,
        pk: &rlwe::PublicKey,
        ct: &rlwe::PkCiphertext,
        pd: &rlwe::PartialDec,
    ) -> DDecProof {
        let bdd: Integer = Integer::from(1) << 128;
        let mut ef_ntt = vec![Integer::ZERO; self.params.rlwe.n];
        for i in 0..self.params.rlwe.n {
            ef_ntt[i].assign(&pd.u_ntt[i]);
            ef_ntt[i] *= &pd.f_ntt[i];
            ef_ntt[i] += &pd.e_ntt[i];
            ef_ntt[i].modulo_mut(&self.params.rlwe.q);
        }
        let mut ef_coeffs = ef_ntt.clone();
        self.neg_transformer.intt(&mut ef_coeffs);

        let q_half = self.params.rlwe.q.clone() >> 1;
        let mut ef_coeffs_bdd = vec![Integer::ZERO; self.params.rlwe.n];
        for i in 0..self.params.rlwe.n {
            if &ef_coeffs[i] > &q_half {
                ef_coeffs[i] -= &self.params.rlwe.q;
            }
            ef_coeffs_bdd[i] = ef_coeffs[i].clone() % &bdd;
        }

        let mut k_coeffs = vec![Integer::ZERO; self.params.rlwe.n];
        for i in 0..self.params.rlwe.n {
            k_coeffs[i] = ef_coeffs[i].clone() - ef_coeffs_bdd[i].clone();
            k_coeffs[i] /= &bdd;
        }
        let mut k_ntt = k_coeffs.clone();
        self.neg_transformer.ntt(&mut k_ntt);

        let s_coeffs_ecd = self.encoder.encode_randomize(&sk.coeffs);
        let s_ntt_ecd = self.encoder.encode_randomize(&sk.ntt);
        let epk_coeffs_ecd = self.encoder.encode_randomize(&pk.epk_coeffs);
        let epk_ntt_ecd = self.encoder.encode_randomize(&pk.epk_ntt);
        let edd_coeffs_ecd = self.encoder.encode_randomize(&pd.e_coeffs);
        let edd_ntt_ecd = self.encoder.encode_randomize(&pd.e_ntt);
        let fdd_coeffs_ecd = self.encoder.encode_randomize(&pd.f_coeffs);
        let fdd_ntt_ecd = self.encoder.encode_randomize(&pd.f_ntt);
        let k_coeffs_ecd = self.encoder.encode_randomize(&k_coeffs);
        let k_ntt_ecd = self.encoder.encode_randomize(&k_ntt);

        let s_coeffs_ecd_ntt = self.ringq.ntt(&s_coeffs_ecd);
        let s_ntt_ecd_ntt = self.ringq.ntt(&s_ntt_ecd);
        let epk_coeffs_ecd_ntt = self.ringq.ntt(&epk_coeffs_ecd);
        let epk_ntt_ecd_ntt = self.ringq.ntt(&epk_ntt_ecd);
        let edd_coeffs_ecd_ntt = self.ringq.ntt(&edd_coeffs_ecd);
        let edd_ntt_ecd_ntt = self.ringq.ntt(&edd_ntt_ecd);
        let fdd_coeffs_ecd_ntt = self.ringq.ntt(&fdd_coeffs_ecd);
        let fdd_ntt_ecd_ntt = self.ringq.ntt(&fdd_ntt_ecd);
        let k_coeffs_ecd_ntt = self.ringq.ntt(&k_coeffs_ecd);
        let k_ntt_ecd_ntt = self.ringq.ntt(&k_ntt_ecd);

        let ddec_oracle_coeffs = vec![
            &s_coeffs_ecd.coeffs[..],
            &s_ntt_ecd.coeffs[..],
            &epk_coeffs_ecd.coeffs[..],
            &epk_ntt_ecd.coeffs[..],
            &edd_coeffs_ecd.coeffs[..],
            &edd_ntt_ecd.coeffs[..],
            &fdd_coeffs_ecd.coeffs[..],
            &fdd_ntt_ecd.coeffs[..],
            &k_coeffs_ecd.coeffs[..],
            &k_ntt_ecd.coeffs[..],
        ];

        let ddec_oracle = self.celpc_prover.gen_batch_poly_oracle(&ddec_oracle_coeffs);

        let ntt_oracle_coeffs = vec![
            &s_coeffs_ecd_ntt,
            &epk_coeffs_ecd_ntt,
            &edd_coeffs_ecd_ntt,
            &fdd_coeffs_ecd_ntt,
            &k_coeffs_ecd_ntt,
        ];
        let ntt_oracle_ntt = vec![
            &s_ntt_ecd_ntt,
            &epk_ntt_ecd_ntt,
            &edd_ntt_ecd_ntt,
            &fdd_ntt_ecd_ntt,
            &k_ntt_ecd_ntt,
        ];
        let (ntt_poly, ntt_oracle) =
            self.lin_check_oracle(&ntt_oracle_coeffs, &ntt_oracle_ntt, LinCheckType::NTT);

        let mut p_ntt_ecd_ntt = self.encoder.encode(&pk.p_ntt);
        self.ringq.ntt_inplace(&mut p_ntt_ecd_ntt);
        let mut upk_ntt_ecd_ntt = self.encoder.encode(&pk.u_ntt);
        self.ringq.ntt_inplace(&mut upk_ntt_ecd_ntt);
        let mut neg_one_ecd_ntt = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_one_ecd_ntt);

        let pk_circuit_ntt = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd_ntt, vec![0, 0]),
                (upk_ntt_ecd_ntt, vec![1, 0]),
                (neg_one_ecd_ntt.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };
        let pk_grc_oracle =
            self.gen_row_check_oracle(&[&s_ntt_ecd_ntt, &epk_ntt_ecd_ntt], &pk_circuit_ntt);

        let mut d_ntt_ecd_ntt = self.encoder.encode(&pd.d_ntt);
        self.ringq.ntt_inplace(&mut d_ntt_ecd_ntt);

        let mut neg_c_ntt_ecd_ntt = self.encoder.encode(&ct.c_ntt);
        let mut neg_udd_ntt_ecd_ntt = self.encoder.encode(&pd.u_ntt);
        for i in 0..self.encoder.embedding_n {
            neg_c_ntt_ecd_ntt.coeffs[i].neg_assign();
            neg_udd_ntt_ecd_ntt.coeffs[i].neg_assign();
        }
        self.ringq.ntt_inplace(&mut neg_c_ntt_ecd_ntt);
        self.ringq.ntt_inplace(&mut neg_udd_ntt_ecd_ntt);

        let mut bdd_ecd_ntt = self.encoder.encode(&vec![bdd.clone(); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut bdd_ecd_ntt);

        let dd_circuit_ntt = PolyMultiVariatePoly {
            coeffs: vec![
                (d_ntt_ecd_ntt, vec![0, 0, 0, 0]),
                (neg_c_ntt_ecd_ntt, vec![1, 0, 0, 0]),
                (neg_udd_ntt_ecd_ntt, vec![0, 1, 0, 0]),
                (neg_one_ecd_ntt, vec![0, 0, 1, 0]),
                (bdd_ecd_ntt, vec![0, 0, 0, 1]),
            ],
            max_degree: 1,
        };
        let dd_grc_oracle = self.gen_row_check_oracle(
            &[
                &s_ntt_ecd_ntt,
                &fdd_ntt_ecd_ntt,
                &edd_ntt_ecd_ntt,
                &k_ntt_ecd_ntt,
            ],
            &dd_circuit_ntt,
        );

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        let s_norm_oracle = self.row_check_oracle(&[&s_coeffs_ecd_ntt], &ternary_check_circuit);
        let epk_norm_oracle = self.row_check_oracle(&[&epk_coeffs_ecd_ntt], &ternary_check_circuit);
        let edd_norm_oracle = self.row_check_oracle(&[&edd_coeffs_ecd_ntt], &ternary_check_circuit);
        let fdd_norm_oracle = self.row_check_oracle(&[&fdd_coeffs_ecd_ntt], &ternary_check_circuit);
        let (k_norm_poly, k_norm_oracle) = self.norm_check_oracle(
            &k_coeffs,
            &k_coeffs_ecd_ntt,
            self.params.rlwe.n.ilog2() as usize,
        );

        self.oracle.write_batch_polynomial_oracle(&ddec_oracle);
        self.oracle.write_lincheck_oracle(&ntt_oracle);
        self.oracle.write_genrowcheck_oracle(&pk_grc_oracle);
        self.oracle.write_genrowcheck_oracle(&dd_grc_oracle);
        self.oracle.write_rowcheck_oracle(&s_norm_oracle);
        self.oracle.write_rowcheck_oracle(&epk_norm_oracle);
        self.oracle.write_rowcheck_oracle(&edd_norm_oracle);
        self.oracle.write_rowcheck_oracle(&fdd_norm_oracle);
        self.oracle.write_normcheck_oracle(&k_norm_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let s_coeffs_ecd_eval = self.ringq.evaluate(&s_coeffs_ecd, &alpha);
        let s_ntt_ecd_eval = self.ringq.evaluate(&s_ntt_ecd, &alpha);
        let epk_coeffs_ecd_eval = self.ringq.evaluate(&epk_coeffs_ecd, &alpha);
        let epk_ntt_ecd_eval = self.ringq.evaluate(&epk_ntt_ecd, &alpha);
        let edd_coeffs_ecd_eval = self.ringq.evaluate(&edd_coeffs_ecd, &alpha);
        let edd_ntt_ecd_eval = self.ringq.evaluate(&edd_ntt_ecd, &alpha);
        let fdd_coeffs_ecd_eval = self.ringq.evaluate(&fdd_coeffs_ecd, &alpha);
        let fdd_ntt_ecd_eval = self.ringq.evaluate(&fdd_ntt_ecd, &alpha);
        let k_coeffs_ecd_eval = self.ringq.evaluate(&k_coeffs_ecd, &alpha);
        let k_ntt_ecd_eval = self.ringq.evaluate(&k_ntt_ecd, &alpha);

        let ddec_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &[
                s_coeffs_ecd_eval,
                s_ntt_ecd_eval,
                epk_coeffs_ecd_eval,
                epk_ntt_ecd_eval,
                edd_coeffs_ecd_eval,
                edd_ntt_ecd_eval,
                fdd_coeffs_ecd_eval,
                fdd_ntt_ecd_eval,
                k_coeffs_ecd_eval,
                k_ntt_ecd_eval,
            ],
            &ddec_oracle.commitment,
        );

        let ntt_eval_pf = self.lin_check_eval(&alpha, &alpha_combine, &ntt_poly, &ntt_oracle);
        let pk_grc_eval_pf = self.gen_row_check_eval(&alpha, &pk_grc_oracle);
        let dd_grc_eval_pf = self.gen_row_check_eval(&alpha, &dd_grc_oracle);

        let s_norm_eval_pf = self.row_check_eval(&alpha, &s_norm_oracle);
        let epk_norm_eval_pf = self.row_check_eval(&alpha, &epk_norm_oracle);
        let edd_norm_eval_pf = self.row_check_eval(&alpha, &edd_norm_oracle);
        let fdd_norm_eval_pf = self.row_check_eval(&alpha, &fdd_norm_oracle);
        let k_norm_eval_pf =
            self.norm_check_eval(&alpha, &alpha_combine, &k_norm_poly, &k_norm_oracle);

        return DDecProof {
            ddec_oracle,
            ddec_eval_pf,

            ntt_oracle,
            ntt_eval_pf,

            pk_grc_oracle,
            pk_grc_eval_pf,
            dd_grc_oracle,
            dd_grc_eval_pf,

            s_norm_oracle,
            s_norm_eval_pf,
            epk_norm_oracle,
            epk_norm_eval_pf,
            edd_norm_oracle,
            edd_norm_eval_pf,
            f_norm_oracle: fdd_norm_oracle,
            f_norm_eval_pf: fdd_norm_eval_pf,
            k_norm_oracle,
            k_norm_eval_pf,
        };
    }

    pub fn prove_pk(&mut self, sk: &rlwe::SecretKey, pk: &rlwe::PublicKey) -> PkProof {
        let s_coeffs_ecd = self.encoder.encode_randomize(&sk.coeffs);
        let s_ntt_ecd = self.encoder.encode_randomize(&sk.ntt);
        let epk_coeffs_ecd = self.encoder.encode_randomize(&pk.epk_coeffs);
        let epk_ntt_ecd = self.encoder.encode_randomize(&pk.epk_ntt);

        let s_coeffs_ecd_ntt = self.ringq.ntt(&s_coeffs_ecd);
        let s_ntt_ecd_ntt = self.ringq.ntt(&s_ntt_ecd);
        let epk_coeffs_ecd_ntt = self.ringq.ntt(&epk_coeffs_ecd);
        let epk_ntt_ecd_ntt = self.ringq.ntt(&epk_ntt_ecd);

        let pk_oracle_coeffs = vec![
            &s_coeffs_ecd.coeffs[..],
            &s_ntt_ecd.coeffs[..],
            &epk_coeffs_ecd.coeffs[..],
            &epk_ntt_ecd.coeffs[..],
        ];

        let pk_oracle = self.celpc_prover.gen_batch_poly_oracle(&pk_oracle_coeffs);

        let ntt_oracle_coeffs = vec![&s_coeffs_ecd_ntt, &epk_coeffs_ecd_ntt];
        let ntt_oracle_ntt = vec![&s_ntt_ecd_ntt, &epk_ntt_ecd_ntt];
        let (ntt_poly, ntt_oracle) =
            self.lin_check_oracle(&ntt_oracle_coeffs, &ntt_oracle_ntt, LinCheckType::NTT);

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        let s_norm_oracle = self.row_check_oracle(&[&s_coeffs_ecd_ntt], &ternary_check_circuit);

        // p = -upk * s + epk
        let mut p_ntt_ecd_ntt = self.encoder.encode(&pk.p_ntt);
        self.ringq.ntt_inplace(&mut p_ntt_ecd_ntt);
        let mut upk_ntt_ecd_ntt = self.encoder.encode(&pk.u_ntt);
        self.ringq.ntt_inplace(&mut upk_ntt_ecd_ntt);
        let mut neg_one_ecd_ntt = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_one_ecd_ntt);

        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd_ntt, vec![0, 0]),
                (upk_ntt_ecd_ntt, vec![1, 0]),
                (neg_one_ecd_ntt, vec![0, 1]),
            ],
            max_degree: 1,
        };
        let pk_grc_oracle =
            self.gen_row_check_oracle(&[&s_ntt_ecd_ntt, &epk_ntt_ecd_ntt], &pk_circuit);

        self.oracle.write_batch_polynomial_oracle(&pk_oracle);
        self.oracle.write_lincheck_oracle(&ntt_oracle);
        self.oracle.write_rowcheck_oracle(&s_norm_oracle);
        self.oracle.write_genrowcheck_oracle(&pk_grc_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let s_coeffs_ecd_eval = self.ringq.evaluate(&s_coeffs_ecd, &alpha);
        let s_ntt_ecd_eval = self.ringq.evaluate(&s_ntt_ecd, &alpha);
        let epk_coeffs_ecd_eval = self.ringq.evaluate(&epk_coeffs_ecd, &alpha);
        let epk_ntt_ecd_eval = self.ringq.evaluate(&epk_ntt_ecd, &alpha);

        let pk_eval_pf_eval = vec![
            s_coeffs_ecd_eval,
            s_ntt_ecd_eval,
            epk_coeffs_ecd_eval,
            epk_ntt_ecd_eval,
        ];

        let pk_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &pk_eval_pf_eval,
            &pk_oracle.commitment,
        );

        let ntt_eval_pf = self.lin_check_eval(&alpha, &alpha_combine, &ntt_poly, &ntt_oracle);
        let s_norm_eval_pf = self.row_check_eval(&alpha, &s_norm_oracle);
        let pk_grc_eval_pf = self.gen_row_check_eval(&alpha, &pk_grc_oracle);

        return PkProof {
            pk_oracle,
            pk_eval_pf,

            ntt_oracle,
            ntt_eval_pf,

            s_norm_oracle,
            s_norm_eval_pf,
            pk_grc_oracle,
            pk_grc_eval_pf,
        };
    }

    pub fn prove_evk(
        &mut self,
        sk: &rlwe::SecretKey,
        pk: &rlwe::PublicKey,
        rlk: &rlwe::RelinKey,
        atk: Vec<&rlwe::AutomorphismKey>,
    ) -> EvkProof {
        let level = self.params.rlwe.gadget.len();

        let s_coeffs_ecd = self.encoder.encode_randomize(&sk.coeffs);
        let s_ntt_ecd = self.encoder.encode_randomize(&sk.ntt);
        let epk_coeffs_ecd = self.encoder.encode_randomize(&pk.epk_coeffs);
        let epk_ntt_ecd = self.encoder.encode_randomize(&pk.epk_ntt);
        let f_coeffs_ecd = self.encoder.encode_randomize(&rlk.f_coeffs);
        let f_ntt_ecd = self.encoder.encode_randomize(&rlk.f_ntt);
        let erlk0_coeffs_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e0_coeffs[i]))
            .collect::<Vec<_>>();
        let erlk0_ntt_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e0_ntt[i]))
            .collect::<Vec<_>>();
        let erlk1_coeffs_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e1_coeffs[i]))
            .collect::<Vec<_>>();
        let erlk1_ntt_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e1_ntt[i]))
            .collect::<Vec<_>>();
        let erlk2_coeffs_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e2_coeffs[i]))
            .collect::<Vec<_>>();
        let erlk2_ntt_ecd = (0..level)
            .map(|i| self.encoder.encode_randomize(&rlk.e2_ntt[i]))
            .collect::<Vec<_>>();
        let mut sk_d_ntt_ecd = Vec::with_capacity(atk.len());
        let mut eatk_coeffs_ecd = Vec::with_capacity(atk.len());
        let mut eatk_ntt_ecd = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            sk_d_ntt_ecd.push(self.encoder.encode_randomize(&atk[i].sk_d_ntt));
            eatk_coeffs_ecd.push(
                (0..level)
                    .map(|j| self.encoder.encode_randomize(&atk[i].e_coeffs[j]))
                    .collect::<Vec<_>>(),
            );
            eatk_ntt_ecd.push(
                (0..level)
                    .map(|j| self.encoder.encode_randomize(&atk[i].e_ntt[j]))
                    .collect::<Vec<_>>(),
            );
        }

        let s_coeffs_ecd_ntt = self.ringq.ntt(&s_coeffs_ecd);
        let s_ntt_ecd_ntt = self.ringq.ntt(&s_ntt_ecd);
        let epk_coeffs_ecd_ntt = self.ringq.ntt(&epk_coeffs_ecd);
        let epk_ntt_ecd_ntt = self.ringq.ntt(&epk_ntt_ecd);
        let f_coeffs_ecd_ntt = self.ringq.ntt(&f_coeffs_ecd);
        let f_ntt_ecd_ntt = self.ringq.ntt(&f_ntt_ecd);
        let erlk0_coeffs_ecd_ntt = erlk0_coeffs_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let erlk0_ntt_ecd_ntt = erlk0_ntt_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let erlk1_coeffs_ecd_ntt = erlk1_coeffs_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let erlk1_ntt_ecd_ntt = erlk1_ntt_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let erlk2_coeffs_ecd_ntt = erlk2_coeffs_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let erlk2_ntt_ecd_ntt = erlk2_ntt_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let sk_d_ntt_ecd_ntt = sk_d_ntt_ecd
            .iter()
            .map(|p| self.ringq.ntt(p))
            .collect::<Vec<_>>();
        let eatk_coeffs_ecd_ntt = eatk_coeffs_ecd
            .iter()
            .map(|p| p.iter().map(|q| self.ringq.ntt(q)).collect::<Vec<_>>())
            .collect::<Vec<_>>();
        let eatk_ntt_ecd_ntt = eatk_ntt_ecd
            .iter()
            .map(|p| p.iter().map(|q| self.ringq.ntt(q)).collect::<Vec<_>>())
            .collect::<Vec<_>>();

        let mut evk_oracle_coeffs = vec![
            &s_coeffs_ecd.coeffs[..],
            &s_ntt_ecd.coeffs[..],
            &epk_coeffs_ecd.coeffs[..],
            &epk_ntt_ecd.coeffs[..],
            &f_coeffs_ecd.coeffs[..],
            &f_ntt_ecd.coeffs[..],
        ];
        evk_oracle_coeffs.append(&mut erlk0_coeffs_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut erlk0_ntt_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut erlk1_coeffs_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut erlk1_ntt_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut erlk2_coeffs_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut erlk2_ntt_ecd.iter().map(|p| &p.coeffs[..]).collect());
        evk_oracle_coeffs.append(&mut sk_d_ntt_ecd.iter().map(|p| &p.coeffs[..]).collect());
        for i in 0..atk.len() {
            evk_oracle_coeffs
                .append(&mut eatk_coeffs_ecd[i].iter().map(|p| &p.coeffs[..]).collect());
        }
        for i in 0..atk.len() {
            evk_oracle_coeffs.append(&mut eatk_ntt_ecd[i].iter().map(|p| &p.coeffs[..]).collect());
        }

        let evk_oracle = self.celpc_prover.gen_batch_poly_oracle(&evk_oracle_coeffs);

        let mut ntt_oracle_coeffs = vec![&s_coeffs_ecd_ntt, &epk_coeffs_ecd_ntt, &f_coeffs_ecd_ntt];
        ntt_oracle_coeffs.append(&mut erlk0_coeffs_ecd_ntt.iter().map(|p| p).collect());
        ntt_oracle_coeffs.append(&mut erlk1_coeffs_ecd_ntt.iter().map(|p| p).collect());
        ntt_oracle_coeffs.append(&mut erlk2_coeffs_ecd_ntt.iter().map(|p| p).collect());
        for i in 0..atk.len() {
            ntt_oracle_coeffs.append(&mut eatk_coeffs_ecd_ntt[i].iter().map(|p| p).collect());
        }
        let mut ntt_oracle_ntt = vec![&s_ntt_ecd_ntt, &epk_ntt_ecd_ntt, &f_ntt_ecd_ntt];
        ntt_oracle_ntt.append(&mut erlk0_ntt_ecd_ntt.iter().map(|p| p).collect());
        ntt_oracle_ntt.append(&mut erlk1_ntt_ecd_ntt.iter().map(|p| p).collect());
        ntt_oracle_ntt.append(&mut erlk2_ntt_ecd_ntt.iter().map(|p| p).collect());
        for i in 0..atk.len() {
            ntt_oracle_ntt.append(&mut eatk_ntt_ecd_ntt[i].iter().map(|p| p).collect());
        }
        let (ntt_poly, ntt_oracle) =
            self.lin_check_oracle(&ntt_oracle_coeffs, &ntt_oracle_ntt, LinCheckType::NTT);

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        let s_norm_oracle = self.row_check_oracle(&[&s_coeffs_ecd_ntt], &ternary_check_circuit);

        // p = -upk * s + epk
        let mut p_ntt_ecd_ntt = self.encoder.encode(&pk.p_ntt);
        self.ringq.ntt_inplace(&mut p_ntt_ecd_ntt);
        let mut upk_ntt_ecd_ntt = self.encoder.encode(&pk.u_ntt);
        self.ringq.ntt_inplace(&mut upk_ntt_ecd_ntt);
        let mut neg_one_ecd_ntt = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_one_ecd_ntt);

        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd_ntt, vec![0, 0]),
                (upk_ntt_ecd_ntt, vec![1, 0]),
                (neg_one_ecd_ntt, vec![0, 1]),
            ],
            max_degree: 1,
        };
        let pk_grc_oracle =
            self.gen_row_check_oracle(&[&s_ntt_ecd_ntt, &epk_ntt_ecd_ntt], &pk_circuit);

        let f_norm_oracle = self.row_check_oracle(&[&f_coeffs_ecd_ntt], &ternary_check_circuit);

        let mut neg_one_ecd_ntt = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        self.ringq.ntt_inplace(&mut neg_one_ecd_ntt);

        let mut gad_ecd_ntt = Vec::with_capacity(level);
        let mut neg_gad_ecd_ntt = Vec::with_capacity(level);
        for i in 0..level {
            let mut gad_ecd_ntt_i = self.encoder.encode(&vec![
                self.params.rlwe.gadget[i].clone();
                self.params.rlwe.n
            ]);
            let mut neg_gad_ecd_ntt_i = self.encoder.encode(&vec![
                -self.params.rlwe.gadget[i]
                    .clone();
                self.params.rlwe.n
            ]);
            self.ringq.ntt_inplace(&mut gad_ecd_ntt_i);
            self.ringq.ntt_inplace(&mut neg_gad_ecd_ntt_i);

            gad_ecd_ntt.push(gad_ecd_ntt_i);
            neg_gad_ecd_ntt.push(neg_gad_ecd_ntt_i);
        }

        let mut r0_grc_oracle = Vec::with_capacity(level);
        let mut r1_grc_oracle = Vec::with_capacity(level);
        let mut r2_grc_oracle = Vec::with_capacity(level);
        let mut erlk0_norm_oracle = Vec::with_capacity(level);
        let mut erlk1_norm_oracle = Vec::with_capacity(level);
        let mut erlk2_norm_oracle = Vec::with_capacity(level);
        for i in 0..level {
            let mut r0_ntt_ecd_ntt = self.encoder.encode(&rlk.r0_ntt[i]);
            let mut r1_ntt_ecd_ntt = self.encoder.encode(&rlk.r1_ntt[i]);
            let mut r2_ntt_ecd_ntt = self.encoder.encode(&rlk.r2_ntt[i]);
            self.ringq.ntt_inplace(&mut r0_ntt_ecd_ntt);
            self.ringq.ntt_inplace(&mut r1_ntt_ecd_ntt);
            self.ringq.ntt_inplace(&mut r2_ntt_ecd_ntt);

            let mut urlk0_ecd_ntt = self.encoder.encode(&rlk.u0_ntt[i]);
            let mut urlk1_ecd_ntt = self.encoder.encode(&rlk.u1_ntt[i]);
            self.ringq.ntt_inplace(&mut urlk0_ecd_ntt);
            self.ringq.ntt_inplace(&mut urlk1_ecd_ntt);

            let r0_circuit_ntt = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ntt_ecd_ntt, vec![0, 0]),
                    (urlk0_ecd_ntt.clone(), vec![1, 0]),
                    (neg_one_ecd_ntt.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };
            r0_grc_oracle.push(
                self.gen_row_check_oracle(
                    &[&s_ntt_ecd_ntt, &erlk0_ntt_ecd_ntt[i]],
                    &r0_circuit_ntt,
                ),
            );

            let r1_circuit_ntt = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ntt_ecd_ntt, vec![0, 0, 0]),
                    (urlk0_ecd_ntt.clone(), vec![1, 0, 0]),
                    (neg_gad_ecd_ntt[i].clone(), vec![0, 1, 0]),
                    (neg_one_ecd_ntt.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };
            r1_grc_oracle.push(self.gen_row_check_oracle(
                &[&f_ntt_ecd_ntt, &s_ntt_ecd_ntt, &erlk1_ntt_ecd_ntt[i]],
                &r1_circuit_ntt,
            ));

            let r2_circuit_ntt = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ntt_ecd_ntt, vec![0, 0, 0]),
                    (urlk1_ecd_ntt.clone(), vec![1, 0, 0]),
                    (gad_ecd_ntt[i].clone(), vec![0, 1, 0]),
                    (neg_one_ecd_ntt.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };
            r2_grc_oracle.push(self.gen_row_check_oracle(
                &[&s_ntt_ecd_ntt, &f_ntt_ecd_ntt, &erlk2_ntt_ecd_ntt[i]],
                &r2_circuit_ntt,
            ));

            erlk0_norm_oracle
                .push(self.row_check_oracle(&[&erlk0_coeffs_ecd_ntt[i]], &ternary_check_circuit));
            erlk1_norm_oracle
                .push(self.row_check_oracle(&[&erlk1_coeffs_ecd_ntt[i]], &ternary_check_circuit));
            erlk2_norm_oracle
                .push(self.row_check_oracle(&[&erlk2_coeffs_ecd_ntt[i]], &ternary_check_circuit));
        }

        let mut s_aut_poly = Vec::with_capacity(atk.len());
        let mut s_aut_oracle = Vec::with_capacity(atk.len());
        let mut a_grc_oracle = Vec::with_capacity(atk.len());
        let mut eatk_norm_oracle = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            let (s_aut_poly_i, s_aut_oracle_i) = self.lin_check_oracle(
                &[&s_ntt_ecd_ntt],
                &[&sk_d_ntt_ecd_ntt[i]],
                LinCheckType::Automorphism(atk[i].d),
            );
            s_aut_poly.push(s_aut_poly_i);
            s_aut_oracle.push(s_aut_oracle_i);
            let mut a_grc_oracle_i = Vec::with_capacity(level);
            let mut eatk_norm_oracle_i = Vec::with_capacity(level);

            for j in 0..level {
                let mut a_ntt_ecd_ntt = self.encoder.encode(&atk[i].a_ntt[j]);
                let mut uatk_ntt_ecd_ntt = self.encoder.encode(&atk[i].u_ntt[j]);
                self.ringq.ntt_inplace(&mut a_ntt_ecd_ntt);
                self.ringq.ntt_inplace(&mut uatk_ntt_ecd_ntt);

                let a_circuit_ntt = PolyMultiVariatePoly {
                    coeffs: vec![
                        (a_ntt_ecd_ntt, vec![0, 0, 0]),
                        (uatk_ntt_ecd_ntt, vec![1, 0, 0]),
                        (neg_gad_ecd_ntt[j].clone(), vec![0, 1, 0]),
                        (neg_one_ecd_ntt.clone(), vec![0, 0, 1]),
                    ],
                    max_degree: 1,
                };

                a_grc_oracle_i.push(self.gen_row_check_oracle(
                    &[
                        &s_ntt_ecd_ntt,
                        &sk_d_ntt_ecd_ntt[i],
                        &eatk_ntt_ecd_ntt[i][j],
                    ],
                    &a_circuit_ntt,
                ));

                eatk_norm_oracle_i.push(
                    self.row_check_oracle(&[&eatk_coeffs_ecd_ntt[i][j]], &ternary_check_circuit),
                );
            }

            a_grc_oracle.push(a_grc_oracle_i);
            eatk_norm_oracle.push(eatk_norm_oracle_i);
        }

        self.oracle.write_batch_polynomial_oracle(&evk_oracle);
        self.oracle.write_lincheck_oracle(&ntt_oracle);
        self.oracle.write_rowcheck_oracle(&s_norm_oracle);
        self.oracle.write_genrowcheck_oracle(&pk_grc_oracle);
        self.oracle.write_rowcheck_oracle(&f_norm_oracle);
        for i in 0..level {
            self.oracle.write_genrowcheck_oracle(&r0_grc_oracle[i]);
            self.oracle.write_genrowcheck_oracle(&r1_grc_oracle[i]);
            self.oracle.write_genrowcheck_oracle(&r2_grc_oracle[i]);
            self.oracle.write_rowcheck_oracle(&erlk0_norm_oracle[i]);
            self.oracle.write_rowcheck_oracle(&erlk1_norm_oracle[i]);
            self.oracle.write_rowcheck_oracle(&erlk2_norm_oracle[i]);
        }
        for i in 0..atk.len() {
            self.oracle.write_lincheck_oracle(&s_aut_oracle[i]);
            for j in 0..level {
                self.oracle.write_genrowcheck_oracle(&a_grc_oracle[i][j]);
                self.oracle.write_rowcheck_oracle(&eatk_norm_oracle[i][j]);
            }
        }
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        let s_coeffs_ecd_eval = self.ringq.evaluate(&s_coeffs_ecd, &alpha);
        let s_ntt_ecd_eval = self.ringq.evaluate(&s_ntt_ecd, &alpha);
        let epk_coeffs_ecd_eval = self.ringq.evaluate(&epk_coeffs_ecd, &alpha);
        let epk_ntt_ecd_eval = self.ringq.evaluate(&epk_ntt_ecd, &alpha);
        let f_coeffs_ecd_eval = self.ringq.evaluate(&f_coeffs_ecd, &alpha);
        let f_ntt_ecd_eval = self.ringq.evaluate(&f_ntt_ecd, &alpha);
        let mut erlk0_coeffs_ecd_eval = erlk0_coeffs_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut erlk0_ntt_ecd_eval = erlk0_ntt_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut erlk1_coeffs_ecd_eval = erlk1_coeffs_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut erlk1_ntt_ecd_eval = erlk1_ntt_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut erlk2_coeffs_ecd_eval = erlk2_coeffs_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut erlk2_ntt_ecd_eval = erlk2_ntt_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut sk_d_ntt_ecd_eval = sk_d_ntt_ecd
            .iter()
            .map(|p| self.ringq.evaluate(p, &alpha))
            .collect::<Vec<_>>();
        let mut eatk_coeffs_ecd_eval = Vec::with_capacity(atk.len());
        let mut eatk_ntt_ecd_eval = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            eatk_coeffs_ecd_eval.push(
                eatk_coeffs_ecd[i]
                    .iter()
                    .map(|p| self.ringq.evaluate(p, &alpha))
                    .collect::<Vec<_>>(),
            );
            eatk_ntt_ecd_eval.push(
                eatk_ntt_ecd[i]
                    .iter()
                    .map(|p| self.ringq.evaluate(p, &alpha))
                    .collect::<Vec<_>>(),
            );
        }

        let mut evk_eval_pf_eval = vec![
            s_coeffs_ecd_eval,
            s_ntt_ecd_eval,
            epk_coeffs_ecd_eval,
            epk_ntt_ecd_eval,
            f_coeffs_ecd_eval,
            f_ntt_ecd_eval,
        ];
        evk_eval_pf_eval.append(&mut erlk0_coeffs_ecd_eval);
        evk_eval_pf_eval.append(&mut erlk0_ntt_ecd_eval);
        evk_eval_pf_eval.append(&mut erlk1_coeffs_ecd_eval);
        evk_eval_pf_eval.append(&mut erlk1_ntt_ecd_eval);
        evk_eval_pf_eval.append(&mut erlk2_coeffs_ecd_eval);
        evk_eval_pf_eval.append(&mut erlk2_ntt_ecd_eval);
        evk_eval_pf_eval.append(&mut sk_d_ntt_ecd_eval);
        for i in 0..atk.len() {
            evk_eval_pf_eval.append(&mut eatk_coeffs_ecd_eval[i]);
        }
        for i in 0..atk.len() {
            evk_eval_pf_eval.append(&mut eatk_ntt_ecd_eval[i]);
        }

        let evk_eval_pf = self.celpc_prover.evaluate_batch(
            &alpha,
            &alpha_combine,
            &evk_eval_pf_eval,
            &evk_oracle.commitment,
        );

        let ntt_eval_pf = self.lin_check_eval(&alpha, &alpha_combine, &ntt_poly, &ntt_oracle);
        let s_norm_eval_pf = self.row_check_eval(&alpha, &s_norm_oracle);
        let pk_grc_eval_pf = self.gen_row_check_eval(&alpha, &pk_grc_oracle);

        let mut r0_grc_eval_pf = Vec::with_capacity(level);
        let mut r1_grc_eval_pf = Vec::with_capacity(level);
        let mut r2_grc_eval_pf = Vec::with_capacity(level);
        for i in 0..level {
            r0_grc_eval_pf.push(self.gen_row_check_eval(&alpha, &r0_grc_oracle[i]));
            r1_grc_eval_pf.push(self.gen_row_check_eval(&alpha, &r1_grc_oracle[i]));
            r2_grc_eval_pf.push(self.gen_row_check_eval(&alpha, &r2_grc_oracle[i]));
        }

        let f_norm_eval_pf = self.row_check_eval(&alpha, &f_norm_oracle);
        let mut erlk0_norm_eval_pf = Vec::with_capacity(level);
        let mut erlk1_norm_eval_pf = Vec::with_capacity(level);
        let mut erlk2_norm_eval_pf = Vec::with_capacity(level);
        for i in 0..level {
            erlk0_norm_eval_pf.push(self.row_check_eval(&alpha, &erlk0_norm_oracle[i]));
            erlk1_norm_eval_pf.push(self.row_check_eval(&alpha, &erlk1_norm_oracle[i]));
            erlk2_norm_eval_pf.push(self.row_check_eval(&alpha, &erlk2_norm_oracle[i]));
        }

        let mut s_aut_eval_pf = Vec::with_capacity(atk.len());
        let mut a_grc_eval_pf = Vec::with_capacity(atk.len());
        let mut eatk_norm_eval_pf = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            s_aut_eval_pf.push(self.lin_check_eval(
                &alpha,
                &alpha_combine,
                &s_aut_poly[i],
                &s_aut_oracle[i],
            ));
            let mut a_grc_eval_pf_i = Vec::with_capacity(level);
            let mut eatk_norm_eval_pf_i = Vec::with_capacity(level);
            for j in 0..level {
                a_grc_eval_pf_i.push(self.gen_row_check_eval(&alpha, &a_grc_oracle[i][j]));
                eatk_norm_eval_pf_i.push(self.row_check_eval(&alpha, &eatk_norm_oracle[i][j]));
            }
            a_grc_eval_pf.push(a_grc_eval_pf_i);
            eatk_norm_eval_pf.push(eatk_norm_eval_pf_i);
        }

        return EvkProof {
            evk_oracle,
            evk_eval_pf,

            ntt_oracle,
            ntt_eval_pf,

            s_norm_oracle,
            s_norm_eval_pf,

            pk_grc_oracle,
            pk_grc_eval_pf,

            r0_grc_oracle,
            r0_grc_eval_pf,
            r1_grc_oracle,
            r1_grc_eval_pf,
            r2_grc_oracle,
            r2_grc_eval_pf,

            f_norm_oracle,
            f_norm_eval_pf,

            erlk0_norm_oracle,
            erlk0_norm_eval_pf,
            erlk1_norm_oracle,
            erlk1_norm_eval_pf,
            erlk2_norm_oracle,
            erlk2_norm_eval_pf,

            s_aut_oracle,
            s_aut_eval_pf,
            eatk_norm_oracle,
            eatk_norm_eval_pf,
            a_grc_oracle,
            a_grc_eval_pf,
        };
    }
}

pub struct Verifier<'a> {
    pub params: &'a Parameters,

    pub encoder: Encoder<'a>,
    pub celpc_verifier: celpc::PolynomialVerifier<'a>,

    pub oracle: Oracle,

    pub ringq: BigRing,
    pub neg_transformer: rlwe::NegacyclicTransformer,
}

impl<'a> Verifier<'a> {
    pub fn new(params: &'a Parameters, ck: &'a celpc::CommitKey) -> Verifier<'a> {
        let encoder = Encoder::new(params);
        let celpc_verifier = celpc::PolynomialVerifier::new(&params.pcs, ck);

        Verifier {
            params: params,
            encoder: encoder,
            celpc_verifier: celpc_verifier,

            oracle: Oracle::new(),

            ringq: BigRing::new(params.embedding_n, &params.rlwe.q),
            neg_transformer: rlwe::NegacyclicTransformer::new(params.rlwe.n, &params.rlwe.q),
        }
    }

    pub fn row_check(
        &mut self,
        alpha: &Integer,
        a_eval: &[&Integer],
        c: &BigMultiVariatePoly,
        rc_oracle: &RowCheckOracle,
        rc_eval_pf: &RowCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify(
            &rc_oracle.quo_oracle.commitment,
            &rc_oracle.quo_oracle.open_proof,
        ) {
            println!("row_check oracle verification failed");
            return false;
        }
        if !self.celpc_verifier.verify_evaluation(
            alpha,
            &rc_oracle.quo_oracle.commitment,
            &rc_eval_pf.quo_eval_pf,
        ) {
            println!("row_check eval proof verification failed");
            return false;
        }

        let mut c_a_eval = self.ringq.evaluate_multivariate(c, a_eval);

        let mut z = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        z -= Integer::ONE;
        let mut qz_eval = Integer::ZERO;
        qz_eval.assign(&z);
        qz_eval *= &rc_eval_pf.quo_eval_pf.y_big;
        qz_eval.modulo_mut(&self.params.rlwe.q);

        c_a_eval -= &qz_eval;
        if !c_a_eval.is_zero() {
            return false;
        }

        return true;
    }

    pub fn gen_row_check(
        &mut self,
        alpha: &Integer,
        a_eval: &[&Integer],
        c: &PolyMultiVariatePoly,
        grc_oracle: &GenRowCheckOracle,
        grc_eval_pf: &GenRowCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify(
            &grc_oracle.quo_oracle.commitment,
            &grc_oracle.quo_oracle.open_proof,
        ) {
            return false;
        }
        if !self.celpc_verifier.verify_evaluation(
            alpha,
            &grc_oracle.quo_oracle.commitment,
            &grc_eval_pf.quo_eval_pf,
        ) {
            return false;
        }

        let mut c_big = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(c.coeffs.len()),
            max_degree: c.max_degree,
        };
        for i in 0..c.coeffs.len() {
            c_big.coeffs.push((
                self.ringq.evaluate(&c.coeffs[i].0, &alpha),
                c.coeffs[i].1.clone(),
            ));
        }
        let mut c_a_eval = self.ringq.evaluate_multivariate(&c_big, a_eval);

        let mut z = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        z -= Integer::ONE;
        let mut qz_eval = Integer::ZERO;
        qz_eval.assign(&z);
        qz_eval *= &grc_eval_pf.quo_eval_pf.y_big;
        qz_eval.modulo_mut(&self.params.rlwe.q);

        c_a_eval -= &qz_eval;
        if !c_a_eval.is_zero() {
            return false;
        }

        return true;
    }

    pub fn norm_check(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        a_eval: &Integer,
        nm_oracle: &NormCheckOracle,
        nm_eval_pf: &NormCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify_batch(
            &nm_oracle.decomposed_oracle.commitment,
            &nm_oracle.decomposed_oracle.open_proof,
        ) {
            println!("decomposed_oracle verification failed");
            return false;
        }
        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &nm_oracle.decomposed_oracle.commitment,
            &nm_eval_pf.decomposed_eval_pf,
        ) {
            println!("decomposed_eval_pf verification failed");
            return false;
        }

        let norm_check_circuit_dcmp = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };

        for i in 0..nm_oracle.log_bound + 1 {
            if !self.row_check(
                &alpha,
                &[&nm_eval_pf.decomposed_eval_pf.y_batch[i]],
                &norm_check_circuit_dcmp,
                &nm_oracle.rc_oracle[i],
                &nm_eval_pf.rc_eval_pf[i],
            ) {
                println!("row_check {} verification failed", i);
                return false;
            }
        }

        let mut norm_check_circuit = BigMultiVariatePoly {
            coeffs: Vec::with_capacity(nm_oracle.log_bound + 2),
            max_degree: 1,
        };
        let mut deg = vec![0; nm_oracle.log_bound + 2];
        deg[0] = 1;
        norm_check_circuit
            .coeffs
            .push((Integer::from(1), deg.clone()));

        deg.fill(0);
        deg[1] = 1;
        norm_check_circuit
            .coeffs
            .push((Integer::from(-1), deg.clone()));
        for i in 2..nm_oracle.log_bound + 2 {
            deg.fill(0);
            deg[i] = 1;
            norm_check_circuit
                .coeffs
                .push((Integer::from(-(1i64 << (i - 2))), deg.clone()));
        }

        let mut norm_check_input = Vec::with_capacity(nm_oracle.log_bound + 2);
        norm_check_input.push(a_eval);
        for i in 0..nm_oracle.log_bound + 1 {
            norm_check_input.push(&nm_eval_pf.decomposed_eval_pf.y_batch[i]);
        }

        if !self.row_check(
            &alpha,
            &norm_check_input,
            &norm_check_circuit,
            &nm_oracle.rc_oracle[nm_oracle.log_bound + 1],
            &nm_eval_pf.rc_eval_pf[nm_oracle.log_bound + 1],
        ) {
            println!("row_check verification failed");
            return false;
        }

        return true;
    }

    pub fn lin_check_challenge(&mut self, lc_oracle: &LinCheckOracle) -> LinCheckChallenge {
        if !self.celpc_verifier.verify(
            &lc_oracle.g_oracle.commitment,
            &lc_oracle.g_oracle.open_proof,
        ) {
            panic!("g_oracle verification failed");
        }

        if !self.celpc_verifier.verify_batch(
            &lc_oracle.quo_rem_oracle.commitment,
            &lc_oracle.quo_rem_oracle.open_proof,
        ) {
            panic!("quo_rem verification failed");
        }

        self.oracle.write_polynomial_oracle(&lc_oracle.g_oracle);
        self.oracle.finalize();

        let beta = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let v_big = self.oracle.read_range_bigint(&self.params.rlwe.q);

        return LinCheckChallenge { beta, v: v_big };
    }

    pub fn lin_check(
        &mut self,
        alpha: &Integer,
        alpha_combine: &Integer,
        a_eval: &[&Integer],
        b_eval: &[&Integer],
        lc_chal: &LinCheckChallenge,
        lc_oracle: &LinCheckOracle,
        lc_eval_pf: &LinCheckEvalProof,
    ) -> bool {
        if !self.celpc_verifier.verify_evaluation(
            alpha,
            &lc_oracle.g_oracle.commitment,
            &lc_eval_pf.g_eval_pf,
        ) {
            println!("g_eval_pf verification failed");
            return false;
        }

        if !self.celpc_verifier.verify_evaluation_batch(
            alpha,
            alpha_combine,
            &lc_oracle.quo_rem_oracle.commitment,
            &lc_eval_pf.quo_rem_eval_pf,
        ) {
            println!("quo_rem_eval_pf verification failed");
            return false;
        }

        let (beta, v_big) = (&lc_chal.beta, &lc_chal.v);

        let mut v = vec![Integer::from(1); self.params.rlwe.n];
        for i in 1..v.len() {
            v[i] = v[i - 1].clone() * v_big;
            v[i].modulo_mut(&self.params.rlwe.q);
        }

        let mut w;
        match lc_oracle.lin_type {
            LinCheckType::NTT => {
                w = v.clone();
                w.reverse();
                self.neg_transformer.intt_without_normalize(&mut w);
            }
            LinCheckType::Automorphism(d) => {
                let d_inv = modinverse::modinverse(d, 2 * &self.params.rlwe.n).unwrap();
                w = self.neg_transformer.automorphism(&v, d_inv);
            }
        }

        let v_ecd = self.encoder.encode(&v);
        let w_ecd = self.encoder.encode(&w);

        let v_ecd_eval = self.ringq.evaluate(&v_ecd, alpha);
        let w_ecd_eval = self.ringq.evaluate(&w_ecd, alpha);

        let mut check_right = lc_eval_pf.g_eval_pf.y_big.clone();
        let mut aw = Integer::ZERO;
        let mut bv = Integer::ZERO;
        let mut beta_pow = beta.clone();
        for i in 0..a_eval.len() {
            aw.assign(a_eval[i]);
            aw *= &w_ecd_eval;
            bv.assign(b_eval[i]);
            bv *= &v_ecd_eval;
            aw -= &bv;
            aw *= &beta_pow;
            check_right += &aw;
            check_right.modulo_mut(&self.params.rlwe.q);

            beta_pow *= beta;
            beta_pow.modulo_mut(&self.params.rlwe.q);
        }

        let mut qz = alpha
            .pow_mod_ref(&Integer::from(self.params.rlwe.n), &self.params.rlwe.q)
            .unwrap()
            .complete();
        qz -= Integer::ONE;
        qz *= &lc_eval_pf.quo_rem_eval_pf.y_batch[0];

        let ra = lc_eval_pf.quo_rem_eval_pf.y_batch[1].clone();

        let mut check_left = Integer::ZERO;
        check_left.assign(&qz);
        check_left += &ra;
        check_left += &lc_oracle.mu;
        check_left.modulo_mut(&self.params.rlwe.q);

        check_right -= &check_left;
        if !check_right.is_zero() {
            return false;
        }

        return true;
    }

    pub fn verify_pkenc(
        &mut self,
        pk: &rlwe::PublicKey,
        ct: &rlwe::PkCiphertext,
        pf: &PkEncProof,
    ) -> bool {
        if !self
            .celpc_verifier
            .verify_batch(&pf.pkenc_oracle.commitment, &pf.pkenc_oracle.open_proof)
        {
            println!("pkenc_oracle verification failed");
            return false;
        }

        let ntt_chal = self.lin_check_challenge(&pf.ntt_oracle);

        self.oracle.write_batch_polynomial_oracle(&pf.pkenc_oracle);
        self.oracle.write_lincheck_oracle(&pf.ntt_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.c0_grc_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.c1_grc_oracle);
        self.oracle.write_rowcheck_oracle(&pf.e0_norm_oracle);
        self.oracle.write_rowcheck_oracle(&pf.e1_norm_oracle);
        self.oracle.write_rowcheck_oracle(&pf.f_norm_oracle);
        self.oracle.write_normcheck_oracle(&pf.m_norm_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &pf.pkenc_oracle.commitment,
            &pf.pkenc_eval_pf,
        ) {
            println!("pkenc_eval_pf verification failed");
            return false;
        }

        let e0_coeffs_ecd_eval = pf.pkenc_eval_pf.y_batch[0].clone();
        let e0_ntt_ecd_eval = pf.pkenc_eval_pf.y_batch[1].clone();
        let e1_coeffs_ecd_eval = pf.pkenc_eval_pf.y_batch[2].clone();
        let e1_ntt_ecd_eval = pf.pkenc_eval_pf.y_batch[3].clone();
        let f_coeffs_ecd_eval = pf.pkenc_eval_pf.y_batch[4].clone();
        let f_ntt_ecd_eval = pf.pkenc_eval_pf.y_batch[5].clone();
        let m_coeffs_ecd_eval = pf.pkenc_eval_pf.y_batch[6].clone();
        let m_ntt_ecd_eval = pf.pkenc_eval_pf.y_batch[7].clone();

        if !self.lin_check(
            &alpha,
            &alpha_combine,
            &[
                &e0_coeffs_ecd_eval,
                &e1_coeffs_ecd_eval,
                &f_coeffs_ecd_eval,
                &m_coeffs_ecd_eval,
            ],
            &[
                &e0_ntt_ecd_eval,
                &e1_ntt_ecd_eval,
                &f_ntt_ecd_eval,
                &m_ntt_ecd_eval,
            ],
            &ntt_chal,
            &pf.ntt_oracle,
            &pf.ntt_eval_pf,
        ) {
            return false;
        }

        let c_ntt_ecd = self.encoder.encode(&ct.c_ntt);
        let u_ntt_ecd = self.encoder.encode(&ct.u_ntt);
        let mut neg_p_ntt_ecd = self.encoder.encode(&pk.p_ntt);
        let mut neg_upk_ntt_ecd = self.encoder.encode(&pk.u_ntt);
        for i in 0..self.encoder.embedding_n {
            neg_p_ntt_ecd.coeffs[i].neg_assign();
            neg_upk_ntt_ecd.coeffs[i].neg_assign();
        }
        let neg_one_ecd = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);
        let neg_delta_ecd = self
            .encoder
            .encode(&vec![-self.params.rlwe.delta.clone(); self.params.rlwe.n]);

        // c = pf + Delta m + e0
        let c_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (c_ntt_ecd, vec![0, 0, 0]),
                (neg_p_ntt_ecd, vec![1, 0, 0]),
                (neg_delta_ecd, vec![0, 1, 0]),
                (neg_one_ecd.clone(), vec![0, 0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[&f_ntt_ecd_eval, &m_ntt_ecd_eval, &e0_ntt_ecd_eval],
            &c_circuit,
            &pf.c0_grc_oracle,
            &pf.c0_grc_eval_pf,
        ) {
            println!("c0_grc verification failed");
            return false;
        }

        // u = upk*f + e1
        let u_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (u_ntt_ecd, vec![0, 0]),
                (neg_upk_ntt_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[&f_ntt_ecd_eval, &e1_ntt_ecd_eval],
            &u_circuit,
            &pf.c1_grc_oracle,
            &pf.c1_grc_eval_pf,
        ) {
            println!("c1_grc verification failed");
            return false;
        }

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };

        if !self.row_check(
            &alpha,
            &[&e0_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.e0_norm_oracle,
            &pf.e0_norm_eval_pf,
        ) {
            println!("e0_norm verification failed");
            return false;
        }
        if !self.row_check(
            &alpha,
            &[&e1_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.e1_norm_oracle,
            &pf.e1_norm_eval_pf,
        ) {
            println!("e1_norm verification failed");
            return false;
        }
        if !self.row_check(
            &alpha,
            &[&f_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.f_norm_oracle,
            &pf.f_norm_eval_pf,
        ) {
            println!("f_norm verification failed");
            return false;
        }
        if !self.norm_check(
            &alpha,
            &alpha_combine,
            &m_coeffs_ecd_eval,
            &pf.m_norm_oracle,
            &pf.m_norm_eval_pf,
        ) {
            println!("m_norm verification failed");
            return false;
        }

        return true;
    }

    pub fn verify_ddec(
        &mut self,
        pk: &rlwe::PublicKey,
        ct: &rlwe::PkCiphertext,
        pd: &rlwe::PartialDec,
        pf: &DDecProof,
    ) -> bool {
        if !self
            .celpc_verifier
            .verify_batch(&pf.ddec_oracle.commitment, &pf.ddec_oracle.open_proof)
        {
            println!("ddec_oracle verification failed");
            return false;
        }

        let ntt_chal = self.lin_check_challenge(&pf.ntt_oracle);

        self.oracle.write_batch_polynomial_oracle(&pf.ddec_oracle);
        self.oracle.write_lincheck_oracle(&pf.ntt_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.pk_grc_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.dd_grc_oracle);
        self.oracle.write_rowcheck_oracle(&pf.s_norm_oracle);
        self.oracle.write_rowcheck_oracle(&pf.epk_norm_oracle);
        self.oracle.write_rowcheck_oracle(&pf.edd_norm_oracle);
        self.oracle.write_rowcheck_oracle(&pf.f_norm_oracle);
        self.oracle.write_normcheck_oracle(&pf.k_norm_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &pf.ddec_oracle.commitment,
            &pf.ddec_eval_pf,
        ) {
            println!("ddec_eval_pf verification failed");
            return false;
        }

        let s_coeffs_ecd_eval = pf.ddec_eval_pf.y_batch[0].clone();
        let s_ntt_ecd_eval = pf.ddec_eval_pf.y_batch[1].clone();
        let epk_coeffs_ecd_eval = pf.ddec_eval_pf.y_batch[2].clone();
        let epk_ntt_ecd_eval = pf.ddec_eval_pf.y_batch[3].clone();
        let edd_coeffs_ecd_eval = pf.ddec_eval_pf.y_batch[4].clone();
        let edd_ntt_ecd_eval = pf.ddec_eval_pf.y_batch[5].clone();
        let f_coeffs_ecd_eval = pf.ddec_eval_pf.y_batch[6].clone();
        let f_ntt_ecd_eval = pf.ddec_eval_pf.y_batch[7].clone();
        let k_coeffs_ecd_eval = pf.ddec_eval_pf.y_batch[8].clone();
        let k_ntt_ecd_eval = pf.ddec_eval_pf.y_batch[9].clone();

        if !self.lin_check(
            &alpha,
            &alpha_combine,
            &[
                &s_coeffs_ecd_eval,
                &epk_coeffs_ecd_eval,
                &edd_coeffs_ecd_eval,
                &f_coeffs_ecd_eval,
                &k_coeffs_ecd_eval,
            ],
            &[
                &s_ntt_ecd_eval,
                &epk_ntt_ecd_eval,
                &edd_ntt_ecd_eval,
                &f_ntt_ecd_eval,
                &k_ntt_ecd_eval,
            ],
            &ntt_chal,
            &pf.ntt_oracle,
            &pf.ntt_eval_pf,
        ) {
            println!("ntt verification failed");
            return false;
        }

        let p_ntt_ecd = self.encoder.encode(&pk.p_ntt);
        let upk_ntt_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);

        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd, vec![0, 0]),
                (upk_ntt_ecd, vec![1, 0]),
                (neg_one_ecd.clone(), vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[&s_ntt_ecd_eval, &epk_ntt_ecd_eval],
            &pk_circuit,
            &pf.pk_grc_oracle,
            &pf.pk_grc_eval_pf,
        ) {
            println!("pk_grc verification failed");
            return false;
        }

        let d_ntt_ecd = self.encoder.encode(&pd.d_ntt);
        let mut neg_c_ntt_ecd = self.encoder.encode(&ct.c_ntt);
        let mut neg_udd_ntt_ecd = self.encoder.encode(&pd.u_ntt);
        for i in 0..self.encoder.embedding_n {
            neg_c_ntt_ecd.coeffs[i].neg_assign();
            neg_udd_ntt_ecd.coeffs[i].neg_assign();
        }
        let bdd: Integer = Integer::from(1) << 128;
        let bdd_ecd = self.encoder.encode(&vec![bdd.clone(); self.params.rlwe.n]);

        let dd_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (d_ntt_ecd, vec![0, 0, 0, 0]),
                (neg_c_ntt_ecd, vec![1, 0, 0, 0]),
                (neg_udd_ntt_ecd, vec![0, 1, 0, 0]),
                (neg_one_ecd, vec![0, 0, 1, 0]),
                (bdd_ecd, vec![0, 0, 0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[
                &s_ntt_ecd_eval,
                &f_ntt_ecd_eval,
                &edd_ntt_ecd_eval,
                &k_ntt_ecd_eval,
            ],
            &dd_circuit,
            &pf.dd_grc_oracle,
            &pf.dd_grc_eval_pf,
        ) {
            println!("dd_grc verification failed");
            return false;
        }

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        if !self.row_check(
            &alpha,
            &[&s_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.s_norm_oracle,
            &pf.s_norm_eval_pf,
        ) {
            println!("s_norm verification failed");
            return false;
        }
        if !self.row_check(
            &alpha,
            &[&epk_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.epk_norm_oracle,
            &pf.epk_norm_eval_pf,
        ) {
            println!("epk_norm verification failed");
            return false;
        }
        if !self.row_check(
            &alpha,
            &[&edd_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.edd_norm_oracle,
            &pf.edd_norm_eval_pf,
        ) {
            println!("edd_norm verification failed");
            return false;
        }
        if !self.row_check(
            &alpha,
            &[&f_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.f_norm_oracle,
            &pf.f_norm_eval_pf,
        ) {
            println!("f_norm verification failed");
            return false;
        }
        if !self.norm_check(
            &alpha,
            &alpha_combine,
            &k_coeffs_ecd_eval,
            &pf.k_norm_oracle,
            &pf.k_norm_eval_pf,
        ) {
            println!("k_norm verification failed");
            return false;
        }

        return true;
    }

    pub fn verify_pk(&mut self, pk: &rlwe::PublicKey, pf: &PkProof) -> bool {
        if !self
            .celpc_verifier
            .verify_batch(&pf.pk_oracle.commitment, &pf.pk_oracle.open_proof)
        {
            println!("pk_oracle verification failed");
            return false;
        }

        let ntt_chal = self.lin_check_challenge(&pf.ntt_oracle);

        self.oracle.write_batch_polynomial_oracle(&pf.pk_oracle);
        self.oracle.write_lincheck_oracle(&pf.ntt_oracle);
        self.oracle.write_rowcheck_oracle(&pf.s_norm_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.pk_grc_oracle);
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &pf.pk_oracle.commitment,
            &pf.pk_eval_pf,
        ) {
            println!("pk_eval_pf verification failed");
            return false;
        }

        let s_coeffs_ecd_eval = pf.pk_eval_pf.y_batch[0].clone();
        let s_ntt_ecd_eval = pf.pk_eval_pf.y_batch[1].clone();
        let epk_coeffs_ecd_eval = pf.pk_eval_pf.y_batch[2].clone();
        let epk_ntt_ecd_eval = pf.pk_eval_pf.y_batch[3].clone();

        let ntt_coeffs_eval = vec![&s_coeffs_ecd_eval, &epk_coeffs_ecd_eval];
        let ntt_ntt_eval = vec![&s_ntt_ecd_eval, &epk_ntt_ecd_eval];
        if !self.lin_check(
            &alpha,
            &alpha_combine,
            &ntt_coeffs_eval,
            &ntt_ntt_eval,
            &ntt_chal,
            &pf.ntt_oracle,
            &pf.ntt_eval_pf,
        ) {
            return false;
        }

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        if !self.row_check(
            &alpha,
            &[&s_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.s_norm_oracle,
            &pf.s_norm_eval_pf,
        ) {
            println!("s_norm verification failed");
            return false;
        }

        let p_ntt_ecd = self.encoder.encode(&pk.p_ntt);
        let upk_ntt_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);

        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd, vec![0, 0]),
                (upk_ntt_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[&s_ntt_ecd_eval, &epk_ntt_ecd_eval],
            &pk_circuit,
            &pf.pk_grc_oracle,
            &pf.pk_grc_eval_pf,
        ) {
            println!("pk_grc verification failed");
            return false;
        }
        return true;
    }

    pub fn verify_evk(
        &mut self,
        pk: &rlwe::PublicKey,
        rlk: &rlwe::RelinKey,
        atk: Vec<&rlwe::AutomorphismKey>,
        pf: &EvkProof,
    ) -> bool {
        let level = self.params.rlwe.gadget.len();

        if !self
            .celpc_verifier
            .verify_batch(&pf.evk_oracle.commitment, &pf.evk_oracle.open_proof)
        {
            println!("pk_oracle verification failed");
            return false;
        }

        let ntt_chal = self.lin_check_challenge(&pf.ntt_oracle);
        let mut aut_chal = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            aut_chal.push(self.lin_check_challenge(&pf.s_aut_oracle[i]));
        }

        self.oracle.write_batch_polynomial_oracle(&pf.evk_oracle);
        self.oracle.write_lincheck_oracle(&pf.ntt_oracle);
        self.oracle.write_rowcheck_oracle(&pf.s_norm_oracle);
        self.oracle.write_genrowcheck_oracle(&pf.pk_grc_oracle);
        self.oracle.write_rowcheck_oracle(&pf.f_norm_oracle);
        for i in 0..level {
            self.oracle.write_genrowcheck_oracle(&pf.r0_grc_oracle[i]);
            self.oracle.write_genrowcheck_oracle(&pf.r1_grc_oracle[i]);
            self.oracle.write_genrowcheck_oracle(&pf.r2_grc_oracle[i]);
            self.oracle.write_rowcheck_oracle(&pf.erlk0_norm_oracle[i]);
            self.oracle.write_rowcheck_oracle(&pf.erlk1_norm_oracle[i]);
            self.oracle.write_rowcheck_oracle(&pf.erlk2_norm_oracle[i]);
        }
        for i in 0..atk.len() {
            self.oracle.write_lincheck_oracle(&pf.s_aut_oracle[i]);
            for j in 0..level {
                self.oracle.write_genrowcheck_oracle(&pf.a_grc_oracle[i][j]);
                self.oracle
                    .write_rowcheck_oracle(&pf.eatk_norm_oracle[i][j]);
            }
        }
        self.oracle.finalize();

        let alpha = self.oracle.read_range_bigint(&self.params.rlwe.q);
        let alpha_combine = self.oracle.read_range_bigint(&self.params.rlwe.q);

        if !self.celpc_verifier.verify_evaluation_batch(
            &alpha,
            &alpha_combine,
            &pf.evk_oracle.commitment,
            &pf.evk_eval_pf,
        ) {
            println!("pk_eval_pf verification failed");
            return false;
        }

        let s_coeffs_ecd_eval = pf.evk_eval_pf.y_batch[0].clone();
        let s_ntt_ecd_eval = pf.evk_eval_pf.y_batch[1].clone();
        let epk_coeffs_ecd_eval = pf.evk_eval_pf.y_batch[2].clone();
        let epk_ntt_ecd_eval = pf.evk_eval_pf.y_batch[3].clone();
        let f_coeffs_ecd_eval = pf.evk_eval_pf.y_batch[4].clone();
        let f_ntt_ecd_eval = pf.evk_eval_pf.y_batch[5].clone();
        let erlk0_coeffs_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + i].clone())
            .collect::<Vec<_>>();
        let erlk0_ntt_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + level + i].clone())
            .collect::<Vec<_>>();
        let erlk1_coeffs_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + 2 * level + i].clone())
            .collect::<Vec<_>>();
        let erlk1_ntt_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + 3 * level + i].clone())
            .collect::<Vec<_>>();
        let erlk2_coeffs_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + 4 * level + i].clone())
            .collect::<Vec<_>>();
        let erlk2_ntt_ecd_eval = (0..level)
            .map(|i| pf.evk_eval_pf.y_batch[6 + 5 * level + i].clone())
            .collect::<Vec<_>>();
        let sk_d_ntt_ecd_eval = (0..atk.len())
            .map(|i| pf.evk_eval_pf.y_batch[6 + 6 * level + i].clone())
            .collect::<Vec<_>>();
        let mut eatk_coeffs_ecd_eval = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            eatk_coeffs_ecd_eval.push(
                (0..level)
                    .map(|j| {
                        pf.evk_eval_pf.y_batch[6 + 6 * level + atk.len() + i * level + j].clone()
                    })
                    .collect::<Vec<_>>(),
            );
        }
        let mut eatk_ntt_ecd_eval = Vec::with_capacity(atk.len());
        for i in 0..atk.len() {
            eatk_ntt_ecd_eval.push(
                (0..level)
                    .map(|j| {
                        pf.evk_eval_pf.y_batch
                            [6 + 6 * level + atk.len() + atk.len() * level + i * level + j]
                            .clone()
                    })
                    .collect::<Vec<_>>(),
            );
        }

        let mut ntt_coeffs_eval =
            vec![&s_coeffs_ecd_eval, &epk_coeffs_ecd_eval, &f_coeffs_ecd_eval];
        ntt_coeffs_eval.append(&mut erlk0_coeffs_ecd_eval.iter().map(|p| p).collect());
        ntt_coeffs_eval.append(&mut erlk1_coeffs_ecd_eval.iter().map(|p| p).collect());
        ntt_coeffs_eval.append(&mut erlk2_coeffs_ecd_eval.iter().map(|p| p).collect());
        for i in 0..atk.len() {
            ntt_coeffs_eval.append(&mut eatk_coeffs_ecd_eval[i].iter().map(|p| p).collect());
        }
        let mut ntt_ntt_eval = vec![&s_ntt_ecd_eval, &epk_ntt_ecd_eval, &f_ntt_ecd_eval];
        ntt_ntt_eval.append(&mut erlk0_ntt_ecd_eval.iter().map(|p| p).collect());
        ntt_ntt_eval.append(&mut erlk1_ntt_ecd_eval.iter().map(|p| p).collect());
        ntt_ntt_eval.append(&mut erlk2_ntt_ecd_eval.iter().map(|p| p).collect());
        for i in 0..atk.len() {
            ntt_ntt_eval.append(&mut eatk_ntt_ecd_eval[i].iter().map(|p| p).collect());
        }
        if !self.lin_check(
            &alpha,
            &alpha_combine,
            &ntt_coeffs_eval,
            &ntt_ntt_eval,
            &ntt_chal,
            &pf.ntt_oracle,
            &pf.ntt_eval_pf,
        ) {
            println!("ntt verification failed");
            return false;
        }

        let ternary_check_circuit = BigMultiVariatePoly {
            coeffs: vec![(Integer::from(1), vec![3]), (Integer::from(-1), vec![1])],
            max_degree: 3,
        };
        if !self.row_check(
            &alpha,
            &[&s_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.s_norm_oracle,
            &pf.s_norm_eval_pf,
        ) {
            println!("s_norm verification failed");
            return false;
        }

        let p_ntt_ecd = self.encoder.encode(&pk.p_ntt);
        let upk_ntt_ecd = self.encoder.encode(&pk.u_ntt);
        let neg_one_ecd = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);

        let pk_circuit = PolyMultiVariatePoly {
            coeffs: vec![
                (p_ntt_ecd, vec![0, 0]),
                (upk_ntt_ecd, vec![1, 0]),
                (neg_one_ecd, vec![0, 1]),
            ],
            max_degree: 1,
        };
        if !self.gen_row_check(
            &alpha,
            &[&s_ntt_ecd_eval, &epk_ntt_ecd_eval],
            &pk_circuit,
            &pf.pk_grc_oracle,
            &pf.pk_grc_eval_pf,
        ) {
            println!("pk_grc verification failed");
            return false;
        }

        if !self.row_check(
            &alpha,
            &[&f_coeffs_ecd_eval],
            &ternary_check_circuit,
            &pf.f_norm_oracle,
            &pf.f_norm_eval_pf,
        ) {
            println!("f_norm verification failed");
            return false;
        }

        let neg_one_ecd = self
            .encoder
            .encode(&vec![Integer::from(-1); self.params.rlwe.n]);

        let mut gad_ecd = Vec::with_capacity(level);
        let mut neg_gad_ecd = Vec::with_capacity(level);
        for i in 0..level {
            let gad_ecd_i = self.encoder.encode(&vec![
                self.params.rlwe.gadget[i].clone();
                self.params.rlwe.n
            ]);
            let neg_gad_ecd_i = self.encoder.encode(&vec![
                -self.params.rlwe.gadget[i].clone();
                self.params.rlwe.n
            ]);

            gad_ecd.push(gad_ecd_i);
            neg_gad_ecd.push(neg_gad_ecd_i);
        }

        for i in 0..level {
            let r0_ntt_ecd = self.encoder.encode(&rlk.r0_ntt[i]);
            let r1_ntt_ecd = self.encoder.encode(&rlk.r1_ntt[i]);
            let r2_ntt_ecd = self.encoder.encode(&rlk.r2_ntt[i]);

            let urlk0_ecd = self.encoder.encode(&rlk.u0_ntt[i]);
            let urlk1_ecd = self.encoder.encode(&rlk.u1_ntt[i]);

            let r0_circuit = PolyMultiVariatePoly {
                coeffs: vec![
                    (r0_ntt_ecd, vec![0, 0]),
                    (urlk0_ecd.clone(), vec![1, 0]),
                    (neg_one_ecd.clone(), vec![0, 1]),
                ],
                max_degree: 1,
            };
            if !self.gen_row_check(
                &alpha,
                &[&s_ntt_ecd_eval, &erlk0_ntt_ecd_eval[i]],
                &r0_circuit,
                &pf.r0_grc_oracle[i],
                &pf.r0_grc_eval_pf[i],
            ) {
                println!("r0_grc verification failed");
                return false;
            }

            let r1_circuit = PolyMultiVariatePoly {
                coeffs: vec![
                    (r1_ntt_ecd, vec![0, 0, 0]),
                    (urlk0_ecd.clone(), vec![1, 0, 0]),
                    (neg_gad_ecd[i].clone(), vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };
            if !self.gen_row_check(
                &alpha,
                &[&f_ntt_ecd_eval, &s_ntt_ecd_eval, &erlk1_ntt_ecd_eval[i]],
                &r1_circuit,
                &pf.r1_grc_oracle[i],
                &pf.r1_grc_eval_pf[i],
            ) {
                println!("r1_grc verification failed");
                return false;
            }

            let r2_circuit = PolyMultiVariatePoly {
                coeffs: vec![
                    (r2_ntt_ecd, vec![0, 0, 0]),
                    (urlk1_ecd.clone(), vec![1, 0, 0]),
                    (gad_ecd[i].clone(), vec![0, 1, 0]),
                    (neg_one_ecd.clone(), vec![0, 0, 1]),
                ],
                max_degree: 1,
            };
            if !self.gen_row_check(
                &alpha,
                &[&s_ntt_ecd_eval, &f_ntt_ecd_eval, &erlk2_ntt_ecd_eval[i]],
                &r2_circuit,
                &pf.r2_grc_oracle[i],
                &pf.r2_grc_eval_pf[i],
            ) {
                println!("r2_grc verification failed");
                return false;
            }

            if !self.row_check(
                &alpha,
                &[&erlk0_coeffs_ecd_eval[i]],
                &ternary_check_circuit,
                &pf.erlk0_norm_oracle[i],
                &pf.erlk0_norm_eval_pf[i],
            ) {
                println!("erlk0_norm verification failed");
                return false;
            }

            if !self.row_check(
                &alpha,
                &[&erlk1_coeffs_ecd_eval[i]],
                &ternary_check_circuit,
                &pf.erlk1_norm_oracle[i],
                &pf.erlk1_norm_eval_pf[i],
            ) {
                println!("erlk1_norm verification failed");
                return false;
            }

            if !self.row_check(
                &alpha,
                &[&erlk2_coeffs_ecd_eval[i]],
                &ternary_check_circuit,
                &pf.erlk2_norm_oracle[i],
                &pf.erlk2_norm_eval_pf[i],
            ) {
                println!("erlk2_norm verification failed");
                return false;
            }
        }

        for i in 0..atk.len() {
            if !self.lin_check(
                &alpha,
                &alpha_combine,
                &[&s_ntt_ecd_eval],
                &[&sk_d_ntt_ecd_eval[i]],
                &aut_chal[i],
                &pf.s_aut_oracle[i],
                &pf.s_aut_eval_pf[i],
            ) {
                println!("s_aut verification failed");
                return false;
            }

            for j in 0..level {
                let a_ntt_ecd = self.encoder.encode(&atk[i].a_ntt[j]);
                let uatk_ntt_ecd = self.encoder.encode(&atk[i].u_ntt[j]);

                let a_circuit = PolyMultiVariatePoly {
                    coeffs: vec![
                        (a_ntt_ecd, vec![0, 0, 0]),
                        (uatk_ntt_ecd, vec![1, 0, 0]),
                        (neg_gad_ecd[j].clone(), vec![0, 1, 0]),
                        (neg_one_ecd.clone(), vec![0, 0, 1]),
                    ],
                    max_degree: 1,
                };

                if !self.gen_row_check(
                    &alpha,
                    &[
                        &s_ntt_ecd_eval,
                        &sk_d_ntt_ecd_eval[i],
                        &eatk_ntt_ecd_eval[i][j],
                    ],
                    &a_circuit,
                    &pf.a_grc_oracle[i][j],
                    &pf.a_grc_eval_pf[i][j],
                ) {
                    println!("a_grc verification failed");
                    return false;
                }

                if !self.row_check(
                    &alpha,
                    &[&eatk_coeffs_ecd_eval[i][j]],
                    &ternary_check_circuit,
                    &pf.eatk_norm_oracle[i][j],
                    &pf.eatk_norm_eval_pf[i][j],
                ) {
                    println!("eatk_norm verification failed");
                    return false;
                }
            }
        }

        return true;
    }
}

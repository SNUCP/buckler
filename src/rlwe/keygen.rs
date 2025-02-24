use crate::csprng::UniformSampler;

use super::{NegacyclicTransformer, Parameters};
use rand::{seq::SliceRandom, thread_rng};
use rug::{Assign, Integer};

pub struct SecretKey {
    pub coeffs: Vec<Integer>,
    pub ntt: Vec<Integer>,
}

pub struct Ciphertext {
    pub u_coeffs: Vec<Integer>,
    pub u_ntt: Vec<Integer>,

    pub c_coeffs: Vec<Integer>,
    pub c_ntt: Vec<Integer>,

    pub m_coeffs: Vec<Integer>,
    pub m_ntt: Vec<Integer>,

    pub e_coeffs: Vec<Integer>,
    pub e_ntt: Vec<Integer>,
}

pub struct PkCiphertext {
    pub u_coeffs: Vec<Integer>,
    pub u_ntt: Vec<Integer>,

    pub c_coeffs: Vec<Integer>,
    pub c_ntt: Vec<Integer>,

    pub f_coeffs: Vec<Integer>,
    pub f_ntt: Vec<Integer>,

    pub e0_coeffs: Vec<Integer>,
    pub e0_ntt: Vec<Integer>,

    pub e1_coeffs: Vec<Integer>,
    pub e1_ntt: Vec<Integer>,

    pub m_coeffs: Vec<Integer>,
    pub m_ntt: Vec<Integer>,

    pub delta: Integer,
}

pub struct PartialDec {
    pub f_coeffs: Vec<Integer>,
    pub f_ntt: Vec<Integer>,

    pub u_coeffs: Vec<Integer>,
    pub u_ntt: Vec<Integer>,

    pub e_coeffs: Vec<Integer>,
    pub e_ntt: Vec<Integer>,

    pub d_coeffs: Vec<Integer>,
    pub d_ntt: Vec<Integer>,
}

pub struct PublicKey {
    pub u_coeffs: Vec<Integer>,
    pub u_ntt: Vec<Integer>,

    pub p_coeffs: Vec<Integer>,
    pub p_ntt: Vec<Integer>,

    pub epk_coeffs: Vec<Integer>,
    pub epk_ntt: Vec<Integer>,
}

pub struct RelinKey {
    pub r0_coeffs: Vec<Vec<Integer>>,
    pub r0_ntt: Vec<Vec<Integer>>,
    pub r1_coeffs: Vec<Vec<Integer>>,
    pub r1_ntt: Vec<Vec<Integer>>,
    pub r2_coeffs: Vec<Vec<Integer>>,
    pub r2_ntt: Vec<Vec<Integer>>,

    pub u0_coeffs: Vec<Vec<Integer>>,
    pub u0_ntt: Vec<Vec<Integer>>,
    pub u1_coeffs: Vec<Vec<Integer>>,
    pub u1_ntt: Vec<Vec<Integer>>,

    pub e0_coeffs: Vec<Vec<Integer>>,
    pub e0_ntt: Vec<Vec<Integer>>,
    pub e1_coeffs: Vec<Vec<Integer>>,
    pub e1_ntt: Vec<Vec<Integer>>,
    pub e2_coeffs: Vec<Vec<Integer>>,
    pub e2_ntt: Vec<Vec<Integer>>,

    pub f_coeffs: Vec<Integer>,
    pub f_ntt: Vec<Integer>,
}

pub struct AutomorphismKey {
    pub a_coeffs: Vec<Vec<Integer>>,
    pub a_ntt: Vec<Vec<Integer>>,

    pub u_coeffs: Vec<Vec<Integer>>,
    pub u_ntt: Vec<Vec<Integer>>,

    pub e_coeffs: Vec<Vec<Integer>>,
    pub e_ntt: Vec<Vec<Integer>>,

    pub sk_d_ntt: Vec<Integer>,

    pub d: usize,
}

pub struct KeyGenerator<'a> {
    pub params: &'a Parameters,

    pub uniform_sampler: UniformSampler,
    pub transformer: NegacyclicTransformer,
}

impl<'a> KeyGenerator<'a> {
    pub fn new(params: &'a Parameters) -> Self {
        Self {
            params: params,
            uniform_sampler: UniformSampler::new(),
            transformer: NegacyclicTransformer::new(params.n, &params.q),
        }
    }

    /// Generates the secret key.
    pub fn gen_secret_key(&mut self) -> SecretKey {
        let mut sk = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.s_hamming_weight {
            sk[i] = Integer::from(1);
        }
        sk.shuffle(&mut thread_rng());

        let mut sk_ntt = sk.clone();
        self.transformer.ntt(&mut sk_ntt);

        return SecretKey {
            coeffs: sk,
            ntt: sk_ntt,
        };
    }

    pub fn gen_encryption(
        &mut self,
        sk: &SecretKey,
        m_ntt: &[Integer],
        delta: &Integer,
    ) -> Ciphertext {
        let mut a = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            a[i] = self.uniform_sampler.sample_range_bigint(&self.params.q);
        }
        let mut a_ntt = a.clone();
        self.transformer.ntt(&mut a_ntt);

        let mut e = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            e[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                    as i64)
                    - (1 << self.params.log_e_bound as i64),
            );
        }
        let mut e_ntt = e.clone();
        self.transformer.ntt(&mut e_ntt);

        let mut m_ntt = m_ntt.to_vec();
        for i in 0..self.params.n {
            m_ntt[i] *= delta;
            m_ntt[i].modulo_mut(&self.params.q);
        }
        let mut m_coeffs = m_ntt.clone();
        self.transformer.intt(&mut m_coeffs);

        let mut b_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            b_ntt[i].assign(-&a_ntt[i]);
            b_ntt[i] *= &sk.ntt[i];
            b_ntt[i] += &e_ntt[i];
            b_ntt[i] += &m_ntt[i];
            b_ntt[i].modulo_mut(&self.params.q);
        }
        let mut b = b_ntt.clone();
        self.transformer.intt(&mut b);

        return Ciphertext {
            u_coeffs: a,
            u_ntt: a_ntt,

            c_coeffs: b,
            c_ntt: b_ntt,

            m_coeffs: m_coeffs,
            m_ntt: m_ntt,

            e_coeffs: e,
            e_ntt,
        };
    }

    pub fn gen_pk_encryption(
        &mut self,
        pk: &PublicKey,
        m_ntt: &[Integer],
        delta: &Integer,
    ) -> PkCiphertext {
        let f_sk = self.gen_secret_key();
        let f_coeffs = f_sk.coeffs;
        let f_ntt = f_sk.ntt;

        let mut e0_coeffs = vec![Integer::ZERO; self.params.n];
        let mut e1_coeffs = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            e0_coeffs[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                    as i64)
                    - (1 << self.params.log_e_bound as i64),
            );
            e1_coeffs[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                    as i64)
                    - (1 << self.params.log_e_bound as i64),
            );
        }
        let mut e0_ntt = e0_coeffs.clone();
        self.transformer.ntt(&mut e0_ntt);
        let mut e1_ntt = e1_coeffs.clone();
        self.transformer.ntt(&mut e1_ntt);

        let mut c_ntt = vec![Integer::ZERO; self.params.n];
        let mut u_ntt = vec![Integer::ZERO; self.params.n];
        let m_ntt = m_ntt.to_vec();
        for i in 0..self.params.n {
            c_ntt[i].assign(&pk.p_ntt[i]);
            c_ntt[i] *= &f_ntt[i];
            c_ntt[i] += &e0_ntt[i];
            c_ntt[i] += delta.clone() * &m_ntt[i];
            c_ntt[i].modulo_mut(&self.params.q);

            u_ntt[i].assign(&pk.u_ntt[i]);
            u_ntt[i] *= &f_ntt[i];
            u_ntt[i] += &e1_ntt[i];
            u_ntt[i].modulo_mut(&self.params.q);
        }

        let mut c = c_ntt.clone();
        self.transformer.intt(&mut c);
        let mut u = u_ntt.clone();
        self.transformer.intt(&mut u);
        let mut m = m_ntt.clone();
        self.transformer.intt(&mut m);

        return PkCiphertext {
            u_coeffs: u,
            u_ntt: u_ntt,

            c_coeffs: c,
            c_ntt: c_ntt,

            f_coeffs: f_coeffs,
            f_ntt: f_ntt,

            e0_coeffs: e0_coeffs,
            e0_ntt: e0_ntt,

            e1_coeffs: e1_coeffs,
            e1_ntt: e1_ntt,

            m_coeffs: m,
            m_ntt: m_ntt,

            delta: delta.clone(),
        };
    }

    pub fn gen_dist_decryption(&mut self, sk: &SecretKey, ct: &PkCiphertext) -> PartialDec {
        let bdd = Integer::from(1) << 128;

        let f = self.gen_secret_key();
        let mut e_coeffs = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            e_coeffs[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                    as i64)
                    - (1 << self.params.log_e_bound as i64),
            );
        }
        let mut e_ntt = e_coeffs.clone();
        self.transformer.ntt(&mut e_ntt);

        let mut u_coeffs = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            u_coeffs[i] = self.uniform_sampler.sample_range_bigint(&bdd);
        }
        let mut u_ntt = u_coeffs.clone();
        self.transformer.ntt(&mut u_ntt);

        let mut ef_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            ef_ntt[i].assign(&u_ntt[i]);
            ef_ntt[i] *= &f.ntt[i];
            ef_ntt[i] += &e_ntt[i];
            ef_ntt[i].modulo_mut(&self.params.q);
        }
        let mut ef_coeffs = ef_ntt.clone();
        self.transformer.intt(&mut ef_coeffs);

        let q_half = self.params.q.clone() >> 1;
        for i in 0..self.params.n {
            if &ef_coeffs[i] > &q_half {
                ef_coeffs[i] -= &self.params.q;
            }
            ef_coeffs[i] %= &bdd;
        }
        ef_ntt.clone_from(&ef_coeffs);
        self.transformer.ntt(&mut ef_ntt);

        let mut d_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            d_ntt[i].assign(&ct.c_ntt[i]);
            d_ntt[i] *= &sk.ntt[i];
            d_ntt[i] += &ef_ntt[i];
            d_ntt[i].modulo_mut(&self.params.q);
        }
        let mut d_coeffs = d_ntt.clone();
        self.transformer.intt(&mut d_coeffs);

        return PartialDec {
            f_coeffs: f.coeffs,
            f_ntt: f.ntt,

            u_coeffs: u_coeffs,
            u_ntt: u_ntt,

            e_coeffs: e_coeffs,
            e_ntt: e_ntt,

            d_coeffs: d_coeffs,
            d_ntt: d_ntt,
        };
    }

    pub fn gen_public_key(&mut self, sk: &SecretKey) -> PublicKey {
        let pk = self.gen_encryption(sk, &vec![Integer::ZERO; self.params.n], Integer::ONE);
        return PublicKey {
            u_coeffs: pk.u_coeffs,
            u_ntt: pk.u_ntt,

            p_coeffs: pk.c_coeffs,
            p_ntt: pk.c_ntt,

            epk_coeffs: pk.e_coeffs,
            epk_ntt: pk.e_ntt,
        };
    }

    /// Generates the relinearization key.
    pub fn gen_relin_key(&mut self, sk: &SecretKey) -> RelinKey {
        let level = self.params.gadget.len();

        let mut r0_coeffs = Vec::with_capacity(level);
        let mut r0_ntt = Vec::with_capacity(level);
        let mut r1_coeffs = Vec::with_capacity(level);
        let mut r1_ntt = Vec::with_capacity(level);
        let mut r2_coeffs = Vec::with_capacity(level);
        let mut r2_ntt = Vec::with_capacity(level);

        let mut u0_coeffs = Vec::with_capacity(level);
        let mut u0_ntt = Vec::with_capacity(level);
        let mut u1_coeffs = Vec::with_capacity(level);
        let mut u1_ntt = Vec::with_capacity(level);

        let mut e0_coeffs = Vec::with_capacity(level);
        let mut e0_ntt = Vec::with_capacity(level);
        let mut e1_coeffs = Vec::with_capacity(level);
        let mut e1_ntt = Vec::with_capacity(level);
        let mut e2_coeffs = Vec::with_capacity(level);
        let mut e2_ntt = Vec::with_capacity(level);

        let f_sk = self.gen_secret_key();
        let f_coeffs = f_sk.coeffs;
        let f_ntt = f_sk.ntt;

        for i in 0..level {
            // (-u0s + e0, u0)
            let r0_enc = self.gen_encryption(sk, &vec![Integer::ZERO; self.params.n], Integer::ONE);
            u0_coeffs.push(r0_enc.u_coeffs);
            u0_ntt.push(r0_enc.u_ntt);
            e0_coeffs.push(r0_enc.e_coeffs);
            e0_ntt.push(r0_enc.e_ntt);
            r0_coeffs.push(r0_enc.c_coeffs);
            r0_ntt.push(r0_enc.c_ntt);

            // (-u1s -fg + e2, u1)
            let r2_enc = self.gen_encryption(sk, &f_ntt, &(-self.params.gadget[i].clone()));
            u1_coeffs.push(r2_enc.u_coeffs);
            u1_ntt.push(r2_enc.u_ntt);
            e2_coeffs.push(r2_enc.e_coeffs);
            e2_ntt.push(r2_enc.e_ntt);
            r2_coeffs.push(r2_enc.c_coeffs);
            r2_ntt.push(r2_enc.c_ntt);

            let mut e1_i = vec![Integer::ZERO; self.params.n];
            for j in 0..self.params.n {
                e1_i[j] = Integer::from(
                    (self
                        .uniform_sampler
                        .sample_range((1 << (self.params.log_e_bound + 1)) + 1)
                        as i64)
                        - (1 << self.params.log_e_bound as i64),
                );
            }
            let mut e1_ntt_i = e1_i.clone();
            self.transformer.ntt(&mut e1_ntt_i);

            // (-u0f + sg + e1, u0)
            let mut sg_ntt = sk.ntt.clone();
            for j in 0..self.params.n {
                sg_ntt[j] *= &self.params.gadget[i];
                sg_ntt[j].modulo_mut(&self.params.q);
            }
            let mut r1_ntt_i = vec![Integer::ZERO; self.params.n];
            for j in 0..self.params.n {
                r1_ntt_i[j].assign(-u0_ntt[i][j].clone());
                r1_ntt_i[j] *= &f_ntt[j];
                r1_ntt_i[j] += &sg_ntt[j];
                r1_ntt_i[j] += &e1_ntt_i[j];
                r1_ntt_i[j].modulo_mut(&self.params.q);
            }
            let mut r1_i = r1_ntt_i.clone();
            self.transformer.intt(&mut r1_i);

            r1_coeffs.push(r1_i);
            r1_ntt.push(r1_ntt_i);
            e1_coeffs.push(e1_i);
            e1_ntt.push(e1_ntt_i);
        }

        return RelinKey {
            r0_coeffs,
            r0_ntt,
            r1_coeffs,
            r1_ntt,
            r2_coeffs,
            r2_ntt,

            u0_coeffs,
            u0_ntt,
            u1_coeffs,
            u1_ntt,

            e0_coeffs,
            e0_ntt,
            e1_coeffs,
            e1_ntt,
            e2_coeffs,
            e2_ntt,

            f_coeffs: f_coeffs,
            f_ntt: f_ntt,
        };
    }

    /// Generates the automorphism key.
    pub fn gen_aut_key(&mut self, sk: &SecretKey, d: usize) -> AutomorphismKey {
        let level = self.params.gadget.len();

        let sk_d_ntt = self.transformer.automorphism(&sk.ntt, d);
        let mut sk_d = sk_d_ntt.clone();
        self.transformer.intt(&mut sk_d);

        let mut a_coeffs = Vec::with_capacity(level);
        let mut a_ntt = Vec::with_capacity(level);

        let mut u_coeffs = Vec::with_capacity(level);
        let mut u_ntt = Vec::with_capacity(level);

        let mut e_coeffs = Vec::with_capacity(level);
        let mut e_ntt = Vec::with_capacity(level);

        for i in 0..level {
            let a_enc = self.gen_encryption(sk, &sk_d_ntt, &self.params.gadget[i]);

            a_coeffs.push(a_enc.c_coeffs);
            a_ntt.push(a_enc.c_ntt);

            u_coeffs.push(a_enc.u_coeffs);
            u_ntt.push(a_enc.u_ntt);

            e_coeffs.push(a_enc.e_coeffs);
            e_ntt.push(a_enc.e_ntt);
        }

        return AutomorphismKey {
            a_coeffs,
            a_ntt,

            u_coeffs,
            u_ntt,

            e_coeffs,
            e_ntt,

            sk_d_ntt,
            d,
        };
    }
}

use crate::csprng::UniformSampler;

use super::{NegacyclicTransformer, Parameters};
use rug::{Assign, Integer};

pub struct SecretKey {
    pub coeffs: Vec<Integer>,
    pub ntt: Vec<Integer>,
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
    /// Legth 3
    pub r_coeffs: Vec<Vec<Vec<Integer>>>,
    /// Legth 3
    pub r_ntt: Vec<Vec<Vec<Integer>>>,

    /// Length 2
    pub u_coeffs: Vec<Vec<Vec<Integer>>>,
    /// Length 2
    pub u_ntt: Vec<Vec<Vec<Integer>>>,

    /// Length 3
    pub e_coeffs: Vec<Vec<Vec<Integer>>>,
    /// Length 3
    pub e_ntt: Vec<Vec<Vec<Integer>>>,

    /// Length 3
    pub f_coeffs: Vec<Integer>,
    /// Length 3
    pub f_ntt: Vec<Integer>,
}

pub struct AutomorphismKey {
    pub u_coeffs: Vec<Vec<Integer>>,
    pub u_ntt: Vec<Vec<Integer>>,

    pub a_coeffs: Vec<Vec<Integer>>,
    pub a_ntt: Vec<Vec<Integer>>,

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
        for i in 0..self.params.n {
            sk[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range(2 * self.params.s_bound + 1) as i64)
                    - (self.params.s_bound as i64),
            );
        }

        let mut sk_ntt = sk.clone();
        self.transformer.ntt(&mut sk_ntt);

        return SecretKey {
            coeffs: sk,
            ntt: sk_ntt,
        };
    }

    /// Generates the public key.
    pub fn gen_public_key(&mut self, sk: &SecretKey) -> PublicKey {
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
                    .sample_range(2 * self.params.e_bound + 1) as i64)
                    - (self.params.e_bound as i64),
            );
        }
        let mut e_ntt = e.clone();
        self.transformer.ntt(&mut e_ntt);

        let mut b_ntt = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            b_ntt[i].assign(-&a_ntt[i]);
            b_ntt[i] *= &sk.ntt[i];
            b_ntt[i] += &e_ntt[i];
            b_ntt[i].modulo_mut(&self.params.q);
        }
        let mut b = b_ntt.clone();
        self.transformer.intt(&mut b);

        return PublicKey {
            u_coeffs: a,
            u_ntt: a_ntt,

            p_coeffs: b,
            p_ntt: b_ntt,

            epk_coeffs: e,
            epk_ntt: e_ntt,
        };
    }

    /// Generates the relinearization key.
    pub fn gen_relin_key(&mut self, sk: &SecretKey) -> RelinKey {
        let level = self.params.gadget.len();

        let mut f_coeffs = vec![Integer::ZERO; self.params.n];
        for i in 0..self.params.n {
            f_coeffs[i] = Integer::from(
                (self
                    .uniform_sampler
                    .sample_range(2 * self.params.s_bound + 1) as i64)
                    - (self.params.s_bound as i64),
            );
        }
        let mut f_ntt = f_coeffs.clone();
        self.transformer.ntt(&mut f_ntt);

        let mut u_coeffs = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        let mut u_ntt = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        for i in 0..level {
            for j in 0..self.params.n {
                u_coeffs[0][i][j] = self.uniform_sampler.sample_range_bigint(&self.params.q);
                u_coeffs[1][i][j] = self.uniform_sampler.sample_range_bigint(&self.params.q);
            }
            u_ntt[0][i].clone_from(&u_coeffs[0][i]);
            self.transformer.ntt(&mut u_ntt[0][i]);
            u_ntt[1][i].clone_from(&u_coeffs[1][i]);
            self.transformer.ntt(&mut u_ntt[1][i]);
        }

        let mut e_coeffs = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        let mut e_ntt = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        for i in 0..level {
            for j in 0..self.params.n {
                e_coeffs[0][i][j] = Integer::from(
                    (self
                        .uniform_sampler
                        .sample_range(2 * self.params.e_bound + 1) as i64)
                        - (self.params.e_bound as i64),
                );
                e_coeffs[1][i][j] = Integer::from(
                    (self
                        .uniform_sampler
                        .sample_range(2 * self.params.e_bound + 1) as i64)
                        - (self.params.e_bound as i64),
                );
                e_coeffs[2][i][j] = Integer::from(
                    (self
                        .uniform_sampler
                        .sample_range(2 * self.params.e_bound + 1) as i64)
                        - (self.params.e_bound as i64),
                );
            }
            e_ntt[0][i].clone_from(&e_coeffs[0][i]);
            self.transformer.ntt(&mut e_ntt[0][i]);
            e_ntt[1][i].clone_from(&e_coeffs[1][i]);
            self.transformer.ntt(&mut e_ntt[1][i]);
            e_ntt[2][i].clone_from(&e_coeffs[2][i]);
            self.transformer.ntt(&mut e_ntt[2][i]);
        }

        let mut r_coeffs = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        let mut r_ntt = vec![vec![vec![Integer::ZERO; self.params.n]; level]; 3];
        let mut buf = Integer::ZERO;
        for j in 0..level {
            for k in 0..self.params.n {
                r_ntt[0][j][k].assign(-&u_ntt[0][j][k]);
                r_ntt[0][j][k] *= &sk.ntt[k];
                r_ntt[0][j][k] += &e_ntt[0][j][k];

                r_ntt[1][j][k].assign(-&u_ntt[0][j][k]);
                r_ntt[1][j][k] *= &f_ntt[k];
                buf.assign(&self.params.gadget[j]);
                buf *= &sk.ntt[k];
                r_ntt[1][j][k] += &buf;
                r_ntt[1][j][k] += &e_ntt[1][j][k];

                r_ntt[2][j][k].assign(-&u_ntt[1][j][k]);
                r_ntt[2][j][k] *= &sk.ntt[k];
                buf.assign(-&self.params.gadget[j]);
                buf *= &f_ntt[k];
                r_ntt[2][j][k] += &buf;
                r_ntt[2][j][k] += &e_ntt[2][j][k];

                r_ntt[0][j][k].modulo_mut(&self.params.q);
                r_ntt[1][j][k].modulo_mut(&self.params.q);
                r_ntt[2][j][k].modulo_mut(&self.params.q);
            }
            r_coeffs[0][j].clone_from(&r_ntt[0][j]);
            self.transformer.intt(&mut r_coeffs[0][j]);
            r_coeffs[1][j].clone_from(&r_ntt[1][j]);
            self.transformer.intt(&mut r_coeffs[1][j]);
            r_coeffs[2][j].clone_from(&r_ntt[2][j]);
            self.transformer.intt(&mut r_coeffs[2][j]);
        }

        return RelinKey {
            r_coeffs: r_coeffs,
            r_ntt: r_ntt,

            u_coeffs: u_coeffs,
            u_ntt: u_ntt,

            e_coeffs: e_coeffs,
            e_ntt: e_ntt,

            f_coeffs: f_coeffs,
            f_ntt: f_ntt,
        };
    }

    /// Generates the automorphism key.
    pub fn gen_aut_key(&mut self, sk: &SecretKey, d: usize) -> AutomorphismKey {
        let level = self.params.gadget.len();

        let mut u_coeffs = vec![vec![Integer::ZERO; self.params.n]; level];
        let mut u_ntt = vec![vec![Integer::ZERO; self.params.n]; level];
        for i in 0..level {
            for j in 0..self.params.n {
                u_coeffs[i][j] = self.uniform_sampler.sample_range_bigint(&self.params.q);
            }
            u_ntt[i].clone_from(&u_coeffs[i]);
            self.transformer.ntt(&mut u_ntt[i]);
        }

        let mut e_coeffs = vec![vec![Integer::ZERO; self.params.n]; level];
        let mut e_ntt = vec![vec![Integer::ZERO; self.params.n]; level];
        for i in 0..level {
            for j in 0..self.params.n {
                e_coeffs[i][j] = Integer::from(
                    (self
                        .uniform_sampler
                        .sample_range(2 * self.params.e_bound + 1) as i64)
                        - (self.params.e_bound as i64),
                );
            }
            e_ntt[i].clone_from(&e_coeffs[i]);
            self.transformer.ntt(&mut e_ntt[i]);
        }

        let sk_ntt_d = self.transformer.automorphism(&sk.ntt, d);
        let mut a_coeffs = vec![vec![Integer::ZERO; self.params.n]; level];
        let mut a_ntt = vec![vec![Integer::ZERO; self.params.n]; level];
        let mut buf = Integer::ZERO;
        for i in 0..level {
            for j in 0..self.params.n {
                a_ntt[i][j].assign(-&u_ntt[i][j]);
                a_ntt[i][j] *= &sk.ntt[j];

                buf.assign(&self.params.gadget[i]);
                buf *= &sk_ntt_d[j];
                a_ntt[i][j] += &buf;

                a_ntt[i][j] += &e_ntt[i][j];
                a_ntt[i][j].modulo_mut(&self.params.q);
            }
            a_coeffs[i].clone_from(&a_ntt[i]);
            self.transformer.intt(&mut a_coeffs[i]);
        }

        return AutomorphismKey {
            u_coeffs: u_coeffs,
            u_ntt: u_ntt,

            a_coeffs: a_coeffs,
            a_ntt: a_ntt,

            e_coeffs: e_coeffs,
            e_ntt: e_ntt,

            sk_d_ntt: sk_ntt_d,

            d: d,
        };
    }
}

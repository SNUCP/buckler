use crate::{celpc::*, BigPoly};
use rug::Integer;

#[derive(Clone)]
pub struct PolynomialOracle {
    pub commitment: PolynomialCommitment,
    pub open_proof: OpenProof,
}

#[derive(Clone)]
pub struct BatchPolynomialOracle {
    pub commitment: BatchPolynomialCommitment,
    pub open_proof: BatchOpenProof,
}

#[derive(Clone)]
pub struct RowCheckPoly {
    pub quo: BigPoly,
}

#[derive(Clone)]
pub struct RowCheckOracle {
    pub quo_oracle: PolynomialOracle,
}

#[derive(Clone)]
pub struct RowCheckEvalProof {
    pub quo_eval_pf: EvaluationProof,
}

#[derive(Clone)]
pub struct GenRowCheckPoly {
    pub quo: BigPoly,
}

#[derive(Clone)]
pub struct GenRowCheckOracle {
    pub quo_oracle: PolynomialOracle,
}

#[derive(Clone)]
pub struct GenRowCheckEvalProof {
    pub quo_eval_pf: EvaluationProof,
}

#[derive(Clone)]
pub struct NormCheckOracle {
    pub decomposed_oracle: BatchPolynomialOracle,
    pub rc_oracle: Vec<RowCheckOracle>,
    pub log_bound: usize,
}

#[derive(Clone)]
pub struct NormCheckEvalProof {
    pub decomposed_eval_pf: BatchEvaluationProof,
    pub rc_eval_pf: Vec<RowCheckEvalProof>,
}

#[derive(Clone)]
pub enum LinCheckType {
    NTT,
    Automorphism(usize),
}

#[derive(Clone)]
pub struct LinCheckPoly {
    pub g: BigPoly,
    pub quo: BigPoly,
    pub rem: BigPoly,
}

#[derive(Clone)]
pub struct LinCheckOracle {
    pub lin_type: LinCheckType,
    pub g_oracle: PolynomialOracle,
    pub mu: Integer,
    pub quo_rem_oracle: BatchPolynomialOracle,
}

#[derive(Clone)]
pub struct LinCheckEvalProof {
    pub g_eval_pf: EvaluationProof,
    pub quo_rem_eval_pf: BatchEvaluationProof,
}

#[derive(Clone)]
pub struct LinCheckChallenge {
    pub beta: Integer,
    pub v: Integer,
}

#[derive(Clone)]
pub struct PkEncProof {
    pub pkenc_oracle: BatchPolynomialOracle,
    pub pkenc_eval_pf: BatchEvaluationProof,

    pub ntt_oracle: LinCheckOracle,
    pub ntt_eval_pf: LinCheckEvalProof,

    pub c0_grc_oracle: GenRowCheckOracle,
    pub c0_grc_eval_pf: GenRowCheckEvalProof,
    pub c1_grc_oracle: GenRowCheckOracle,
    pub c1_grc_eval_pf: GenRowCheckEvalProof,

    pub e0_norm_oracle: RowCheckOracle,
    pub e0_norm_eval_pf: RowCheckEvalProof,
    pub e1_norm_oracle: RowCheckOracle,
    pub e1_norm_eval_pf: RowCheckEvalProof,
    pub f_norm_oracle: RowCheckOracle,
    pub f_norm_eval_pf: RowCheckEvalProof,
    pub m_norm_oracle: NormCheckOracle,
    pub m_norm_eval_pf: NormCheckEvalProof,
}

#[derive(Clone)]
pub struct DDecProof {
    pub ddec_oracle: BatchPolynomialOracle,
    pub ddec_eval_pf: BatchEvaluationProof,

    pub ntt_oracle: LinCheckOracle,
    pub ntt_eval_pf: LinCheckEvalProof,

    pub pk_grc_oracle: GenRowCheckOracle,
    pub pk_grc_eval_pf: GenRowCheckEvalProof,

    pub dd_grc_oracle: GenRowCheckOracle,
    pub dd_grc_eval_pf: GenRowCheckEvalProof,

    pub s_norm_oracle: RowCheckOracle,
    pub s_norm_eval_pf: RowCheckEvalProof,
    pub epk_norm_oracle: RowCheckOracle,
    pub epk_norm_eval_pf: RowCheckEvalProof,
    pub edd_norm_oracle: RowCheckOracle,
    pub edd_norm_eval_pf: RowCheckEvalProof,
    pub f_norm_oracle: RowCheckOracle,
    pub f_norm_eval_pf: RowCheckEvalProof,
    pub k_norm_oracle: NormCheckOracle,
    pub k_norm_eval_pf: NormCheckEvalProof,
}

#[derive(Clone)]
pub struct PkProof {
    pub pk_oracle: BatchPolynomialOracle,
    pub pk_eval_pf: BatchEvaluationProof,

    pub ntt_oracle: LinCheckOracle,
    pub ntt_eval_pf: LinCheckEvalProof,

    pub s_norm_oracle: RowCheckOracle,
    pub s_norm_eval_pf: RowCheckEvalProof,

    pub pk_grc_oracle: GenRowCheckOracle,
    pub pk_grc_eval_pf: GenRowCheckEvalProof,
}

#[derive(Clone)]
pub struct EvkProof {
    pub evk_oracle: BatchPolynomialOracle,
    pub evk_eval_pf: BatchEvaluationProof,

    pub ntt_oracle: LinCheckOracle,
    pub ntt_eval_pf: LinCheckEvalProof,

    pub s_norm_oracle: RowCheckOracle,
    pub s_norm_eval_pf: RowCheckEvalProof,

    pub pk_grc_oracle: GenRowCheckOracle,
    pub pk_grc_eval_pf: GenRowCheckEvalProof,

    pub r0_grc_oracle: Vec<GenRowCheckOracle>,
    pub r0_grc_eval_pf: Vec<GenRowCheckEvalProof>,
    pub r1_grc_oracle: Vec<GenRowCheckOracle>,
    pub r1_grc_eval_pf: Vec<GenRowCheckEvalProof>,
    pub r2_grc_oracle: Vec<GenRowCheckOracle>,
    pub r2_grc_eval_pf: Vec<GenRowCheckEvalProof>,

    pub f_norm_oracle: RowCheckOracle,
    pub f_norm_eval_pf: RowCheckEvalProof,
    pub erlk0_norm_oracle: Vec<RowCheckOracle>,
    pub erlk0_norm_eval_pf: Vec<RowCheckEvalProof>,
    pub erlk1_norm_oracle: Vec<RowCheckOracle>,
    pub erlk1_norm_eval_pf: Vec<RowCheckEvalProof>,
    pub erlk2_norm_oracle: Vec<RowCheckOracle>,
    pub erlk2_norm_eval_pf: Vec<RowCheckEvalProof>,

    pub s_aut_oracle: Vec<LinCheckOracle>,
    pub s_aut_eval_pf: Vec<LinCheckEvalProof>,
    pub eatk_norm_oracle: Vec<Vec<RowCheckOracle>>,
    pub eatk_norm_eval_pf: Vec<Vec<RowCheckEvalProof>>,
    pub a_grc_oracle: Vec<Vec<GenRowCheckOracle>>,
    pub a_grc_eval_pf: Vec<Vec<GenRowCheckEvalProof>>,
}

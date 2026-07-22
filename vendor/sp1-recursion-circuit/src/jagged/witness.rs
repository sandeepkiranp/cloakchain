use slop_algebra::AbstractField;
use slop_challenger::IopCtx;
use slop_jagged::{
    unzip_and_prefix_sums, JaggedLittlePolynomialVerifierParams, JaggedPcsProof,
    JaggedSumcheckEvalProof, PrefixSumsMaxLogRowCount,
};
use slop_multilinear::Point;
use sp1_primitives::{SP1ExtensionField, SP1Field};
use sp1_recursion_compiler::ir::Builder;

use crate::{
    basefold::{stacked::RecursiveStackedPcsProof, RecursiveBasefoldProof},
    witness::{WitnessWriter, Witnessable},
    CircuitConfig, SP1FieldConfigVariable,
};

use super::verifier::JaggedPcsProofVariable;

impl<C: CircuitConfig, T: Witnessable<C>> Witnessable<C> for JaggedSumcheckEvalProof<T> {
    type WitnessVariable = JaggedSumcheckEvalProof<T::WitnessVariable>;

    fn read(&self, builder: &mut Builder<C>) -> Self::WitnessVariable {
        JaggedSumcheckEvalProof {
            partial_sumcheck_proof: self.partial_sumcheck_proof.read(builder),
        }
    }

    fn write(&self, witness: &mut impl WitnessWriter<C>) {
        self.partial_sumcheck_proof.write(witness);
    }
}

impl<C: CircuitConfig, T: Witnessable<C>> Witnessable<C>
    for JaggedLittlePolynomialVerifierParams<T>
{
    type WitnessVariable = JaggedLittlePolynomialVerifierParams<T::WitnessVariable>;

    fn read(&self, builder: &mut Builder<C>) -> Self::WitnessVariable {
        JaggedLittlePolynomialVerifierParams {
            col_prefix_sums: self
                .col_prefix_sums
                .iter()
                .map(|x| (*x).read(builder))
                .collect::<Vec<_>>(),
        }
    }

    fn write(&self, witness: &mut impl WitnessWriter<C>) {
        for x in &self.col_prefix_sums {
            x.write(witness);
        }
    }
}

impl<GC, C, Proof> Witnessable<C> for JaggedPcsProof<GC, Proof>
where
    GC: IopCtx<F = SP1Field, EF = SP1ExtensionField> + SP1FieldConfigVariable<C>,
    C: CircuitConfig,
    Proof: Witnessable<
        C,
        WitnessVariable = RecursiveStackedPcsProof<
            RecursiveBasefoldProof<C, GC>,
            SP1Field,
            SP1ExtensionField,
        >,
    >,
    GC::Digest: Witnessable<C, WitnessVariable = GC::DigestVariable>,
{
    type WitnessVariable =
        JaggedPcsProofVariable<RecursiveBasefoldProof<C, GC>, GC::DigestVariable>;

    fn read(&self, builder: &mut Builder<C>) -> Self::WitnessVariable {
        let PrefixSumsMaxLogRowCount { row_counts, column_counts, usize_prefix_sums, log_m: _ } =
            unzip_and_prefix_sums(&self.row_counts_and_column_counts);

        let point_prefix_sums: Vec<Point<GC::F>> =
            usize_prefix_sums.iter().map(|&x| Point::from_usize(x, self.log_m + 1)).collect();
        let column_prefix_sums = point_prefix_sums.read(builder);
        let params = JaggedLittlePolynomialVerifierParams { col_prefix_sums: column_prefix_sums };

        let sumcheck_proof = self.sumcheck_proof.read(builder);
        let jagged_eval_proof = self.jagged_eval_proof.read(builder);
        let pcs_proof = self.pcs_proof.read(builder);

        let row_counts = row_counts
            .into_iter()
            .map(|x| x.into_iter().map(SP1Field::from_canonical_usize).collect::<Vec<_>>())
            .collect::<Vec<_>>()
            .read(builder);
        let original_commitments =
            self.merkle_tree_commitments.clone().into_iter().collect::<Vec<_>>().read(builder);
        let expected_eval = self.expected_eval.read(builder);

        JaggedPcsProofVariable {
            pcs_proof,
            sumcheck_proof,
            jagged_eval_proof,
            params,
            column_counts,
            row_counts,
            original_commitments,
            expected_eval,
        }
    }

    fn write(&self, witness: &mut impl WitnessWriter<C>) {
        let PrefixSumsMaxLogRowCount { usize_prefix_sums, log_m, .. } =
            unzip_and_prefix_sums(&self.row_counts_and_column_counts);

        let point_prefix_sums: Vec<Point<GC::F>> =
            usize_prefix_sums.iter().map(|&x| Point::from_usize(x, log_m + 1)).collect();
        let params = JaggedLittlePolynomialVerifierParams { col_prefix_sums: point_prefix_sums };
        params.write(witness);
        self.sumcheck_proof.write(witness);
        self.jagged_eval_proof.write(witness);
        self.pcs_proof.write(witness);
        self.row_counts_and_column_counts
            .clone()
            .into_iter()
            .map(|x| x.into_iter().map(|x| SP1Field::from_canonical_usize(x.0)).collect::<Vec<_>>())
            .collect::<Vec<_>>()
            .write(witness);
        self.merkle_tree_commitments.write(witness);
        self.expected_eval.write(witness);
    }
}

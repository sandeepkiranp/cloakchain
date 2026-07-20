use crate::builder::SP1RecursionAirBuilder;
use slop_air::{Air, AirBuilder, BaseAir, PairBuilder};
use slop_algebra::PrimeField32;
use slop_matrix::Matrix;
use sp1_derive::AlignedBorrow;
use sp1_hypercube::air::MachineAir;
use sp1_primitives::SP1Field;
use sp1_recursion_executor::{
    ExecutionRecord, Instruction, RecursionProgram, RecursionPublicValues, DIGEST_SIZE,
    RECURSIVE_PROOF_NUM_PV_ELTS,
};
use std::{
    borrow::{Borrow, BorrowMut},
    mem::MaybeUninit,
};

use super::mem::MemoryAccessColsChips;
use crate::chips::mem::MemoryAccessCols;

pub const NUM_PUBLIC_VALUES_COLS: usize = core::mem::size_of::<PublicValuesCols<u8>>();
pub const NUM_PUBLIC_VALUES_PREPROCESSED_COLS: usize =
    core::mem::size_of::<PublicValuesPreprocessedCols<u8>>();

pub const PUB_VALUES_LOG_HEIGHT: usize = 4;

#[derive(Default, Clone)]
pub struct PublicValuesChip;

/// The preprocessed columns for the CommitPVHash instruction.
#[derive(AlignedBorrow, Debug, Clone, Copy)]
#[repr(C)]
pub struct PublicValuesPreprocessedCols<T: Copy> {
    pub pv_idx: [T; DIGEST_SIZE],
    pub pv_mem: MemoryAccessColsChips<T>,
}

/// The cols for a CommitPVHash invocation.
#[derive(AlignedBorrow, Debug, Clone, Copy)]
#[repr(C)]
pub struct PublicValuesCols<T: Copy> {
    pub pv_element: T,
}

impl<F> BaseAir<F> for PublicValuesChip {
    fn width(&self) -> usize {
        NUM_PUBLIC_VALUES_COLS
    }
}

impl<F: PrimeField32> MachineAir<F> for PublicValuesChip {
    type Record = ExecutionRecord<F>;

    type Program = RecursionProgram<F>;

    fn name(&self) -> &'static str {
        "PublicValues"
    }

    fn generate_dependencies(&self, _: &Self::Record, _: &mut Self::Record) {
        // This is a no-op.
    }

    fn preprocessed_width(&self) -> usize {
        NUM_PUBLIC_VALUES_PREPROCESSED_COLS
    }

    fn num_rows(&self, _: &Self::Record) -> Option<usize> {
        Some(1 << PUB_VALUES_LOG_HEIGHT)
    }

    fn preprocessed_num_rows(&self, _program: &Self::Program) -> Option<usize> {
        Some(1 << PUB_VALUES_LOG_HEIGHT)
    }

    fn preprocessed_num_rows_with_instrs_len(&self, _: &Self::Program, _: usize) -> Option<usize> {
        Some(1 << PUB_VALUES_LOG_HEIGHT)
    }

    fn generate_preprocessed_trace_into(
        &self,
        program: &Self::Program,
        buffer: &mut [MaybeUninit<F>],
    ) {
        assert_eq!(
            std::any::TypeId::of::<F>(),
            std::any::TypeId::of::<SP1Field>(),
            "generate_preprocessed_trace only supports SP1Field field"
        );

        let padded_nb_rows = self.preprocessed_num_rows(program).unwrap();

        unsafe {
            let padding_size = padded_nb_rows * NUM_PUBLIC_VALUES_PREPROCESSED_COLS;
            core::ptr::write_bytes(buffer.as_mut_ptr(), 0, padding_size);
        }

        let buffer_ptr = buffer.as_mut_ptr() as *mut F;
        let values = unsafe {
            core::slice::from_raw_parts_mut(
                buffer_ptr,
                padded_nb_rows * NUM_PUBLIC_VALUES_PREPROCESSED_COLS,
            )
        };

        let commit_pv_hash_instrs = program
            .inner
            .iter()
            .filter_map(|instruction| {
                if let Instruction::CommitPublicValues(instr) = instruction.inner() {
                    Some(instr)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();

        if commit_pv_hash_instrs.len() != 1 {
            tracing::warn!("Expected exactly one CommitPVHash instruction.");
        }

        // We only take 1 commit pv hash instruction, since our air only checks for one public
        // values hash.
        for instr in commit_pv_hash_instrs.iter().take(1) {
            for (i, addr) in instr.pv_addrs.digest.iter().enumerate() {
                let start = i * NUM_PUBLIC_VALUES_PREPROCESSED_COLS;
                let end = (i + 1) * NUM_PUBLIC_VALUES_PREPROCESSED_COLS;
                let cols: &mut PublicValuesPreprocessedCols<F> = values[start..end].borrow_mut();
                cols.pv_idx[i] = F::one();
                cols.pv_mem = MemoryAccessCols { addr: *addr, mult: F::one() };
            }
        }
    }

    fn generate_trace_into(
        &self,
        input: &ExecutionRecord<F>,
        _: &mut ExecutionRecord<F>,
        buffer: &mut [MaybeUninit<F>],
    ) {
        assert_eq!(
            std::any::TypeId::of::<F>(),
            std::any::TypeId::of::<SP1Field>(),
            "generate_trace_into only supports SP1Field"
        );
        let padded_nb_rows = <PublicValuesChip as MachineAir<F>>::num_rows(self, input).unwrap();

        unsafe {
            let padding_size = padded_nb_rows * NUM_PUBLIC_VALUES_COLS;
            core::ptr::write_bytes(buffer.as_mut_ptr(), 0, padding_size);
        }

        let buffer_ptr = buffer.as_mut_ptr() as *mut F;
        let values = unsafe {
            core::slice::from_raw_parts_mut(buffer_ptr, padded_nb_rows * NUM_PUBLIC_VALUES_COLS)
        };

        for event in input.commit_pv_hash_events.iter().take(1) {
            for (idx, element) in event.public_values.digest.iter().enumerate() {
                let start = idx * NUM_PUBLIC_VALUES_COLS;
                let end = (idx + 1) * NUM_PUBLIC_VALUES_COLS;
                let cols: &mut PublicValuesCols<F> = values[start..end].borrow_mut();
                cols.pv_element = *element;
            }
        }
    }

    fn included(&self, _record: &Self::Record) -> bool {
        true
    }
}

impl<AB> Air<AB> for PublicValuesChip
where
    AB: SP1RecursionAirBuilder + PairBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &PublicValuesCols<AB::Var> = (*local).borrow();
        let prepr = builder.preprocessed();
        let local_prepr = prepr.row_slice(0);
        let local_prepr: &PublicValuesPreprocessedCols<AB::Var> = (*local_prepr).borrow();
        let pv = builder.public_values();
        let pv_elms: [AB::Expr; RECURSIVE_PROOF_NUM_PV_ELTS] =
            core::array::from_fn(|i| pv[i].into());
        let public_values: &RecursionPublicValues<AB::Expr> = pv_elms.as_slice().borrow();

        // Constrain mem read for the public value element.
        builder.receive_single(local_prepr.pv_mem.addr, local.pv_element, local_prepr.pv_mem.mult);

        for (i, pv_elm) in public_values.digest.iter().enumerate() {
            builder.when(local_prepr.pv_idx[i]).assert_eq(pv_elm.clone(), local.pv_element);
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::print_stdout)]

    use crate::{
        chips::{public_values::PublicValuesChip, test_fixtures},
        test::test_recursion_linear_program,
    };
    use rand::{rngs::StdRng, Rng, SeedableRng};
    use slop_algebra::AbstractField;

    use slop_challenger::IopCtx;
    use slop_matrix::Matrix;
    use sp1_core_machine::utils::setup_logger;
    use sp1_hypercube::air::MachineAir;
    use sp1_primitives::SP1GlobalContext;
    use sp1_recursion_executor::{
        instruction as instr, ExecutionRecord, MemAccessKind, RecursionPublicValues, DIGEST_SIZE,
        NUM_PV_ELMS_TO_HASH, RECURSIVE_PROOF_NUM_PV_ELTS,
    };
    use std::{array, borrow::Borrow};

    #[tokio::test]
    async fn prove_koalabear_circuit_public_values() {
        setup_logger();
        type F = <SP1GlobalContext as IopCtx>::F;

        let mut rng = StdRng::seed_from_u64(0xDEADBEEF);
        let mut random_felt = move || -> F { F::from_canonical_u32(rng.gen_range(0..1 << 16)) };
        let random_pv_elms: [F; RECURSIVE_PROOF_NUM_PV_ELTS] = array::from_fn(|_| random_felt());
        let public_values_a: [u32; RECURSIVE_PROOF_NUM_PV_ELTS] = array::from_fn(|i| i as u32);

        let mut instructions = Vec::new();
        // Allocate the memory for the public values hash.

        for i in 0..RECURSIVE_PROOF_NUM_PV_ELTS {
            let mult = (NUM_PV_ELMS_TO_HASH..NUM_PV_ELMS_TO_HASH + DIGEST_SIZE).contains(&i);
            instructions.push(instr::mem_block(
                MemAccessKind::Write,
                mult as u32,
                public_values_a[i],
                random_pv_elms[i].into(),
            ));
        }
        let public_values_a: &RecursionPublicValues<u32> = public_values_a.as_slice().borrow();
        instructions.push(instr::commit_public_values(public_values_a));

        test_recursion_linear_program(instructions).await;
    }

    #[tokio::test]
    async fn generate_trace() {
        let shard = test_fixtures::shard().await;
        let trace = PublicValuesChip.generate_trace(shard, &mut ExecutionRecord::default());
        assert_eq!(trace.height(), 16);
    }

    #[tokio::test]
    async fn generate_preprocessed_trace() {
        let program = &test_fixtures::program_with_input().await.0;
        let trace = PublicValuesChip.generate_preprocessed_trace(program).unwrap();
        assert_eq!(trace.height(), 16);
    }
}

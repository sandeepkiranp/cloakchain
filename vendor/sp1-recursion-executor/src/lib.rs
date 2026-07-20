pub mod analyzed;
mod block;
pub mod instruction;
mod memory;
mod opcode;
mod program;
mod public_values;
mod record;
pub mod shape;

pub use analyzed::AnalyzedInstruction;
pub use public_values::PV_DIGEST_NUM_WORDS;

// Avoid triggering annoying branch of thiserror derive macro.
use backtrace::Backtrace as Trace;
pub use block::Block;
use cfg_if::cfg_if;
pub use instruction::Instruction;
use instruction::{
    FieldEltType, HintAddCurveInstr, HintBitsInstr, HintExt2FeltsInstr, HintInstr, PrintInstr,
};
use itertools::Itertools;
use memory::*;
pub use opcode::*;
pub use program::*;
pub use public_values::{RecursionPublicValues, NUM_PV_ELMS_TO_HASH, RECURSIVE_PROOF_NUM_PV_ELTS};
pub use record::*;
use serde::{Deserialize, Serialize};
use slop_algebra::{
    AbstractExtensionField, AbstractField, ExtensionField, PrimeField32, PrimeField64,
};
use slop_maybe_rayon::prelude::*;
use slop_poseidon2::{Poseidon2, Poseidon2ExternalMatrixGeneral};
use slop_symmetric::{CryptographicPermutation, Permutation};
use sp1_derive::AlignedBorrow;
use sp1_hypercube::{
    operations::poseidon2::air::{external_linear_layer_mut, internal_linear_layer_mut},
    septic_curve::SepticCurve,
    septic_extension::SepticExtension,
    MachineRecord,
};
use std::{
    array,
    borrow::Borrow,
    cell::{RefCell, UnsafeCell},
    collections::{HashMap as DiagHashMap, VecDeque},
    fmt::Debug,
    io::{stdout, Write},
    iter::zip,
    marker::PhantomData,
    sync::{Arc, Mutex},
};
use thiserror::Error;
use tracing::debug_span;

/// The width of the Poseidon2 permutation.
pub const PERMUTATION_WIDTH: usize = 16;
pub const POSEIDON2_SBOX_DEGREE: u64 = 3;
pub const HASH_RATE: usize = 8;

/// The current verifier implementation assumes that we are using a 256-bit hash with 32-bit
/// elements.
pub const DIGEST_SIZE: usize = 8;

pub const NUM_BITS: usize = 31;

pub const D: usize = 4;

#[derive(
    AlignedBorrow, Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize, Default,
)]
#[repr(transparent)]
pub struct Address<F>(pub F);

impl<F: PrimeField64> Address<F> {
    #[inline]
    pub fn as_usize(&self) -> usize {
        self.0.as_canonical_u64() as usize
    }
}

// ─── Write-tracker diagnostic ─────────────────────────────────────────────────
// Set RECURSION_DIAG=1 to activate.  On a DivF out-of-domain panic, dumps:
//   1. The first INIT_DUMP_STEPS Mem::Write operations (proof input layout)
//   2. Last-write info for watched addresses around the crash site
//   3. Last 50 instructions before the crash
//
// Address 316465 is the SHARED DENOMINATOR for all DivF operations. It's written
// once at step 1 (from proof input) with value 0 for coinproof → crash at 174554.
// For VFY-G16 the same address has a non-zero value → no crash.
// Previous hypotheses (BN254 chips, Uint256MulMod) both FAILED — 316465 is still
// 0 after adding both. Need to identify the actual chip via the init dump below.

// How many initial Mem::Write steps to capture for the proof-input layout dump.
const INIT_DUMP_STEPS: usize = 300;

struct ExecDiag {
    active: bool,
    step: usize,
    last_write: DiagHashMap<usize, (usize, String)>,
    trace: VecDeque<String>,
    // All Mem::Write ops in the first INIT_DUMP_STEPS steps: (step, addr, val_u32)
    init_mem_writes: Vec<(usize, usize, u32)>,
    // Hint writes to watched addresses: (hint_seq, addr, [v0,v1,v2,v3])
    hint_watched: Vec<(usize, usize, [u32; 4])>,
    hint_seq: usize,
}

// Addresses to watch: the failing in2 (316465) ± 5 neighbourhood, plus crash in1/out.
const DIAG_WATCHED: &[usize] = &[
    316460, 316461, 316462, 316463, 316464, 316465, 316466, 316467, 316468, 316469, 316470,
    2013019, 2013020,
];
const DIAG_TRACE_LEN: usize = 100;

impl ExecDiag {
    fn new() -> Self {
        let active =
            std::env::var("RECURSION_DIAG").map(|v| v == "1").unwrap_or(false);
        Self {
            active,
            step: 0,
            last_write: DiagHashMap::new(),
            trace: VecDeque::with_capacity(DIAG_TRACE_LEN + 1),
            init_mem_writes: Vec::new(),
            hint_watched: Vec::new(),
            hint_seq: 0,
        }
    }

    fn record(&mut self, dest_addr: usize, summary: String) {
        if !self.active {
            return;
        }
        self.step += 1;
        if self.trace.len() >= DIAG_TRACE_LEN {
            self.trace.pop_front();
        }
        self.trace.push_back(format!("[{:>10}] {}", self.step, &summary));
        if DIAG_WATCHED.contains(&dest_addr) {
            self.last_write.insert(dest_addr, (self.step, summary));
        }
    }

    // Called for every Mem::Write, before step is incremented.
    fn record_mem_write(&mut self, addr: usize, val: u32) {
        if !self.active {
            return;
        }
        // step has already been incremented by record() just before this call
        if self.step <= INIT_DUMP_STEPS {
            self.init_mem_writes.push((self.step, addr, val));
        }
    }

    // Called for every Hint write; tracks watched addresses so we know if a Hint
    // overwrites a Mem::Write-initialized cell with the actual witness value.
    fn record_hint_write(&mut self, addr: usize, block: [u32; 4]) {
        if !self.active { return; }
        self.hint_seq += 1;
        if DIAG_WATCHED.contains(&addr) {
            self.hint_watched.push((self.hint_seq, addr, block));
        }
    }

    // Called at the END of a successful run to show the proof-input layout.
    fn dump_init(&self) {
        if !self.active {
            return;
        }
        eprintln!("\n[RECURSION-DIAG-INIT] ── First {} Mem::Writes (proof input layout, SUCCESS) ──",
            INIT_DUMP_STEPS);
        for &(s, addr, val) in &self.init_mem_writes {
            let marker = if addr == 316465 { " ◄◄◄ addr316465" } else { "" };
            eprintln!("[RECURSION-DIAG-INIT]   step={s:>6}  addr={addr:>8}  val={val:#010x}{marker}");
        }
        eprintln!("[RECURSION-DIAG-INIT]   ({} writes captured, {} total steps)",
            self.init_mem_writes.len(), self.step);
        self.dump_hint_watched("[RECURSION-DIAG-INIT]");
        eprintln!("[RECURSION-DIAG-INIT] ──────────────────────────────────────────────\n");
    }

    fn dump_hint_watched(&self, prefix: &str) {
        eprintln!("{prefix} ── Hint writes to watched addrs ({} total hints) ──", self.hint_seq);
        if self.hint_watched.is_empty() {
            eprintln!("{prefix}   (none — watched addresses never written by Hint)");
        }
        for &(seq, addr, [v0, v1, v2, v3]) in &self.hint_watched {
            eprintln!("{prefix}   hint#{seq:>8}  addr={addr:>8}  \
                block=({v0:#010x},{v1:#010x},{v2:#010x},{v3:#010x})");
        }
    }

    fn dump(&self, label: &str) {
        if !self.active {
            return;
        }
        eprintln!("\n[RECURSION-DIAG] ════════════════════════════════════════════════════");
        eprintln!("[RECURSION-DIAG] post-mortem: {label}  (at step {})", self.step);

        // ── Init mem-write dump: proof input layout ───────────────────────────
        eprintln!("[RECURSION-DIAG] ── First {} Mem::Writes (proof input layout) ──", INIT_DUMP_STEPS);
        for &(s, addr, val) in &self.init_mem_writes {
            let marker = if addr == 316465 { " ◄◄◄ TARGET" } else { "" };
            eprintln!("[RECURSION-DIAG]   step={s:>6}  addr={addr:>8}  val={val:#010x}{marker}");
        }
        eprintln!("[RECURSION-DIAG]   ({} writes captured)", self.init_mem_writes.len());
        self.dump_hint_watched("[RECURSION-DIAG]");

        // ── Watched address summary ───────────────────────────────────────────
        eprintln!("[RECURSION-DIAG] ── Watched address last-write summary ──");
        for &addr in DIAG_WATCHED {
            match self.last_write.get(&addr) {
                Some((s, d)) => {
                    eprintln!("[RECURSION-DIAG]   addr={addr:>8}  last_write_step={s:>10}  {d}")
                }
                None => eprintln!("[RECURSION-DIAG]   addr={addr:>8}  NEVER WRITTEN"),
            }
        }

        // ── Final 50 instructions ─────────────────────────────────────────────
        let show = self.trace.len().min(50);
        eprintln!("[RECURSION-DIAG] ── last {show} instructions (most-recent first) ──");
        for line in self.trace.iter().rev().take(show) {
            eprintln!("[RECURSION-DIAG]   {line}");
        }
        eprintln!("[RECURSION-DIAG] ════════════════════════════════════════════════════\n");
    }
}

thread_local! {
    static EXEC_DIAG: RefCell<ExecDiag> = RefCell::new(ExecDiag::new());
}

// -------------------------------------------------------------------------------------------------

/// The inputs and outputs to an operation of the base field ALU.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct BaseAluIo<V> {
    pub out: V,
    pub in1: V,
    pub in2: V,
}

pub type BaseAluEvent<F> = BaseAluIo<F>;

/// An instruction invoking the extension field ALU.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct BaseAluInstr<F> {
    pub opcode: BaseAluOpcode,
    pub mult: F,
    pub addrs: BaseAluIo<Address<F>>,
}

// -------------------------------------------------------------------------------------------------

/// The inputs and outputs to an operation of the extension field ALU.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct ExtAluIo<V> {
    pub out: V,
    pub in1: V,
    pub in2: V,
}

pub type ExtAluEvent<F> = ExtAluIo<Block<F>>;

/// An instruction invoking the extension field ALU.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct ExtAluInstr<F> {
    pub opcode: ExtAluOpcode,
    pub mult: F,
    pub addrs: ExtAluIo<Address<F>>,
}

// -------------------------------------------------------------------------------------------------

/// The inputs and outputs to the manual memory management/memory initialization table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct MemIo<V> {
    pub inner: V,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemInstr<F> {
    pub addrs: MemIo<Address<F>>,
    pub vals: MemIo<Block<F>>,
    pub mult: F,
    pub kind: MemAccessKind,
}

pub type MemEvent<F> = MemIo<Block<F>>;

// -------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MemAccessKind {
    Read,
    Write,
}

/// The inputs and outputs to a Poseidon2 permutation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2Io<V> {
    pub input: [V; PERMUTATION_WIDTH],
    pub output: [V; PERMUTATION_WIDTH],
}

/// An instruction invoking the Poseidon2 permutation.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2Instr<F> {
    pub addrs: Poseidon2Io<Address<F>>,
    pub mults: [F; PERMUTATION_WIDTH],
}

pub type Poseidon2Event<F> = Poseidon2Io<F>;

/// The inputs and outputs to a Poseidon2 permutation linear layers.
/// The `4` here is calculated from `PERMUTATION_WIDTH / D`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2LinearLayerIo<V> {
    pub input: [V; 4],
    pub output: [V; 4],
}

/// An instruction invoking the Poseidon2 permutation linear layers.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2LinearLayerInstr<F> {
    pub addrs: Poseidon2LinearLayerIo<Address<F>>,
    pub mults: [F; 4],
    pub external: bool,
}

pub type Poseidon2LinearLayerEvent<F> = Poseidon2LinearLayerIo<Block<F>>;

/// The inputs and outputs to an SBOX operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2SBoxIo<V> {
    pub input: V,
    pub output: V,
}

/// An instruction invoking the SBOX operation.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct Poseidon2SBoxInstr<F> {
    pub addrs: Poseidon2SBoxIo<Address<F>>,
    pub mults: F,
    pub external: bool,
}

pub type Poseidon2SBoxEvent<F> = Poseidon2SBoxIo<Block<F>>;

/// An instruction invoking the ext2felt or felt2ext operation.
/// This `5` is derived from `D + 1`. The first address is the extension, and the rest are felts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct ExtFeltInstr<F> {
    pub addrs: [Address<F>; 5],
    pub mults: [F; 5],
    pub ext2felt: bool,
}

/// An event recording an ext2felt or felt2ext operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct ExtFeltEvent<F> {
    pub input: Block<F>,
}

/// The inputs and outputs to a select operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct SelectIo<V> {
    pub bit: V,
    pub out1: V,
    pub out2: V,
    pub in1: V,
    pub in2: V,
}

/// An instruction invoking the select operation.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct SelectInstr<F> {
    pub addrs: SelectIo<Address<F>>,
    pub mult1: F,
    pub mult2: F,
}

/// The event encoding the inputs and outputs of a select operation.
pub type SelectEvent<F> = SelectIo<F>;

/// The inputs and outputs to the operations for prefix sum checks.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrefixSumChecksIo<V> {
    pub zero: V,
    pub one: V,
    pub x1: Vec<V>,
    pub x2: Vec<V>,
    pub accs: Vec<V>,
    pub field_accs: Vec<V>,
}

/// An instruction invoking the PrefixSumChecks operation.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PrefixSumChecksInstr<F> {
    pub addrs: PrefixSumChecksIo<Address<F>>,
    pub acc_mults: Vec<F>,
    pub field_acc_mults: Vec<F>,
}

/// The event encoding the inputs and outputs of an PrefixSumChecks operation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[repr(C)]
pub struct PrefixSumChecksEvent<F> {
    pub x1: F,
    pub x2: Block<F>,
    pub zero: F,
    pub one: Block<F>,
    pub acc: Block<F>,
    pub new_acc: Block<F>,
    pub field_acc: F,
    pub new_field_acc: F,
}

/// An instruction that will save the public values to the execution record and will commit to
/// it's digest.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct CommitPublicValuesInstr<F> {
    pub pv_addrs: RecursionPublicValues<Address<F>>,
}

/// The event for committing to the public values.
#[derive(Clone, Copy, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct CommitPublicValuesEvent<F> {
    pub public_values: RecursionPublicValues<F>,
}

type Perm<F, Diffusion> = Poseidon2<
    F,
    Poseidon2ExternalMatrixGeneral,
    Diffusion,
    PERMUTATION_WIDTH,
    POSEIDON2_SBOX_DEGREE,
>;

/// TODO fully document.
/// Taken from [`sp1_recursion_executor::executor::Runtime`].
/// Many missing things (compared to the old `Runtime`) will need to be implemented.
pub struct Executor<'a, F: PrimeField32, EF: ExtensionField<F>, Diffusion> {
    /// The program.
    pub program: Arc<RecursionProgram<F>>,

    /// Memory. From canonical usize of an Address to a MemoryEntry.
    pub memory: MemVec<F>,

    /// The execution record.
    pub record: ExecutionRecord<F>,

    pub witness_stream: VecDeque<Block<F>>,

    /// The stream that print statements write to.
    pub debug_stdout: Box<dyn Write + Send + 'a>,

    /// Entries for dealing with the Poseidon2 hash state.
    perm: Option<Perm<F, Diffusion>>,

    _marker_ef: PhantomData<EF>,

    _marker_diffusion: PhantomData<Diffusion>,
}

#[derive(Error, Debug)]
pub enum RuntimeError<F: Debug, EF: Debug> {
    #[error(
        "attempted to perform base field division {in1:?}/{in2:?}\n\
        \tin instruction {instr:#?}\n\
        \tnearest backtrace:\n{trace:#?}"
    )]
    DivFOutOfDomain { in1: F, in2: F, instr: BaseAluInstr<F>, trace: Option<Trace> },
    #[error(
        "attempted to perform extension field division {in1:?}/{in2:?}\n\
        \tin instruction {instr:#?}\n\
        \tnearest backtrace:\n{trace:#?}"
    )]
    DivEOutOfDomain { in1: EF, in2: EF, instr: ExtAluInstr<F>, trace: Option<Trace> },
    #[error("failed to print to `debug_stdout`: {0}")]
    DebugPrint(#[from] std::io::Error),
    #[error("attempted to read from empty witness stream")]
    EmptyWitnessStream,
}

impl<F: PrimeField32, EF: ExtensionField<F>, Diffusion> Executor<'_, F, EF, Diffusion>
where
    Poseidon2<
        F,
        Poseidon2ExternalMatrixGeneral,
        Diffusion,
        PERMUTATION_WIDTH,
        POSEIDON2_SBOX_DEGREE,
    >: CryptographicPermutation<[F; PERMUTATION_WIDTH]>,
{
    pub fn new(
        program: Arc<RecursionProgram<F>>,
        perm: Poseidon2<
            F,
            Poseidon2ExternalMatrixGeneral,
            Diffusion,
            PERMUTATION_WIDTH,
            POSEIDON2_SBOX_DEGREE,
        >,
    ) -> Self {
        let record = ExecutionRecord::<F> { program: program.clone(), ..Default::default() };
        let memory = MemVec::with_capacity(program.total_memory);
        Self {
            program,
            memory,
            record,
            witness_stream: VecDeque::new(),
            debug_stdout: Box::new(stdout()),
            perm: Some(perm),
            _marker_ef: PhantomData,
            _marker_diffusion: PhantomData,
        }
    }

    pub fn print_stats(&self) {
        if tracing::event_enabled!(tracing::Level::DEBUG) {
            let mut stats = self.record.stats().into_iter().collect::<Vec<_>>();
            stats.sort_unstable();
            tracing::debug!("total events: {}", stats.iter().map(|(_, v)| *v).sum::<usize>());
            for (k, v) in stats {
                tracing::debug!("  {k}: {v}");
            }
        }
    }

    /// # Safety
    ///
    /// Safety is guaranteed if calls to this function (with the given `env` argument) obey the
    /// happens-before relation defined in the documentation of [`RecursionProgram::new_unchecked`].
    ///
    /// This function makes use of interior mutability of `env` via `UnsafeCell`.
    /// All of this function's unsafety stems from the `instruction` argument that indicates'
    /// whether/how to read and write from the memory in `env`. There must be a strict
    /// happens-before relation where reads happen before writes, and memory read from must be
    /// initialized.
    unsafe fn execute_one(
        state: &mut ExecState<F, Diffusion>,
        record: &UnsafeRecord<F>,
        witness_stream: Option<&mut VecDeque<Block<F>>>,
        analyzed_instruction: &AnalyzedInstruction<F>,
    ) -> Result<(), RuntimeError<F, EF>> {
        let ExecEnv { memory, perm, debug_stdout } = state.env;
        let instruction = &analyzed_instruction.inner;
        let offset = analyzed_instruction.offset;

        match *instruction {
            Instruction::BaseAlu(ref instr @ BaseAluInstr { opcode, mult: _, addrs }) => {
                let in1_block = memory.mr_unchecked(addrs.in1).val;
                let in2_block = memory.mr_unchecked(addrs.in2).val;
                let in1 = in1_block.0[0];
                let in2 = in2_block.0[0];
                let in1_u = in1.as_canonical_u32();
                let in2_u = in2.as_canonical_u32();
                // Do the computation.
                let out = match opcode {
                    BaseAluOpcode::AddF => in1 + in2,
                    BaseAluOpcode::SubF => in1 - in2,
                    BaseAluOpcode::MulF => in1 * in2,
                    BaseAluOpcode::DivF => match in1.try_div(in2) {
                        Some(x) => x,
                        None => {
                            // Check for division exceptions and error. Note that 0/0 is defined
                            // to be 1.
                            if in1.is_zero() {
                                AbstractField::one()
                            } else {
                                // ── Diagnostic dump ──
                                let [b0,b1,b2,b3] = in2_block.0.map(|x| x.as_canonical_u32());
                                EXEC_DIAG.with(|d| d.borrow().dump(&format!(
                                    "DivF in1={in1_u:#010x}@{} in2={in2_u:#010x}@{} out@{} \
                                     full_in2_block=({b0:#010x},{b1:#010x},{b2:#010x},{b3:#010x})",
                                    addrs.in1.as_usize(),
                                    addrs.in2.as_usize(),
                                    addrs.out.as_usize(),
                                )));
                                return Err(RuntimeError::DivFOutOfDomain {
                                    in1,
                                    in2,
                                    instr: *instr,
                                    trace: state.resolve_trace().cloned(),
                                });
                            }
                        }
                    },
                };
                let out_u = out.as_canonical_u32();
                let out_addr = addrs.out.as_usize();
                EXEC_DIAG.with(|d| d.borrow_mut().record(
                    out_addr,
                    format!(
                        "BaseAlu::{opcode:?} out@{out_addr}={out_u:#010x} \
                         in1@{}={in1_u:#010x} in2@{}={in2_u:#010x}",
                        addrs.in1.as_usize(),
                        addrs.in2.as_usize(),
                    ),
                ));
                memory.mw_unchecked(addrs.out, Block::from(out));
                // Write the event to the record.
                UnsafeCell::raw_get(record.base_alu_events[offset].as_ptr()).write(BaseAluEvent {
                    out,
                    in1,
                    in2,
                });
            }
            Instruction::ExtAlu(ref instr @ ExtAluInstr { opcode, mult: _, addrs }) => {
                let in1 = memory.mr_unchecked(addrs.in1).val;
                let in2 = memory.mr_unchecked(addrs.in2).val;
                // Do the computation.
                let in1_ef = EF::from_base_fn(|i| in1.0[i]);
                let in2_ef = EF::from_base_fn(|i| in2.0[i]);
                let out_ef = match opcode {
                    ExtAluOpcode::AddE => in1_ef + in2_ef,
                    ExtAluOpcode::SubE => in1_ef - in2_ef,
                    ExtAluOpcode::MulE => in1_ef * in2_ef,
                    ExtAluOpcode::DivE => match in1_ef.try_div(in2_ef) {
                        Some(x) => x,
                        None => {
                            // Check for division exceptions and error. Note that 0/0 is defined
                            // to be 1.
                            if in1_ef.is_zero() {
                                AbstractField::one()
                            } else {
                                return Err(RuntimeError::DivEOutOfDomain {
                                    in1: in1_ef,
                                    in2: in2_ef,
                                    instr: *instr,
                                    trace: state.resolve_trace().cloned(),
                                });
                            }
                        }
                    },
                };
                let out = Block::from(out_ef.as_base_slice());
                memory.mw_unchecked(addrs.out, out);

                // Write the event to the record.
                UnsafeCell::raw_get(record.ext_alu_events[offset].as_ptr()).write(ExtAluEvent {
                    out,
                    in1,
                    in2,
                });
            }
            Instruction::Mem(MemInstr {
                addrs: MemIo { inner: addr },
                vals: MemIo { inner: val },
                mult: _,
                kind,
            }) => match kind {
                MemAccessKind::Read => {
                    let mem_entry = memory.mr_unchecked(addr);
                    assert_eq!(
                        mem_entry.val, val,
                        "stored memory value should be the specified value"
                    );
                }
                MemAccessKind::Write => {
                    let addr_u = addr.as_usize();
                    let val_u = val.0[0].as_canonical_u32();
                    EXEC_DIAG.with(|d| {
                        let mut d = d.borrow_mut();
                        d.record(addr_u, format!("Mem::Write @{addr_u}={val_u:#010x}"));
                        d.record_mem_write(addr_u, val_u);
                    });
                    memory.mw_unchecked(addr, val)
                }
            },
            Instruction::ExtFelt(ExtFeltInstr { addrs, mults: _, ext2felt }) => {
                if ext2felt {
                    let in_val = memory.mr_unchecked(addrs[0]).val;
                    for (addr, value) in addrs[1..].iter().zip_eq(in_val.0) {
                        memory.mw_unchecked(*addr, Block::from(value));
                    }
                    // Write the event to the record.
                    UnsafeCell::raw_get(record.ext_felt_conversion_events[offset].as_ptr())
                        .write(ExtFeltEvent { input: in_val });
                } else {
                    let in_val = Block([
                        memory.mr_unchecked(addrs[1]).val.0[0],
                        memory.mr_unchecked(addrs[2]).val.0[0],
                        memory.mr_unchecked(addrs[3]).val.0[0],
                        memory.mr_unchecked(addrs[4]).val.0[0],
                    ]);
                    memory.mw_unchecked(addrs[0], in_val);
                    // Write the event to the record.
                    UnsafeCell::raw_get(record.ext_felt_conversion_events[offset].as_ptr())
                        .write(ExtFeltEvent { input: in_val });
                }
            }
            Instruction::Poseidon2(ref instr) => {
                let Poseidon2Instr { addrs: Poseidon2Io { input, output }, mults: _ } =
                    instr.as_ref();
                let in_vals = std::array::from_fn(|i| memory.mr_unchecked(input[i]).val[0]);
                let perm_output = perm.permute(in_vals);

                perm_output.iter().zip(output).for_each(|(&val, addr)| {
                    let addr_u = addr.as_usize();
                    EXEC_DIAG.with(|d| d.borrow_mut().record(
                        addr_u,
                        format!("Poseidon2 @{addr_u}={:#010x}", val.as_canonical_u32()),
                    ));
                    memory.mw_unchecked(*addr, Block::from(val));
                });

                // Write the event to the record.
                UnsafeCell::raw_get(record.poseidon2_events[offset].as_ptr())
                    .write(Poseidon2Event { input: in_vals, output: perm_output });
            }
            Instruction::Poseidon2LinearLayer(ref instr) => {
                let Poseidon2LinearLayerInstr {
                    addrs: Poseidon2LinearLayerIo { input, output },
                    mults: _,
                    external,
                } = instr.as_ref();
                let mut state = [F::zero(); PERMUTATION_WIDTH];
                let mut io_input = [Block::from(F::zero()); PERMUTATION_WIDTH / D];
                let mut io_output = [Block::from(F::zero()); PERMUTATION_WIDTH / D];
                for i in 0..PERMUTATION_WIDTH / D {
                    io_input[i] = memory.mr_unchecked(input[i]).val;
                    for j in 0..D {
                        state[i * D + j] = io_input[i].0[j];
                    }
                }
                if *external {
                    external_linear_layer_mut(&mut state);
                } else {
                    internal_linear_layer_mut(&mut state);
                }
                for i in 0..PERMUTATION_WIDTH / D {
                    io_output[i] = Block(state[i * D..i * D + D].try_into().unwrap());
                    memory.mw_unchecked(output[i], io_output[i]);
                }

                // Write the event to the record.
                UnsafeCell::raw_get(record.poseidon2_linear_layer_events[offset].as_ptr())
                    .write(Poseidon2LinearLayerEvent { input: io_input, output: io_output });
            }
            Instruction::Poseidon2SBox(Poseidon2SBoxInstr {
                addrs: Poseidon2SBoxIo { input, output },
                mults: _,
                external,
            }) => {
                let io_input = memory.mr_unchecked(input).val;
                let pow7 = |x: F| -> F { x * x * x };

                let io_output = if external {
                    Block([
                        pow7(io_input.0[0]),
                        pow7(io_input.0[1]),
                        pow7(io_input.0[2]),
                        pow7(io_input.0[3]),
                    ])
                } else {
                    Block([pow7(io_input.0[0]), io_input.0[1], io_input.0[2], io_input.0[3]])
                };
                memory.mw_unchecked(output, io_output);

                // Write the event to the record.
                UnsafeCell::raw_get(record.poseidon2_sbox_events[offset].as_ptr())
                    .write(Poseidon2SBoxEvent { input: io_input, output: io_output });
            }
            Instruction::Select(SelectInstr {
                addrs: SelectIo { bit, out1, out2, in1, in2 },
                mult1: _,
                mult2: _,
            }) => {
                let bit = memory.mr_unchecked(bit).val[0];
                let in1 = memory.mr_unchecked(in1).val[0];
                let in2 = memory.mr_unchecked(in2).val[0];
                let out1_val = bit * in2 + (F::one() - bit) * in1;
                let out2_val = bit * in1 + (F::one() - bit) * in2;
                let out1_addr = out1.as_usize();
                let out2_addr = out2.as_usize();
                EXEC_DIAG.with(|d| {
                    let mut d = d.borrow_mut();
                    d.record(
                        out1_addr,
                        format!("Select out1@{out1_addr}={:#010x}", out1_val.as_canonical_u32()),
                    );
                    d.record(
                        out2_addr,
                        format!("Select out2@{out2_addr}={:#010x}", out2_val.as_canonical_u32()),
                    );
                });
                memory.mw_unchecked(out1, Block::from(out1_val));
                memory.mw_unchecked(out2, Block::from(out2_val));

                // Write the event to the record.
                UnsafeCell::raw_get(record.select_events[offset].as_ptr()).write(SelectEvent {
                    bit,
                    out1: out1_val,
                    out2: out2_val,
                    in1,
                    in2,
                });
            }
            Instruction::HintBits(HintBitsInstr { ref output_addrs_mults, input_addr }) => {
                let num = memory.mr_unchecked(input_addr).val[0].as_canonical_u32();
                // Decompose the num into LE bits.
                let bits = (0..output_addrs_mults.len())
                    .map(|i| Block::from(F::from_canonical_u32((num >> i) & 1)))
                    .collect::<Vec<_>>();

                // Write the bits to the array at dst.
                for (i, (bit, &(addr, _mult))) in
                    bits.into_iter().zip(output_addrs_mults).enumerate()
                {
                    memory.mw_unchecked(addr, bit);

                    // Write the event to the record.
                    UnsafeCell::raw_get(record.mem_var_events[offset + i].as_ptr())
                        .write(MemEvent { inner: bit });
                }
            }
            Instruction::HintAddCurve(ref instr) => {
                let HintAddCurveInstr {
                    output_x_addrs_mults,
                    output_y_addrs_mults,
                    input1_x_addrs,
                    input1_y_addrs,
                    input2_x_addrs,
                    input2_y_addrs,
                } = instr.as_ref();
                let input1_x = SepticExtension::<F>::from_base_fn(|i| {
                    memory.mr_unchecked(input1_x_addrs[i]).val[0]
                });
                let input1_y = SepticExtension::<F>::from_base_fn(|i| {
                    memory.mr_unchecked(input1_y_addrs[i]).val[0]
                });
                let input2_x = SepticExtension::<F>::from_base_fn(|i| {
                    memory.mr_unchecked(input2_x_addrs[i]).val[0]
                });
                let input2_y = SepticExtension::<F>::from_base_fn(|i| {
                    memory.mr_unchecked(input2_y_addrs[i]).val[0]
                });
                let point1 = SepticCurve { x: input1_x, y: input1_y };
                let point2 = SepticCurve { x: input2_x, y: input2_y };
                let output = point1.add_incomplete(point2);

                for (i, (val, &(addr, _mult))) in output
                    .x
                    .0
                    .into_iter()
                    .zip(output_x_addrs_mults.iter())
                    .chain(output.y.0.into_iter().zip(output_y_addrs_mults.iter()))
                    .enumerate()
                {
                    memory.mw_unchecked(addr, Block::from(val));

                    UnsafeCell::raw_get(record.mem_var_events[offset + i].as_ptr())
                        .write(MemEvent { inner: Block::from(val) });
                }
            }
            Instruction::PrefixSumChecks(ref instr) => {
                let PrefixSumChecksInstr {
                    addrs: PrefixSumChecksIo { zero, one, x1, x2, accs, field_accs },
                    acc_mults: _,
                    field_acc_mults: _,
                } = instr.as_ref();
                let zero = memory.mr_unchecked(*zero).val[0];
                let one = memory.mr_unchecked(*one).val.ext::<EF>();
                let x1_f = x1.iter().map(|addr| memory.mr_unchecked(*addr).val[0]).collect_vec();
                let x2_ef =
                    x2.iter().map(|addr| memory.mr_unchecked(*addr).val.ext::<EF>()).collect_vec();

                let mut acc = EF::one();
                let mut field_acc = F::zero();
                for m in 0..x1_f.len() {
                    let product = EF::from_base(x1_f[m]) * x2_ef[m];
                    let lagrange_term = EF::one() - x1_f[m] - x2_ef[m] + product + product;
                    let new_field_acc = x1_f[m] + field_acc * F::from_canonical_u32(2);
                    let new_acc = acc * lagrange_term;

                    UnsafeCell::raw_get(record.prefix_sum_checks_events[offset + m].as_ptr())
                        .write(PrefixSumChecksEvent {
                            zero,
                            one: Block::from(one.as_base_slice()),
                            x1: x1_f[m],
                            x2: Block::from(x2_ef[m].as_base_slice()),
                            acc: Block::from(acc.as_base_slice()),
                            new_acc: Block::from(new_acc.as_base_slice()),
                            field_acc,
                            new_field_acc,
                        });

                    acc = new_acc;
                    field_acc = new_field_acc;
                    memory.mw_unchecked(accs[m], Block::from(acc.as_base_slice()));
                    memory.mw_unchecked(field_accs[m], Block::from(field_acc));
                }
            }
            Instruction::CommitPublicValues(ref instr) => {
                let pv_addrs = instr.pv_addrs.as_array();
                let pv_values: [F; RECURSIVE_PROOF_NUM_PV_ELTS] =
                    array::from_fn(|i| memory.mr_unchecked(pv_addrs[i]).val[0]);

                // Write the public values to the record.
                UnsafeCell::raw_get(record.public_values.as_ptr())
                    .write(*pv_values.as_slice().borrow());

                // Write the event to the record.
                UnsafeCell::raw_get(record.commit_pv_hash_events[offset].as_ptr()).write(
                    CommitPublicValuesEvent { public_values: *pv_values.as_slice().borrow() },
                );
            }
            Instruction::Print(PrintInstr { ref field_elt_type, addr }) => match field_elt_type {
                FieldEltType::Base => {
                    let f = memory.mr_unchecked(addr).val[0];
                    writeln!(debug_stdout.lock().unwrap(), "PRINTF={f}")
                }
                FieldEltType::Extension => {
                    let ef = memory.mr_unchecked(addr).val;
                    writeln!(debug_stdout.lock().unwrap(), "PRINTEF={ef:?}")
                }
            }
            .map_err(RuntimeError::DebugPrint)?,
            Instruction::HintExt2Felts(HintExt2FeltsInstr { output_addrs_mults, input_addr }) => {
                let fs = memory.mr_unchecked(input_addr).val;
                // Write the bits to the array at dst.
                for (i, (f, (addr, _mult))) in fs.into_iter().zip(output_addrs_mults).enumerate() {
                    let felt = Block::from(f);
                    memory.mw_unchecked(addr, felt);

                    // Write the event to the record.
                    UnsafeCell::raw_get(record.mem_var_events[offset + i].as_ptr())
                        .write(MemEvent { inner: felt });
                }
            }
            Instruction::Hint(HintInstr { ref output_addrs_mults }) => {
                let witness_stream =
                    witness_stream.expect("hint should be called outside parallel contexts");
                // Check that enough Blocks can be read, so `drain` does not panic.
                if witness_stream.len() < output_addrs_mults.len() {
                    return Err(RuntimeError::EmptyWitnessStream);
                }

                let witness = witness_stream.drain(0..output_addrs_mults.len());
                for (i, (&(addr, _mult), val)) in zip(output_addrs_mults, witness).enumerate() {
                    // Inline [`Self::mw`] to mutably borrow multiple fields of `self`.
                    memory.mw_unchecked(addr, val);

                    // Track hint writes to watched addresses for diagnostics.
                    EXEC_DIAG.with(|d| {
                        let mut d = d.borrow_mut();
                        let block = [
                            val.0[0].as_canonical_u32(),
                            val.0[1].as_canonical_u32(),
                            val.0[2].as_canonical_u32(),
                            val.0[3].as_canonical_u32(),
                        ];
                        d.record_hint_write(addr.as_usize(), block);
                    });

                    // Write the event to the record.
                    UnsafeCell::raw_get(record.mem_var_events[offset + i].as_ptr())
                        .write(MemEvent { inner: val });
                }
            }
            Instruction::DebugBacktrace(ref backtrace) => {
                cfg_if! {
                    if #[cfg(feature = "debug")] {
                        state.last_trace = Some(backtrace.clone());
                    } else {
                        // Ignore.
                        let _ = backtrace;
                    }
                }
            }
        }

        Ok(())
    }

    unsafe fn execute_raw(
        env: &ExecEnv<F, Diffusion>,
        root_program: &Arc<RecursionProgram<F>>,
        witness_stream: Option<&mut VecDeque<Block<F>>>,
    ) -> Result<ExecutionRecord<F>, RuntimeError<F, EF>> {
        let root_record = UnsafeRecord::<F>::new(root_program.event_counts);
        debug_span!("root").in_scope(|| {
            Self::execute_raw_inner(env, &root_program.inner, witness_stream, &root_record)
        })?;

        // SAFETY: `root_record` has been populated by the executor.
        let record = root_record.into_record(Arc::clone(root_program), 0);
        Ok(record)
    }

    /// # Safety
    ///
    /// This function makes the same safety assumptions as [`RecursionProgram::new_unchecked`].
    unsafe fn execute_raw_inner(
        env: &ExecEnv<F, Diffusion>,
        program: &RawProgram<AnalyzedInstruction<F>>,
        mut witness_stream: Option<&mut VecDeque<Block<F>>>,
        record: &UnsafeRecord<F>,
    ) -> Result<(), RuntimeError<F, EF>> {
        let mut state = ExecState {
            env: env.clone(),
            #[cfg(feature = "debug")]
            last_trace: None,
        };

        for block in &program.seq_blocks {
            match block {
                SeqBlock::Basic(basic_block) => {
                    for analyzed_instruction in &basic_block.instrs {
                        unsafe {
                            Self::execute_one(
                                &mut state,
                                record,
                                witness_stream.as_deref_mut(),
                                analyzed_instruction,
                            )
                        }?;
                    }
                }
                SeqBlock::Parallel(vec) => {
                    vec.par_iter().try_for_each(|subprogram| {
                        Self::execute_raw_inner(env, subprogram, None, record)
                    })?;
                }
            }
        }

        Ok(())
    }

    /// Run the program.
    pub fn run(&mut self) -> Result<(), RuntimeError<F, EF>> {
        let record = unsafe {
            Self::execute_raw(
                &ExecEnv {
                    memory: &self.memory,
                    perm: self.perm.as_ref().unwrap(),
                    debug_stdout: &Mutex::new(&mut self.debug_stdout),
                },
                &self.program,
                Some(&mut self.witness_stream),
            )
        }?;

        // On success: dump init_mem_writes so we can compare with failing runs.
        EXEC_DIAG.with(|d| d.borrow().dump_init());

        self.record = record;

        Ok(())
    }
}

struct ExecState<'a, 'b, F, Diffusion> {
    pub env: ExecEnv<'a, 'b, F, Diffusion>,
    // pub record: Arc<UnsafeRecord<F>>,
    #[cfg(feature = "debug")]
    pub last_trace: Option<Trace>,
}

impl<F, Diffusion> ExecState<'_, '_, F, Diffusion> {
    fn resolve_trace(&mut self) -> Option<&mut Trace> {
        cfg_if::cfg_if! {
            if #[cfg(feature = "debug")] {
                // False positive.
                #[allow(clippy::manual_inspect)]
                self.last_trace.as_mut().map(|trace| {
                    trace.resolve();
                    trace
                })
            } else {
                None
            }
        }
    }
}

impl<'a, 'b, F, Diffusion> Clone for ExecState<'a, 'b, F, Diffusion>
where
    ExecEnv<'a, 'b, F, Diffusion>: Clone,
    ExecutionRecord<F>: Clone,
{
    fn clone(&self) -> Self {
        let Self {
            env,
            // record,
            #[cfg(feature = "debug")]
            last_trace,
        } = self;
        Self {
            env: env.clone(),
            // record: record.clone(),
            #[cfg(feature = "debug")]
            last_trace: last_trace.clone(),
        }
    }

    fn clone_from(&mut self, source: &Self) {
        let Self {
            env,
            // record,
            #[cfg(feature = "debug")]
            last_trace,
        } = self;
        env.clone_from(&source.env);
        // record.clone_from(&source.record);
        #[cfg(feature = "debug")]
        last_trace.clone_from(&source.last_trace);
    }
}

struct ExecEnv<'a, 'b, F, Diffusion> {
    pub memory: &'a MemVec<F>,
    pub perm: &'a Perm<F, Diffusion>,
    pub debug_stdout: &'a Mutex<dyn Write + Send + 'b>,
}

impl<F, Diffusion> Clone for ExecEnv<'_, '_, F, Diffusion> {
    fn clone(&self) -> Self {
        let Self { memory, perm, debug_stdout } = self;
        Self { memory, perm, debug_stdout }
    }

    fn clone_from(&mut self, source: &Self) {
        let Self { memory, perm, debug_stdout } = self;
        memory.clone_from(&source.memory);
        perm.clone_from(&source.perm);
        debug_stdout.clone_from(&source.debug_stdout);
    }
}

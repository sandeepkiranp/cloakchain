use sp1_sdk::{blocking::MockProver, blocking::Prover, include_elf, Elf, HashableKey, ProvingKey};

/// The ELF files for the Succinct RISC-V zkVM.
const CLOAKKCHAIN_SPEND_ELF: Elf = include_elf!("cloakkchain-program-spend");
const CLOAKKCHAIN_COINPROOF_ELF: Elf = include_elf!("cloakkchain-program-coinproof");

fn main() {
    let prover = MockProver::new();

    let spend_pk = prover.setup(CLOAKKCHAIN_SPEND_ELF).expect("failed to setup spend elf");
    println!("spend:     {}", spend_pk.verifying_key().bytes32());

    let coinproof_pk = prover.setup(CLOAKKCHAIN_COINPROOF_ELF).expect("failed to setup coinproof elf");
    println!("coinproof: {}", coinproof_pk.verifying_key().bytes32());
}

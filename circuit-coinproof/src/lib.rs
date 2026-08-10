//! MNT-native coin-receipt circuit (not yet implemented). Will hold
//! `CoinReceiptCircuit` (`ConstraintSynthesizer<Fr>`, recursively verifying a
//! parent spend proof via `Groth16VerifierGadget`) plus its Groth16
//! setup/prove/verify wrappers.

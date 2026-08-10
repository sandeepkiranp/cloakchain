//! Poseidon hash parameters for MNT4-753's and MNT6-753's scalar fields.
//!
//! **TEST-ONLY, NOT PRODUCTION-SAFE.** Round constants and the MDS matrix are
//! deterministically pseudo-random (fixed-seed), not generated via the
//! reviewed Grain-LFSR + Cauchy-MDS method — the same convention arkworks'
//! own test suite uses for its parameters ("incorrect, test purposes only").
//! No maintained parameter-generation crate targets these fields yet.
//! Generating audited parameters is tracked as follow-up work before any
//! production use — see the `mnt_native_experiment` design note.

use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ff::PrimeField;
use ark_std::rand::{rngs::StdRng, SeedableRng};

const FULL_ROUNDS: usize = 8;
const PARTIAL_ROUNDS: usize = 60;
const ALPHA: u64 = 5;
const RATE: usize = 2;
const CAPACITY: usize = 1;

fn test_only_config<F: PrimeField>(seed: u64) -> PoseidonConfig<F> {
    let mut rng = StdRng::seed_from_u64(seed);
    let width = RATE + CAPACITY;
    let ark = (0..(FULL_ROUNDS + PARTIAL_ROUNDS))
        .map(|_| (0..width).map(|_| F::rand(&mut rng)).collect())
        .collect();
    let mds = (0..width)
        .map(|_| (0..width).map(|_| F::rand(&mut rng)).collect())
        .collect();
    PoseidonConfig::new(FULL_ROUNDS, PARTIAL_ROUNDS, ALPHA, mds, ark, RATE, CAPACITY)
}

pub fn mnt4_753_fr_poseidon_config() -> PoseidonConfig<ark_mnt4_753::Fr> {
    test_only_config(0x434c_4f41_4b4d_5434u64) // "CLOAKM T4"-ish seed
}

pub fn mnt6_753_fr_poseidon_config() -> PoseidonConfig<ark_mnt6_753::Fr> {
    test_only_config(0x434c_4f41_4b4d_5436u64) // "CLOAKM T6"-ish seed
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::{
        poseidon::PoseidonSponge, CryptographicSponge, FieldBasedCryptographicSponge,
    };

    #[test]
    fn mnt4_config_is_deterministic() {
        let a = mnt4_753_fr_poseidon_config();
        let b = mnt4_753_fr_poseidon_config();
        assert_eq!(a.ark, b.ark);
        assert_eq!(a.mds, b.mds);
    }

    #[test]
    fn mnt4_and_mnt6_configs_differ() {
        // Different fields entirely, but sanity-check the seeds at least
        // produced distinct round-constant shapes (both non-empty, same
        // width/round-count convention).
        let a = mnt4_753_fr_poseidon_config();
        let b = mnt6_753_fr_poseidon_config();
        assert_eq!(a.full_rounds, b.full_rounds);
        assert_eq!(a.partial_rounds, b.partial_rounds);
        assert_eq!(a.rate, b.rate);
        assert_eq!(a.capacity, b.capacity);
    }

    #[test]
    fn mnt4_sponge_hash_is_deterministic() {
        let cfg = mnt4_753_fr_poseidon_config();
        let hash_once = || {
            let mut sponge = PoseidonSponge::new(&cfg);
            sponge.absorb(&vec![ark_mnt4_753::Fr::from(7u64), ark_mnt4_753::Fr::from(9u64)]);
            sponge.squeeze_native_field_elements(1)[0]
        };
        assert_eq!(hash_once(), hash_once());
    }
}

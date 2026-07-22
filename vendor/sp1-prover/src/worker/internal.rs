use std::sync::Arc;

use sp1_prover_types::ArtifactClient;

use crate::{
    verify::SP1Verifier,
    worker::{SP1Controller, SP1ProverEngine, WorkerClient},
    SP1ProverComponents,
};

struct SP1WorkerInner<A, W, C: SP1ProverComponents> {
    controller: SP1Controller<A, W>,
    prover_engine: SP1ProverEngine<A, W, C>,
    verifier: SP1Verifier,
}

/// A worker that can be used to run tasks for the SP1 distributed prover.
///
/// # Type Parameters
///
/// - `A`: The artifact client type.
/// - `W`: The worker client type.
/// - `C`: The prover components type.
pub struct SP1Worker<A, W, C: SP1ProverComponents> {
    inner: Arc<SP1WorkerInner<A, W, C>>,
}

impl<A, W, C: SP1ProverComponents> Clone for SP1Worker<A, W, C> {
    fn clone(&self) -> Self {
        Self { inner: self.inner.clone() }
    }
}

impl<A: ArtifactClient, W: WorkerClient, C: SP1ProverComponents> SP1Worker<A, W, C> {
    /// Create a new worker.
    pub fn new(
        controller: SP1Controller<A, W>,
        prover_engine: SP1ProverEngine<A, W, C>,
        verifier: SP1Verifier,
    ) -> Self {
        Self { inner: Arc::new(SP1WorkerInner { controller, prover_engine, verifier }) }
    }

    /// Get a reference to the underlying controller.
    #[inline]
    pub fn controller(&self) -> &SP1Controller<A, W> {
        &self.inner.controller
    }

    /// Get a reference to the underlying prover engine.
    #[inline]
    pub fn prover_engine(&self) -> &SP1ProverEngine<A, W, C> {
        &self.inner.prover_engine
    }

    /// Get a reference to the underlying verifier.
    #[inline]
    pub fn verifier(&self) -> &SP1Verifier {
        &self.inner.verifier
    }

    /// Get a reference to the underlying artifact client.
    #[inline]
    pub fn artifact_client(&self) -> &A {
        &self.inner.controller.artifact_client
    }

    /// Get a reference to the underlying worker client.
    #[inline]
    pub fn worker_client(&self) -> &W {
        &self.inner.controller.worker_client
    }
}

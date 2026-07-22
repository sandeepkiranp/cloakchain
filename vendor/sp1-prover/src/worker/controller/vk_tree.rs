use std::collections::{BTreeMap, BTreeSet};

use either::Either;
use rand::{seq::SliceRandom, SeedableRng};
use serde::{Deserialize, Serialize};
use sp1_hypercube::DIGEST_SIZE;
use sp1_primitives::SP1Field;
use sp1_prover_types::{ArtifactClient, TaskType};

use crate::{
    shapes::create_all_input_shapes,
    worker::{RawTaskRequest, SP1Controller, TaskError, TaskMetadata, WorkerClient},
};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VkeyMapControllerInput {
    pub range_or_limit: Option<Either<Vec<usize>, usize>>,
    pub chunk_size: usize,
    pub reduce_batch_size: usize,
}

#[derive(Debug, Clone, Serialize, serde::Deserialize)]
pub struct VkeyMapControllerOutput {
    pub vk_map: BTreeMap<[SP1Field; DIGEST_SIZE], usize>,
    pub panic_indices: Vec<usize>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VkeyMapChunkInput {
    pub reduce_batch_size: usize,
    pub indices: Vec<usize>,
    pub total_inputs: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VkeyMapChunkOutput {
    pub vk_set: BTreeSet<[SP1Field; DIGEST_SIZE]>,
    pub panic_indices: Vec<usize>,
}

impl<A: ArtifactClient, W: WorkerClient> SP1Controller<A, W> {
    pub async fn run_sp1_util_vkey_map_controller(
        &self,
        request: RawTaskRequest,
    ) -> Result<TaskMetadata, TaskError>
where {
        let subscriber =
            self.worker_client.subscriber(request.context.proof_id.clone()).await?.per_task();
        let input =
            self.artifact_client.download::<VkeyMapControllerInput>(&request.inputs[0]).await?;

        let num_shapes =
            create_all_input_shapes(self.verifier.core.machine().shape(), input.reduce_batch_size)
                .into_iter()
                .collect::<BTreeSet<_>>()
                .len();

        let limit = input.range_or_limit.unwrap_or(Either::Right(num_shapes));

        let mut all_indices = match limit {
            Either::Left(range) => range,
            Either::Right(limit) => (0..limit).collect::<Vec<_>>(),
        };

        // Randomize the order of the indices
        {
            let mut rng = rand::rngs::StdRng::seed_from_u64(0);
            all_indices.shuffle(&mut rng);
        }

        let chunks =
            all_indices.chunks(input.chunk_size).map(|chunk| chunk.to_vec()).collect::<Vec<_>>();

        let inputs = chunks
            .into_iter()
            .map(|chunk| VkeyMapChunkInput {
                reduce_batch_size: input.reduce_batch_size,
                indices: chunk,
                total_inputs: num_shapes,
            })
            .collect::<Vec<_>>();

        let mut input_artifacts = Vec::new();
        for input in &inputs {
            let artifact = self.artifact_client.create_artifact()?;
            self.artifact_client.upload(&artifact, &input).await?;
            input_artifacts.push(artifact);
        }

        let mut output_artifacts = Vec::new();
        for _ in 0..inputs.len() {
            let artifact = self.artifact_client.create_artifact()?;
            output_artifacts.push(artifact);
        }

        let mut tasks = Vec::new();

        for (task_input, task_output) in input_artifacts.into_iter().zip(output_artifacts.iter()) {
            let request = RawTaskRequest {
                inputs: vec![task_input],
                outputs: vec![task_output.clone()],
                context: request.context.clone(),
            };
            let task = self.worker_client.submit_task(TaskType::UtilVkeyMapChunk, request).await?;
            tasks.push(task);
        }

        for task in tasks {
            subscriber.wait_task(task).await?;
        }

        let mut outputs = Vec::new();
        for output_artifact in output_artifacts {
            let output =
                self.artifact_client.download::<VkeyMapChunkOutput>(&output_artifact).await?;
            outputs.push(output);
        }

        // Merge outputs into a single map and reassign indexes
        let (vk_maps, panic_indices): (Vec<_>, Vec<_>) =
            outputs.into_iter().map(|output| (output.vk_set, output.panic_indices)).unzip();
        let final_vk_map = vk_maps
            .into_iter()
            .flatten()
            // It's important to order the VKeys to ensure consistent indexing.
            .collect::<BTreeSet<_>>()
            .into_iter()
            .enumerate()
            .map(|(i, vk)| (vk, i))
            .collect::<BTreeMap<_, _>>();
        let panic_indices = panic_indices.into_iter().flatten().collect::<Vec<_>>();

        let output = VkeyMapControllerOutput { vk_map: final_vk_map, panic_indices };

        self.artifact_client.upload(&request.outputs[0], output).await?;

        Ok(TaskMetadata::default())
    }
}

---
title: "Building a distributed platform for agent training and evaluation"
description: "How I built SynthLabs’ agent-learning platform: reusable agents, distributed task execution, native model integration, reinforcement learning and managed cloud infrastructure."
image: "/assets/synth-platform/article-cover.png"
imageAlt: "Distributed agent training and evaluation: executable work, native agent experience and model updates."
updated: 2026-10-21
---

At SynthLabs, I designed and built a distributed platform for running,
evaluating and training tool-using agents. Its execution and learning core
powered campaigns involving tens of thousands of agent attempts. The platform
runs isolated repository tasks, captures the model interactions produced inside
the native coding harness, joins that experience to task assessments, and trains
a supported model from it. The resulting checkpoint returns to the same harness.

The central engineering problem was preserving the agent through that loop:
its tools, delegation and context behavior; the exact tokens sampled by a
particular model snapshot; and the state produced by each training update.
Independent task work and learning preparation can overlap, while policy
advancement retains an explicit synchronization boundary.

I built the Python RL Runtime, native model adapters, reusable agent profiles,
and the managed delivery paths around them: a Go CLI and agent launcher,
authenticated control, storage contracts and cloud infrastructure. An operator
can submit versioned work and an agent recipe, then return to its execution,
assessments, artifacts and checkpoints without operating the underlying workers.

<nav class="platform-contents" aria-label="Article navigation"><a href="#the-experiment-is-the-interface">The experiment</a> · <a href="#the-system-underneath">Architecture</a> · <a href="#an-agent-profile-is-an-executable-recipe">Agent profiles</a> · <a href="#actors-and-judges-can-run-independently">Actor/judge modes</a> · <a href="#keep-the-native-harness-change-the-model">Native agents</a> · <a href="#one-execution-core-for-evaluation-and-training">Execution</a> · <a href="#from-experience-to-learning">Learning</a> · <a href="#a-managed-service-around-the-learning-loop">Cloud systems</a> · <a href="#what-this-made-possible">Usage</a> · <a href="/from-software-work-to-specialized-agents/">Companion: tasks and specialists</a></nav>

<figure class="platform-figure platform-wide" id="platform-architecture" aria-labelledby="architecture-caption">
  <picture><source media="(max-width: 760px)" srcset="/assets/synth-platform/architecture-mobile.svg" width="420" height="1650"><img src="/assets/synth-platform/architecture.svg" width="1000" height="720" alt="Logical architecture of Synth: the CLI submits experiments to Gateway; Gateway records durable state and delegates execution to Runtime; Runtime coordinates task sandboxes, native-agent inference through Proxy, learning through Tinker and direct artifact transfers through object storage." loading="eager"></picture>
  <figcaption id="architecture-caption">The platform’s principal control, execution and learning paths. Native agents and tools work in remote task environments; model providers perform inference and training computation. <a href="#the-system-underneath">Architecture explained below.</a></figcaption>
</figure>

## The experiment is the interface

An agent experiment includes the work environment, executable agent, assessment
and policy for running it. A coding agent may inspect files, edit code, run tests
and react to their output. Its result includes both the changed artifacts and
the interactions that produced them.

The platform gives those inputs distinct homes:

<figure class="platform-figure" id="experiment-model" aria-labelledby="experiment-caption">
  <div class="experiment-inputs">
    <div><strong>The work</strong><span>Versioned tasks and datasets</span><small>Instructions, starting environment, files and default verification.</small></div>
    <div><strong>The agent</strong><span>A reusable agent profile</span><small>Model, native engine, instructions, tools, configuration and setup.</small></div>
    <div><strong>The assessment</strong><span>Verification or judge, when selected</span><small>The checks or agent responsible for evaluating the outcome.</small></div>
    <div><strong>The plan</strong><span>Work amount and policy</span><small>Repetitions, batches, execution settings and training choices.</small></div>
  </div>
  <div class="experiment-join" aria-hidden="true">↓</div>
  <div class="experiment-run"><strong>One managed run</strong><span>Distributed execution · results and artifacts · training updates and checkpoints when selected</span></div>
  <figcaption id="experiment-caption">The work, agent, assessment and execution plan are reusable inputs. A run records their resolved identities and the work performed from them.</figcaption>
</figure>

**A task defines a piece of work.** For a repository-level engineering task,
that might be a pinned checkout, a problem statement, installed dependencies and
tests. Synth uses [Harbor’s task format](https://github.com/harbor-framework/harbor): the instruction, environment and
verification travel together. A dataset selects exact task versions in a
defined order.

**The profile defines the agent.** The same task can be attempted with different
models, instructions, skills or tool configurations. Those choices belong to
the agent rather than being baked into every task.

**The assessment defines what counts as useful work.** A task can provide
programmatic tests. Where the task supports a separate verifier environment,
an explicit judge profile can instead assess an output using its own model,
instructions and reference information. Actor and judge are roles using the
same underlying agent abstraction.

**The plan defines how the experiment runs.** Evaluation can repeat a fixed
setup across a dataset. Training chooses batches of tasks and repeated attempts
at each task, with explicit optimization and execution settings. Unscored
execution uses the same task-performing path when the desired result is simply
the work and its artifacts.

An engineer can evaluate a baseline profile, change its instructions or tools,
and compare the new setup on the same versioned work. Supported training then
updates the model while retaining the chosen recipe; the checkpoint can be
evaluated on held-out tasks through that same harness.

An authorized operator works with commands such as:

```sh
synth run start \
  --dataset team/evaluation@v1 \
  --actor @agent.json \
  --plan @eval-plan.json
synth train start \
  --dataset team/practice@v1 \
  --actor @agent.json \
  --plan @train-plan.json
synth run show <run-id>
synth run events <run-id> --follow
synth run checkpoints <training-run-id>
```

The dataset, profile and plan references above are illustrative. Submission
returns a durable run identity; the operator can return to its progress,
results, artifacts and checkpoints without keeping a local controller running.

## The system underneath

The architecture separates the **control plane**, which authorizes and records
the experiment, from the **execution and model-computation paths**, which do
the work. Large task packages and trajectories move through object storage
rather than passing through the control service on every transfer.

The main components have deliberately different jobs:

- **`synth`** is the operator interface and native-agent launcher. It exposes
  reusable work and agents, submits experiments, and reads their results.
- **`sprite-gateway`** is the authenticated control plane. It resolves authorized
  inputs, admits durable jobs, delegates execution and serves run progress and
  results.
- **`agent-rl-runtime`** schedules task attempts, coordinates evaluation and
  learning, manages progress and advances model state.
- **`managed-agent-proxy`** connects the native harness to supported models and
  preserves the model-interaction evidence needed for learning.
- **PostgreSQL and object storage** retain complementary parts of the system:
  authoritative relationships and lifecycle facts in one; task packages,
  trajectories and other large payloads in the other.
- **Kubernetes, Harbor, sandbox providers and model-computation providers**
  supply the service, task-execution and numerical-computation foundations.

Consider one training batch. Runtime resolves its selected tasks and agent
configuration, starts isolated attempts, and gives each native agent narrowly
scoped model access. The agent’s tool use occurs in its task environment;
its model calls pass through the compatibility and capture layer. A verifier
or judge assesses the completed work. Runtime joins those assessments to the
corresponding model interactions, prepares learning inputs and submits them to
the training backend. After the update, it obtains the sampler used by the next
batch and retains a checkpoint that an authorized operator can inspect and use.

## An agent profile is an executable recipe

Agent behavior changes faster than execution infrastructure. A different
instruction set, skill or supported harness configuration should be a new
experiment input, not require a new Runtime deployment.

I developed the agent-profile abstraction to make that complete setup reusable
outside the execution machinery. A profile records a selected model and an executable recipe: the native engine
and version, supplied files, setup, working directory, command arguments,
environment bindings, instruction delivery and required outputs. Instructions,
skills, hooks and tool configuration can be supplied through that recipe.

<figure class="platform-figure" id="agent-recipe" aria-labelledby="profile-caption">
  <div class="profile-model"><span class="diagram-label">Model binding</span><strong>Base model or selected checkpoint</strong><span>The learned policy used for generation.</span></div>
  <div class="profile-separator" aria-hidden="true">+</div>
  <div class="profile-harness"><span class="diagram-label">Executable harness recipe</span><div class="profile-grid"><span>Native engine + version</span><span>Instructions + skills</span><span>Tools + configuration</span><span>Files + setup</span><span>Working directory + bindings</span><span>Input + required outputs</span></div></div>
  <div class="profile-bindings"><span><strong>Task</strong> supplies the work and environment.</span><span><strong>Launch</strong> supplies authorized runtime bindings.</span></div>
  <figcaption id="profile-caption">The model and the harness can change independently. A task supplies the work; a profile supplies reusable agent behavior. Launch-time credentials and authority are not part of a shareable recipe.</figcaption>
</figure>

This creates two important experimental levers. To investigate a harness change,
keep the model fixed and change the agent’s instructions, tools or context.
To investigate a model update, keep the recipe fixed and bind it to a new
checkpoint. The system can retain both identities without treating a saved
model as the entire agent.

Local and Harbor-managed execution use one Go interpreter for the profile.
Runtime supplies task, run and effective-model bindings to that launcher;
it does not reconstruct the recipe in Python. Instruction delivery, literal
arguments, setup, environment and working-directory resolution, and required
outputs therefore have one execution contract.

Published profile versions are immutable, so an experiment retains the version
it selected when a newer one is published. The service supplies canonical
profile bytes and a digest; the Go client verifies that representation instead
of assuming that Go and Python serialize the same object identically.

During training, each batch binds that fixed recipe to an explicit effective
model snapshot. The experiment can advance the policy without silently
changing the harness.

### Actors and judges can run independently

An actor profile defines how to perform work. A judge profile defines how to
assess its artifacts. Both are complete agent recipes, with independently
selected models, instructions, tools and resources. A reusable judge can serve
a family of tasks while each task supplies its own reference material. A strong
judge need not be a model the training backend can optimize. On eligible tasks,
it runs in a separate verifier environment with task-owned assessment context,
declared actor outputs and its own scoped model access.

The roles support three useful modes. **Actor-only execution** produces work
and artifacts without requiring a score. **Evaluation** pairs fresh attempts
with the task's verifier or an explicit judge. **Reassessment** applies a new or
repeated judge to retained work without asking the original actor to solve the
task again.

<figure class="platform-figure role-modes" id="independent-role-modes" aria-labelledby="roles-caption">
  <div class="role-lane"><strong>Produce work</strong><div class="role-flow"><span>Task + actor profile</span><b aria-hidden="true">→</b><span>Actor execution</span><b aria-hidden="true">→</b><span>Output + artifacts</span></div></div>
  <div class="role-lane"><strong>Produce and assess</strong><div class="role-flow"><span>New actor output</span><b aria-hidden="true">→</b><span>Verifier or judge</span><b aria-hidden="true">→</b><span>Assessment</span></div><small>The task supplies the assessment context and any private references.</small></div>
  <div class="role-lane"><strong>Reassess fixed work</strong><div class="role-flow"><span>Retained output + task context</span><b aria-hidden="true">→</b><span>Selected judge, repeated or changed</span><b aria-hidden="true">→</b><span>New assessments</span></div></div>
  <figcaption id="roles-caption">Producing work, assessing it and learning from it are separate operations. Reassessment fixes the original output; training additionally needs the actor's captured model interactions.</figcaption>
</figure>

I built a regrading path that reuses the task registry and evaluation machinery.
It derives tasks from the original immutable task versions, restores retained
actor outputs, and runs the selected judge against the preserved assessment
context. Source-trial and artifact digests record which work was assessed.
Different judges and repeated assessments can therefore examine the same
retained output; the task and judge still define what that output means.

This makes the evaluator an independent experimental choice. A judge can be
calibrated or checked for consistency while holding the original work fixed.
Weight training remains a separate operation: it additionally requires the
original actor's captured sampled-token evidence.

## Keep the native harness, change the model

I wanted to retain the capabilities of a real coding harness: repository
navigation, shell commands, file editing, tool use, native configuration and
configured delegation to subagents. Synth’s model layer lets the installed
harness use a supported backend model while preserving that execution model.
In the managed native path, delegated agents inherit the selected model and
scoped inference route rather than silently switching to an unrelated policy.

Here, Claude Code is the native harness and speaks Anthropic’s Messages
protocol. The models behind Synth may have different tokenizers, chat templates, tool-call grammars,
reasoning formats and streaming behavior. Supporting them requires a
model-aware compatibility layer.

The adapter renders the conversation and tool definitions using the model’s
native format, tokenizes that input, submits generation, and parses the result
back into the response the harness expects. The harness then performs the tool
action and continues the conversation.

Compatibility also includes the selected model's context and output limits,
and model-native token counting, so the harness can manage context against the
backend it is actually using.

For example, a model’s native request to run `pytest` must become the structured
tool-use response Claude Code expects. The harness executes the command in the
repository environment. Its output then becomes an observation in the next
model-native prompt. The learning record retains the actual generated tokens
and their probabilities alongside that tool cycle.

<figure class="platform-figure platform-wide" id="native-model-path" aria-labelledby="native-caption">
  <picture><source media="(max-width: 760px)" srcset="/assets/synth-platform/native-model-mobile.svg" width="420" height="1290"><img src="/assets/synth-platform/native-model.svg" width="1000" height="470" alt="A native coding agent sends conversation and tool definitions to the model adapter, which applies the model's template and tokenizer, samples from a model backend, and parses the response back to the harness. Actual prompt tokens, generated tokens and log probabilities are retained alongside the interaction." loading="lazy"></picture>
  <figcaption id="native-caption">The model adapter preserves both sides of the interaction: the native harness receives usable responses, and the learning system receives the actual sampled-token evidence. Tool execution stays in the task environment.</figcaption>
</figure>

I built model-specific routing and adaptation across families including Qwen,
DeepSeek, Kimi and GLM, with backend selection and native rendering/parsing kept
behind explicit adapter interfaces. The inference layer and training admission
have separate capability checks: a route can be useful for inference without
being a model that the selected training backend can optimize.

For training, the Proxy retains the model-native record of each call: prompt
token IDs, generated token IDs and the generation policy’s log probabilities.
Those values come from the sampling path itself and are joined to their
interaction and task attempt. The native response and learning record come
from the same prepared prompt and sampled output; reconstructing a usable tool
response does not replace the original tokens with a new tokenization.

A displayed transcript is not a complete substitute. Chat templates, tool
syntax, reasoning and tokenization affect what the model actually saw and
generated. The harness can also change the context supplied to a later call.
Per-call capture preserves those inputs, so the learning path follows the
contexts the harness used without assuming that every prompt contains the full
displayed history.

### Separate serving from evidence publication

Model adaptation also has its own scaling constraints. Rendering long prompts,
tokenizing them and parsing model output are CPU work; they should not block the
HTTP event loop that manages concurrent requests. I separated that work into a
dedicated worker pool, with independent admission for generation and token-count
requests.

For the Qwen path, I also implemented exact-token prefix reuse across growing
conversations. A bounded cache is scoped by owner, credential, model, native
session and delegated-agent identity. It reuses a completed-turn prefix only
when its rendered text matches exactly, then tokenizes the new suffix. This
reduces repeated local tokenization without changing the prompt supplied to
the model.

Evidence has a separate lifecycle. For captured calls, the service stages the
interaction before returning the completed response. Response-delivery settlement
hands the staged record to a bounded publisher, which obtains an upload grant,
transfers the payload and commits its reference. Foreground model preparation,
staging and publication have separate execution resources. A slow bulk transfer
does not have to occupy the agent's response path, while capture retains an
explicit custody boundary.

## One execution core for evaluation and training

I organized execution, evaluation and training around one common unit:
**one task, one frozen agent snapshot and a requested number of attempts**.
Runtime calls this a sampling group. The snapshot includes the effective model
and harness configuration used by that group.

Multiple groups can execute concurrently. Each attempt gets an isolated task
environment and a stable correlation identity connecting its execution,
assessment, artifacts and model interactions. The runner handles the
Harbor/environment lifecycle; the agent performs the work inside it.

In the profile-based execution path, a Runtime worker coordinates an accepted
run and fans its independent attempts out to remote task environments. Model
inference and training run in separate computation services. The work is
distributed across those environments and services; the worker coordinates the
experiment’s state and results.

This core supports three uses:

- **Unscored execution** returns the work and artifacts.
- **Evaluation** aggregates the outcomes and assessments of a fixed setup.
- **Training** adds the evidence preparation and model-update path to those
  same task attempts.

Evaluation does not need to initialize an optimizer or construct training
datums. Training does not need a second task-execution architecture. The two
operations share sampling and diverge at the point where their purposes differ.

### Scale follows resources and independent work

A plan sets total work; resource admission controls what can run at once.
Runtime tracks active attempts, CPU, memory and storage against the execution
budget, using task metadata and supported overrides for sandbox shape and phase
deadlines. Heterogeneous tasks can execute concurrently within those limits.

For example, several memory-heavy repository builds can fill the RAM budget
while trial slots remain available. Further admission waits for the resources
it needs. The model service can meanwhile have a different bottleneck, and
trajectory export can use its own concurrency limit. One global semaphore
would not describe those constraints well.

Runtime reads the selected immutable dataset version in pages. The control
request carries its identity and authority; the client does not have
to expand a large dataset into a giant submission. Task materialization and
preparation happen as part of the execution path.

The operator submits an experiment and consumes its outputs; the platform
manages workers, task environments, model access and lifecycle. Workload size,
active task resources and model-computation throughput are separate controls.

## From experience to learning

The training path turns scored agent experience into model updates. In the
group-relative setup, Runtime samples several attempts at the same task from
the same agent snapshot. Their assessed outcomes provide a relative learning
signal for that task.

For a coding task, one attempt may produce a correct repair and another may
produce a partial solution. Each attempt can contain many model calls and tool
interactions. The task assessment belongs to the trajectory as a whole; the
individual generating interactions supply the token-level learning inputs.

<figure class="platform-figure platform-wide" id="learning-loop" aria-labelledby="learning-caption">
  <picture><source media="(max-width: 960px)" srcset="/assets/synth-platform/learning-loop-mobile.svg" width="420" height="1240"><img src="/assets/synth-platform/learning-loop.svg" width="1000" height="620" alt="Training loop: select tasks and a frozen agent snapshot, execute repeated attempts, combine task assessments with exact model interaction evidence, prepare group-relative training inputs, submit forward and backward work, update the model and save a sampler and checkpoint for subsequent work." loading="lazy"></picture>
  <figcaption id="learning-caption">Repeated task attempts connect environment-level outcomes to token-level learning. The next batch captures the newly synchronized model while retaining the selected harness recipe.</figcaption>
</figure>

The implemented path is GRPO-style LoRA training through Tinker. Tinker
Cookbook centers rewards within each task group to produce relative advantages,
then constructs the learning datums. The relative outcome weights the behavior
sampled by each trajectory.

Before datum construction, Runtime joins each assessment to its originating
attempt and model records, validates finite rewards and checks output-token /
log-probability alignment. The learning inputs use the actual prompt tokens,
sampled output tokens and generation-policy log probabilities.

Eligibility is settled before relative advantages are computed. A valid zero
reward is a learning outcome; absent or invalid trainable evidence is a different
state. Runtime qualifies the retained trajectories, applies the group's
eligibility and signal requirements, and records exclusions before constructing
the learning inputs. An attempt must not change its siblings' advantages and
then disappear because its evidence could not be used.

Within an attempt, generated action tokens receive its group-relative
advantage. Observations provide context and receive zero advantage: the
optimizer is not being taught to generate the shell’s output as though the
agent wrote it.

Captured calls from the actor's delegated agents follow the same rule: their
sampled outputs are actions in their own contexts. A child's answer, returned
as a tool result, is context for its parent. These calls share the attempt's
group-relative advantage.

Cookbook merges successive interactions while the next prompt extends the
previous prompt and generation. When that prefix relationship breaks, it
starts another training datum. A multi-turn trajectory can therefore yield
several datums while following the contexts the harness actually used. The
default trainer passes the captured generation-policy log probabilities and
these advantages to Tinker’s importance-sampling loss.

Harbor supplies task/trial execution. Tinker and its
[Cookbook](https://github.com/thinking-machines-lab/tinker-cookbook) supply model
computation and learning primitives. I built the native-agent execution and
model adapters, the joins from task outcomes to token-level learning inputs,
and the coordination that advances usable model state.

### Overlap the work, preserve the policy boundary

Agent attempts have uneven runtimes. Some complete quickly; others spend longer
using tools or solving the task. I implemented a grouped pipeline so a ready
group can export evidence, prepare datums and submit forward/backward work
while other groups in the same batch are still sampling.

<figure class="platform-figure platform-wide" id="group-pipeline" aria-labelledby="pipeline-caption">
  <picture><source media="(max-width: 960px)" srcset="/assets/synth-platform/group-pipeline-mobile.svg" width="420" height="770"><img src="/assets/synth-platform/group-pipeline.svg" width="1000" height="480" alt="Conceptual timeline of three groups sampling from one model snapshot. Fast groups begin evidence preparation and forward/backward work while a slow group continues sampling. The optimizer step follows submission of the batch's contributions; the next batch uses the new sampler." loading="lazy"></picture>
  <figcaption id="pipeline-caption">Conceptual ordering, not measured durations. Independent stages overlap; the batch retains one deliberate model-update boundary.</figcaption>
</figure>

Sampling and training use distinct state interfaces. Each group generates
through the batch’s captured sampler, S₀, while the trainer accumulates learning
contributions. A ready group can submit its work as slower groups continue
sampling through S₀.

When a batch has eligible learning contributions, the coordinator waits for its
groups to settle and their contributions to be submitted, then enqueues the
optimizer step in the backend’s ordered operation stream. It settles that work,
saves the next sampling snapshot, S₁, and binds the following batch to it. The
harness recipe stays fixed across that model transition.

This overlaps independent work while preserving the policy boundary. Every
attempt in the current batch keeps its captured sampler, S₀; the next batch
uses S₁.

### Checkpoints are usable model state

Training produces more than a scalar metric. Runtime coordinates saved
inference weights, the sampler used for subsequent generation, and the trainer
state needed for supported optimization continuation. Its resumable state also
tracks the dataset position and acknowledged training progress.

An operator can inspect a checkpoint, bind its saved model to the same harness
recipe and evaluate it on another task set. Starting new training from that model and continuing
compatible optimizer state are distinct choices. The checkpoint’s model
lineage, ownership and training context remain associated with its identity.

Resumability also includes the boundary around a remote optimizer step. Before
enqueueing it, the lifecycle durably marks the update as unresolved;
acknowledged progress is recorded separately. An unresolved update blocks
automatic continuation: a missing acknowledgement is not treated as permission
to repeat the update or advance the dataset cursor. A saved checkpoint and an
outstanding remote mutation are distinct pieces of state.

This closes the practical loop: task experience can produce a new model, and
that model can return to the same native agent for further work or evaluation.

## A managed service around the learning loop

The Runtime is only part of the platform. Turning it into a remotely operable,
shared service requires durable admission, bounded execution authority,
authorized storage and a useful inspection surface.

### Durable jobs and scoped execution

Gateway resolves the dataset, actor and optional judge, checks their authority,
and pins the accepted specification. I made acceptance one database transaction
containing the run, immutable specification and authoritative creation event.
Exact submission retries return that accepted identity. Workers can claim the
job only after its execution prerequisites are durably ready. Organization-level
admission governs jobs; Runtime admits the actual task resources within each job.

The customer identity, worker service identity and authority for an individual
attempt are distinct. Workers claim accepted work and receive scoped execution
credentials. Per-trial model access is bound to the run, attempt, owner and
selected model; the sandbox receives scoped model access rather than a shared
provider key. Heartbeats maintain ownership and convey cancellation.

At the managed-run boundary, PostgreSQL checks the worker’s active execution
attempt and identity inside the transaction that appends progress or commits
completion. Progress retries are deduplicated by that attempt’s local sequence.
Completion locks the run and its current worker attempt, checks the final event
boundary and transitions both together. Ownership therefore governs the actual
state changes, not just the initial API request.

### Metadata and bulk data take different paths

Training trajectories and task archives can be large. Sending every payload
through the authorization service would tie data throughput to the control
plane’s memory, bandwidth and request handling.

For task materialization and training evidence, I separated those paths.
Gateway authorizes transfers and commits canonical references. Producers and
consumers transfer payload bytes directly to and from object storage.
PostgreSQL retains the relationships, lifecycle facts and object references
needed to inspect and authorize them.

<figure class="platform-figure" id="data-custody" aria-labelledby="custody-caption">
  <div class="custody-control"><span class="diagram-label">Control + authority</span><strong>Gateway ↔ PostgreSQL</strong><span>Owner · run · permissions · object identity · durable references</span></div>
  <div class="custody-grants"><span>Authorize exact transfers</span><span>Commit verified references</span></div>
  <div class="custody-data"><div><strong>Producer</strong><span>Task package, interaction evidence or artifact</span></div><span class="custody-arrow" aria-hidden="true">→</span><div><strong>Object storage</strong><span>Immutable payload bytes</span></div><span class="custody-arrow" aria-hidden="true">→</span><div><strong>Consumer</strong><span>Task runner, training preparation or authorized readback</span></div></div>
  <figcaption id="custody-caption">Authorization and durable metadata remain centralized. Large payloads use direct, scoped data paths rather than being relayed through the control service.</figcaption>
</figure>

The transfer contract binds an object’s identity, expected size and digest to
its allowed operation. Publication joins the stored bytes to an authorized,
durable reference. Consumers verify the intended payload before materializing
or using it. A content reference can be shared between components without
copying the same evidence merely to change which service refers to it.

I designed the canonical interaction-storage contract around exact, create-only
uploads and provider-verifiable full-object SHA-256 checksums. Gateway can verify
what it publishes from provider metadata without downloading the trajectory
itself. This preserves both direct data movement and a precise publication
boundary.

### Cloud delivery, networking and credentials

I built the native-agent inference service’s cloud delivery boundary on the
team’s Kubernetes/Azure substrate. Public ingress exposes native model traffic
and readiness; service control uses a separate authenticated path. Application
releases use pinned images and Helm configuration, while infrastructure owns
the network, durable staging and credential-delivery substrate.

Dedicated workload identities read the required credential objects. A secret
controller materializes exact versions into credential generations that
application releases consume by reference. This keeps secret values out of
agent recipes, Terraform plans and Helm configuration, while preserving the
selected credential generation for release and rollback. Worker lifecycle
handling coordinates claimed work, heartbeats, cancellation and shutdown.

The key separation is between the **agent’s permissions inside its work
environment** and the **platform’s authority to operate infrastructure**. A
task-performing agent can be equipped with powerful tools in its sandbox
without receiving the operator’s database, cluster or model-provider
administration credentials.

### Inspection is part of the interface

Long-running work should be observable from another terminal or machine.
Gateway retains ordered events and result references so inspection does not
depend on finding a particular worker process. Clients can reconnect to an
event stream from a cursor and return to the same run identity.

I designed inspection around experimental lineage: which frozen agent produced
each attempt, which trials and token spans supplied a training group's signal,
and which groups contributed to a model update. The retained records connect
that evidence to the successor model snapshot and checkpoint. Large token
payloads stay in artifacts; bounded evidence chunks preserve the exact
references without forcing a whole trajectory into a control-plane event.

The Go CLI exposes human-readable views and structured JSON for automation.
Status, events, artifacts, task attempts, learning updates and checkpoints are
separate useful views of the experiment. Bulky outputs remain downloadable
artifacts rather than being forced into terminal messages.

This matters both for a researcher monitoring training and for another agent
operating the platform. A program can submit work, retain its handle, inspect
the outputs and decide what to do next through the same interface a human
uses.

## What this made possible

I used the platform for training and evaluation campaigns involving tens of
thousands of agent attempts, repeated model updates and checkpoint continuation.
Actual workloads included [R2E-Gym repository tasks](https://github.com/R2E-Gym/R2E-Gym) from public Python projects
such as pandas, NumPy and aiohttp, with task-specific tests and pinned
environments. Other task collections used the same execution and learning
machinery: the task package defines the work and assessment.

The largest campaigns exercised the execution and learning core before the
later profile abstraction and unified managed interface.

The system was deployed and exercised internally in the development
environment; it is not generally available. The public documentation and CLI
releases provide inspectable interfaces to the work.

Profiles gave task-specific actors and judges a common execution format. I used
these boundaries in subsequent work on task factories and repository-specific
reviewer construction: an agent-producing workflow can return a runnable recipe
that a task-performing workflow consumes. The companion article,
[From real software work to specialized agents](/from-software-work-to-specialized-agents/),
explains the task production, knowledge construction and applied workflows.

My contribution was the design and implementation across these boundaries:
native-agent/model integration, distributed task and learning orchestration,
reusable profiles, durable data contracts, managed control, and the CLI and
cloud systems that expose them as one capability. I built this with the
SynthLabs team and extensive use of coding agents, adopting existing execution
and model-computation foundations where they fit.

## Further reading

- [From real software work to specialized agents](/from-software-work-to-specialized-agents/)
- [How Synth fits together](https://synthlabs.mintlify.app/concepts/product-model)
- [Agent profiles](https://synthlabs.mintlify.app/concepts/profiles-and-candidates)
- [Tasks and versions](https://synthlabs.mintlify.app/concepts/tasks-and-versions)
- [Managed execution](https://synthlabs.mintlify.app/guides/managed-execution)
- [Training and checkpoint comparison](https://synthlabs.mintlify.app/guides/managed-training)
- [CLI command reference](https://synthlabs.mintlify.app/reference/cli)
- [Public CLI releases](https://github.com/SynthLabsAI/synth-releases/releases)

<style>
  .platform-contents { font-size: 12px; line-height: 2; margin: 30px 0 44px; }
  .platform-contents a { display: inline-block; padding: 3px 0; }
  .platform-figure { margin: 38px 0 42px; }
  .platform-figure figcaption { max-width: 660px; margin: 14px auto 0; }
  .platform-wide { width: min(1000px, calc(100vw - 56px)); position: relative; left: 50%; transform: translateX(-50%); }
  .platform-figure picture, .platform-figure img { display: block; width: 100%; }
  .platform-figure img { height: auto; border: 1px solid var(--rule); background: #fff; }
  .experiment-inputs { display: grid; grid-template-columns: 1fr 1fr; border-top: 1px solid var(--fg); border-left: 1px solid var(--rule); }
  .experiment-inputs > div { padding: 18px; border-right: 1px solid var(--rule); border-bottom: 1px solid var(--rule); }
  .experiment-inputs strong, .experiment-inputs span, .experiment-inputs small { display: block; }
  .experiment-inputs strong { font-size: 12px; text-transform: uppercase; letter-spacing: .06em; margin-bottom: 7px; }
  .experiment-inputs span { font-size: 13px; font-weight: 700; line-height: 1.5; margin-bottom: 7px; }
  .experiment-inputs small { font-size: 12px; line-height: 1.7; color: var(--dim); }
  .experiment-join { text-align: center; padding: 5px 0; font-size: 25px; }
  .experiment-run { padding: 18px; border: 1px solid var(--fg); background: var(--surface); text-align: center; }
  .experiment-run strong, .experiment-run span { display: block; }
  .experiment-run span { font-size: 12px; line-height: 1.7; margin-top: 6px; }
  .diagram-label { display: block; text-transform: uppercase; letter-spacing: .07em; font-size: 11px; margin-bottom: 9px; color: var(--dim); }
  .profile-model, .profile-harness { padding: 20px; border: 1px solid var(--fg); }
  .profile-model strong, .profile-model > span:last-child { display: block; }
  .profile-model > span:last-child { font-size: 12px; margin-top: 7px; color: var(--dim); }
  .profile-separator { font-size: 25px; text-align: center; padding: 5px 0; }
  .profile-grid { display: grid; grid-template-columns: 1fr 1fr; gap: 9px 20px; font-size: 12px; }
  .profile-grid span { padding: 6px 0; border-bottom: 1px solid var(--rule); }
  .profile-bindings { display: grid; grid-template-columns: 1fr 1fr; gap: 22px; margin-top: 16px; font-size: 12px; }
  .custody-control { padding: 20px; border: 1px solid var(--fg); text-align: center; }
  .custody-control strong, .custody-control > span:last-child { display: block; }
  .custody-control > span:last-child { font-size: 12px; margin-top: 8px; }
  .custody-grants { display: flex; justify-content: space-around; gap: 15px; font-size: 11px; padding: 15px 0; color: var(--dim); }
  .custody-grants span::before { content: "↓ "; color: var(--fg); }
  .custody-grants span:last-child::before { content: "↑ "; }
  .custody-data { display: grid; grid-template-columns: 1fr 22px 1fr 22px 1fr; align-items: center; gap: 5px; }
  .custody-data > div { padding: 16px 12px; border: 1px solid var(--fg); align-self: stretch; }
  .custody-data strong, .custody-data div span { display: block; }
  .custody-data strong { font-size: 12px; }
  .custody-data div span { font-size: 11px; line-height: 1.7; margin-top: 8px; color: var(--dim); }
  .custody-arrow { text-align: center; font-size: 22px; }
  .role-modes { border-top: 1px solid var(--fg); }
  .role-lane { padding: 18px 0; border-bottom: 1px solid var(--rule); }
  .role-lane > strong { display: block; font-size: 12px; text-transform: uppercase; letter-spacing: .05em; margin-bottom: 12px; }
  .role-flow { display: grid; grid-template-columns: 1fr 18px 1fr 18px 1fr; gap: 8px; align-items: center; font-size: 12px; line-height: 1.7; }
  .role-flow span { padding: 13px 10px; border: 1px solid var(--rule); align-self: stretch; display: flex; align-items: center; }
  .role-flow b { text-align: center; font-size: 18px; font-weight: 400; }
  .role-lane small { display: block; color: var(--dim); font-size: 11px; margin-top: 10px; }
  @media (max-width: 960px) {
    #learning-loop, #group-pipeline { width: 100%; position: static; transform: none; }
    #learning-loop picture, #group-pipeline picture { max-width: 480px; margin: 0 auto; }
    #learning-loop img { aspect-ratio: 420 / 1240; }
    #group-pipeline img { aspect-ratio: 420 / 770; }
  }
  @media (max-width: 760px) {
    .platform-wide { width: 100%; position: static; transform: none; }
    .platform-wide picture { max-width: 480px; margin: 0 auto; }
    #platform-architecture img { aspect-ratio: 420 / 1650; }
    #native-model-path img { aspect-ratio: 420 / 1290; }
  }
  @media (max-width: 620px) {
    .role-flow { grid-template-columns: 1fr; gap: 6px; }
    .role-flow b { transform: rotate(90deg); line-height: 1; }
    .experiment-inputs { grid-template-columns: 1fr; }
    .experiment-inputs > div { padding: 16px; }
    .profile-grid, .profile-bindings { grid-template-columns: 1fr; gap: 7px; }
    .custody-grants { flex-direction: column; text-align: center; gap: 4px; }
    .custody-data { grid-template-columns: 1fr; gap: 8px; }
    .custody-data > div { padding: 16px; }
    .custody-data strong { font-size: 13px; }
    .custody-data div span { font-size: 12px; margin-top: 4px; }
    .custody-arrow { transform: rotate(90deg); line-height: 1; }
  }
</style>

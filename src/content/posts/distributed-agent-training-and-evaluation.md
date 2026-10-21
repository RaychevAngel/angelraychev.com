---
title: "Building a distributed platform for agent training and evaluation"
description: "The architecture and engineering behind SynthLabs’ agent platform: native harnesses, exact training evidence, distributed execution, model updates and reusable agent profiles."
updated: 2026-10-20
---

At SynthLabs, I designed and built a distributed platform for evaluating and
training tool-using agents. An operator supplies tasks, an agent configuration
and a plan; the service runs isolated trials, retains their evidence,
coordinates model updates and exposes checkpoints usable through the same
native agent. My work connected the Go CLI, authenticated control plane,
sandbox runtime, inference proxy, storage contracts and cloud delivery.

That sounds straightforward until the agent runs for twenty minutes, makes
dozens of model calls, uses tools, encounters infrastructure failures, and
finishes while other trials are still running. Now a training example is not a
row in a dataset. It is the result of a distributed computation whose model,
inputs, actions, assessment and failure state must still agree.

We deployed and exercised that loop internally. Four retained July campaigns
alone contain 21,500 distinct recorded rollout sessions. A later controlled
managed run went from CLI submission through scored Harbor trials, two optimizer
updates, checkpoint publication and subsequent inference. These are different
execution paths; their evidence and limits are described [below](#what-actually-ran).

I drove this work with the SynthLabs team, using coding agents extensively.
Native Claude Code, Harbor, sandbox providers and Tinker supplied the agent,
execution and model-computation foundations.

**Status:** deployed and exercised internally in the development environment;
not generally available. Public [documentation](https://synthlabs.mintlify.app/)
and [CLI releases](https://github.com/SynthLabsAI/synth-releases/releases) make
the interface inspectable; managed execution requires authorized access.

*[Architecture](#architecture-control-execution-inference-and-learning) ·
[Learning loop](#a-rollout-is-not-yet-training-data) ·
[Agent profiles](#preserve-the-agent-not-just-the-model-name) ·
[Distributed state](#distributed-authority-and-data-custody) ·
[Execution evidence](#what-actually-ran)*

## What the platform makes possible

An operator supplies work, an agent and an execution plan. They do not have to
assemble a new collection of sandbox scripts, inference credentials, trajectory
exporters and training jobs for each experiment.

The same underlying machinery supports three different purposes:

- **Execution:** perform the work and collect outputs, possibly without scoring.
- **Evaluation:** hold the agent setup fixed, repeat the work, and retain the
  outcomes and assessments needed to compare it with another setup.
- **Training:** collect scored experience, construct valid learning examples,
  update a supported model and advance the sampler used by subsequent work.

Those operations should share execution infrastructure without becoming the
same operation. Evaluation does not need to export every trajectory for
gradient computation. Training needs substantially more than a successful task
result and a number called `reward`.

This separation also lets us ask a useful question: **what changed the agent?**
We can change its instructions, tools or context without changing its weights.
We can train a new checkpoint while holding the harness fixed. Or we can change
the tasks and assessment deliberately. If those changes are mixed together
implicitly, an experiment can finish without telling us what improved.

A **trial** is one attempt at a task; repeated attempts at that task form a
**group**. A training batch selects groups for a shared update boundary. Model
calls are retained as **Interactions**, linked to the Session and trial that
produced them, while the **sampler** selects the model state used to generate
them. These units must not
be confused with tasks, tokens or gradient updates.

The CLI calls the task-performing agent the **actor**. For an authorized
operator, the interface looks like this:

```sh
synth run start --dataset acme/evaluation@v1 --actor @agent.json --plan @eval-plan.json
synth train start --dataset acme/practice@v1 --actor @agent.json --plan @train-plan.json
synth run show <run-id>
synth run checkpoints <training-run-id>
synth checkpoint show <checkpoint-id>
```

These illustrate the documented interface, not commands executed for this
article. The example references must be replaced with accessible dataset
versions, prepared profiles and plans; training also needs a supported model
configuration. Submission returns the run identity used by the inspection
commands. Adding `--dry-run` previews a submission without starting the work.

## Architecture: control, execution, inference and learning

The platform is split into components with different responsibilities.

| Component | Responsibility |
| --- | --- |
| `synth` | The operator-facing CLI: authentication, tasks, agent profiles, submission, inspection, artifacts and checkpoints. |
| `sprite-gateway` | The authenticated control plane: customer scope, accepted specifications, durable identities, admission and customer readback. |
| `agent-rl-runtime` | Remote trial orchestration, evaluation, evidence qualification, training coordination and recoverable progress. |
| `managed-agent-proxy` | Supported model routing, native-agent protocol adaptation and faithful interaction evidence. |
| PostgreSQL and object storage | Durable relational authority and large immutable payloads, with explicit publication between them. |
| Kubernetes/Helm and sandbox providers | Service delivery, worker lifecycle, resource admission and isolated task execution. |

<figure id="platform-architecture" class="platform-architecture" aria-labelledby="platform-architecture-caption">
  <div class="platform-lane"><strong>Control</strong><p><span>synth CLI</span><b aria-hidden="true">↔</b><span>Gateway</span><b aria-hidden="true">↔</b><span>Runtime</span></p></div>
  <div class="platform-lane"><strong>Task execution</strong><p><span>Runtime</span><b aria-hidden="true">→</b><span>Harbor</span><b aria-hidden="true">→</b><span>Agent + tools in sandbox</span></p></div>
  <div class="platform-lane"><strong>Inference</strong><p><span>Native agent</span><b aria-hidden="true">↔</b><span>Proxy</span><b aria-hidden="true">↔</b><span>Model provider</span></p></div>
  <div class="platform-lane"><strong>Learning</strong><p><span>Runtime</span><b aria-hidden="true">→</b><span>Tinker update</span><b aria-hidden="true">→</b><span>Sampler for next batch</span></p></div>
  <div class="platform-lane"><strong>Durable state</strong><p><span>Gateway + PostgreSQL</span><b aria-hidden="true">·</b><span>Direct object transfers</span></p></div>
  <figcaption id="platform-architecture-caption">The principal responsibility paths, not a complete network topology. Model inference and gradient computation are services; the task’s agent and tools execute in a separate sandbox. In the inference/training evidence path, Gateway authorizes transfers and records references while bulk payloads move directly to or from object storage.</figcaption>
</figure>

Follow one training run: Gateway authenticates the request and commits a durable
run identity. Runtime claims it and schedules groups of sandboxed agent trials.
Each agent calls its model through Proxy, which retains the interaction evidence.
Runtime joins those interactions to task assessments, submits valid gradient
contributions, and publishes the next checkpoint and progress state. The CLI
reads the same durable records during execution and after it finishes.

Tinker supplies model computation and optimizer state. [Harbor](https://github.com/harbor-framework/harbor)
supplies task and agent execution machinery; Daytona is one remote execution
provider. My work connected those services into one inspectable learning loop,
with explicit contracts for native-agent behavior, learning evidence, update
ordering, durable publication and recovery. The operator-facing result is a
serverless execution surface: submit work and inspect durable results without
provisioning the workers.

## Native Claude Code with a supported open-weight model

I wanted agents to retain a capable, familiar harness rather than move to a
reduced custom loop merely because we wanted to train a different model.

Claude Code speaks an Anthropic-style interface. A supported open-weight model
may use a different conversation template, tool-call syntax, thinking format,
sampling policy and context budget. Bridging those is not just changing a base
URL and renaming a model.

The Proxy normalizes the incoming conversation, chooses the authorized model
route, and uses a model-specific adapter to render the conversation with that
model’s native template. It samples once, parses the result, and reconstructs
the text, thinking and tool-use blocks expected by the native harness.

For a successfully reconstructed response, the learning evidence comes from the
same sampled request: actual prompt token IDs, generated token IDs and their
sampling log probabilities.
It does not reconstruct a plausible training trace by retokenizing the text
shown to the user afterward. Tool formatting, retained thinking and context
compaction can all make those representations differ.

Provider capabilities matter. A route that returns useful text but not the
required token-aligned log probabilities is not automatically a trainable
route. Unsupported model or capability combinations should reject explicitly,
not silently fall back to a superficially similar configuration.

Likewise, a malformed response or an ambiguous provider failure must not trigger
an invisible second model sample. One recorded attempt must correspond to the
sample that actually occurred. Protocol compatibility and honest experiment
accounting are the same engineering problem at this boundary.

## A rollout is not yet training data

A successful task run can still be unusable for training. The optimizer needs
the tokens the model actually sampled and the assessment of that same attempt.
Joining a reward to the wrong trajectory assigns feedback to different actions;
reconstructing tokens from displayed text can break their alignment with the
recorded sampling probabilities.

Each started sampling group asks for an exact number of trials and accounts for
that many outcomes. A failed or cancelled trial is still an
outcome; it does not disappear because it is inconvenient for the denominator.
Trial identities are assigned before execution and checked on return.

Training then applies a separate evidence policy. It needs the task assessment,
the corresponding agent trajectory and valid model-token evidence, joined to
the same trial. Ordinary trial failures can be excluded with a reason. A wrong
owner, corrupt payload or mismatched trajectory identity is not an ordinary bad
sample to ignore: it can invalidate the operation.

The simplest distinction is also one of the most important:

**A reported reward of zero is valid assessment feedback. A missing reward means
there is no assessment value to use. They are not interchangeable.**

For example, consider three attempts with rewards `0`, `1` and no reward.
Subject to the other evidence checks, the first two can supply a relative
learning signal. The third is still an accounted attempt, but it must not be
silently turned into another zero. The meaning of the reward scale belongs to
the task’s assessment, not to the infrastructure.

For grouped relative-policy training, the comparison is between repeated
attempts at the same task. A group needs enough surviving assessed trials and
some relative reward signal. Equal rewards provide no comparative signal.
Evidence loss can remove the only successful trial, so the check has to happen
again after trajectory export—not just before it.

The Runtime joins the valid trajectories to their task rewards and delegates
GRPO (group-relative policy optimization) advantage calculation and datum assembly
to [Tinker Cookbook](https://github.com/thinking-machines-lab/tinker-cookbook). It retains
the mapping back to original trials and interactions. A multi-step agent
trajectory can generate multiple training datums; a datum count is not a task
count or a trial count.

The training path consumes the ordinary Session export rather than maintaining
a second, privileged approximation of the conversation. Size, digest and
token-count checks sit at that boundary, and local materialization is installed
atomically only after validation. A trajectory becoming a local file is not
enough; it must be the intended complete trajectory.

These checks define the learning input. Exact token/logprob alignment, immutable
references, finite rewards, trial correlation and explicit exclusions determine
what the optimizer is actually being asked to learn from.

## Pipeline the work without losing the update boundary

Agent runtimes are uneven. One group finishes quickly; another spends most of
its time in a slow tool or a difficult task. Waiting for every rollout before
beginning all evidence preparation and model computation wastes useful overlap.

I implemented a grouped pipeline: as a group finishes, the Runtime can export
its evidence, prepare datums and enqueue forward/backward work while sibling
groups are still sampling. The model computation backend also supports an
ordered asynchronous submission interface.

But the algorithm retains a deliberate boundary:

1. Every group in the batch receives the same captured agent/model snapshot.
2. Independent groups sample and prepare evidence concurrently.
3. Each eligible group submits its gradient contribution when ready.
4. Only after all groups settle and contributions are submitted does the
   coordinator enqueue the batch’s optimizer step.
5. It settles the submitted operations, saves a synchronized sampler and uses
   that sampler for the next batch.

The host need not wait for every individual gradient acknowledgement before
enqueuing the optimizer into the provider’s ordered operation stream. What
matters is the contribution set and ordering, followed by reconciliation before
the next model snapshot is used.

One focused test blocks a slow group and observes a fast group’s forward/backward
submission while the optimizer call count remains zero. Releasing the slow
group produces one optimizer update. Other tests cover draining already-submitted
work when a sibling fails or cancellation arrives.

This overlaps expensive work without quietly turning the experiment into
stale-policy asynchronous RL.

### A timeout is not proof that the optimizer did nothing

A remote optimizer operation can succeed while its acknowledgement is lost.
Blindly repeating it can apply an update twice; blindly skipping it can resume
from the wrong policy and task position.

Before dispatching an optimizer step, the managed lifecycle can durably record
that its outcome is unresolved: a **write-ahead, unknown-outcome hold**. If the
process dies or the acknowledgement is lost, recovery must reconcile the
operation before continuing; it cannot infer that no update happened. A
resumable state binds the model/optimizer checkpoint, sampler, dataset and
cursor, while acknowledged updates remain distinct from intended steps.

The same principle applies to cancellation. Already-submitted provider work has
to be reconciled or drained. Killing a local process does not retroactively
cancel a remote mutation. Sampling weights, resumable training state including
optimizer state, and platform progress are different facts with different
recovery meanings—even when a provider packages some of them together.

## Preserve the agent, not just the model name

Capturing model calls controls only part of the experiment. A coding agent also
has an execution engine, instructions, files, skills, hooks, permissions, tools,
setup, working directory and a policy for consuming the task. Those choices can
change its behavior independently of its weights.

In September, I developed the reusable **agent profile** to make that complete
behavior explicit. A profile can carry a pinned engine version, packaged files
or immutable bundles, setup and native command arguments, environment bindings,
instruction delivery and required outputs. It is credential-free: declaring an
environment binding does not grant the authority to populate it with a secret.

The important boundaries are:

| Object | What it fixes |
| --- | --- |
| Task and task version | The work, starting environment and default verification. |
| Agent profile | A starting model selector and executable harness recipe. |
| Verifier or judge | How the outcome is assessed; a judge may have its own profile. |
| Plan | Work amounts and explicit execution settings. |
| Run | What was accepted and what actually happened. |
| Checkpoint | A particular saved model state, not the entire agent. |

The implementation uses **one Go launcher** for local execution and the
managed Harbor path. The Python runtime adapter supplies task, run and model
bindings; it does not independently reinterpret the profile into another agent.
Setup and execution are joined by a receipt for the selected recipe and engine.
Arguments are passed as literal arguments rather than silently evaluated as a
shell command.

Actor and judge are roles, not two incompatible kinds of agent configuration.
Both use the same complete profile format. The task, scoring selection and run
plan remain separate from those profiles; server-derived execution pins do not
silently rewrite the submitted experiment.

One test makes the intent concrete. Given the same task instruction, one
profile pipes it to the agent, another supplies a file path, and another ignores
it. A recorder checks the actual arguments, standard input, working directory
and environment. The launcher must not helpfully insert the instruction through
a second, hidden channel. A separate Runtime test exercises the actual Go
launcher through its Python adapter with a deterministic stand-in engine.

This tests whether the profile really determines execution. A training update
can replace the effective sampler without quietly changing the selected harness
or judge. Source profile identity and the effective model/sampler binding are
recorded separately: new weights do not have to mean a rewritten recipe.

Profile identity also has to survive the Python–Go boundary. The CLI verifies
the server’s exact canonical JSON bytes and digest instead of assuming two
encoders will serialize numbers and Unicode identically. Publication uses replay
keys and expected-current-version checks, so retrying a request is not a new
publication and a concurrent edit cannot silently replace another version.

## Distributed authority and data custody

A remote run crosses several boundaries: an authenticated customer, an admitted
job, a worker attempt, a sandbox, a model route and retained artifacts. Passing
one broad credential through all of them would be simple to implement and hard
to reason about.

The Gateway is the public authority boundary. Its database accepts the run,
immutable specification, resource reservation and initial event together.
An identical replay returns the original identity; a divergent replay conflicts.
Workers cannot claim execution before required external setup has been committed.

This prevents a familiar distributed failure: acceptance partially succeeds,
the caller retries, and the system starts another expensive job or exposes a
half-prepared one. Worker leases and attempt fences then prevent an obsolete
attempt from continuing to publish as though it still owns the run.

The inference/training evidence data plane is deliberately different from its
control plane. Large token arrays and artifacts need not be relayed through
Gateway merely because Gateway authorizes them. In this path, producers and
consumers transfer payloads directly to or from object storage under scoped
permissions; Gateway verifies and commits the corresponding references. This
keeps authorization and publication explicit without making the control service
a relay for every large payload in this path.

For an upload, the grant can bind the destination, length, content digest, type,
create-only condition and expiry. Publication is not complete just because an
upload returned success: the canonical reference must also be acknowledged.
The database and the object store serve different purposes, and their boundary
needs an explicit protocol.

Keeping canonical Interaction bytes off Gateway required more than trusting a
checksum supplied by the uploader. The checksum-capable storage path binds the
upload to exact bytes and checks the object store’s full-object checksum before
committing the reference. Otherwise, avoiding a bulk reread would quietly
weaken the integrity contract. This was a storage/API design decision, not just
a choice of where to put a file.

An early local integration test exercised that boundary against real
PostgreSQL and MinIO. The first metadata commit succeeded but its response was
deliberately lost. Replaying the same commit after the short upload grant had
expired returned the acknowledgement without another upload, replacement grant
or duplicate Interaction. This was a local composition test of an earlier
publication design, rather than a test of the deployed service.

Tenant checks, verified customer identity, workload authority, model-route
authority and artifact custody are separate layers. Credentials and transient
signed transfer material are not agent-profile content or public run artifacts.
The objective is a traceable chain of authority, not just redacting a token from
the final log.

## Operating the platform is part of building it

The implementation also includes Kubernetes/Helm delivery, worker-generation
and graceful-termination behavior, resource-aware trial admission and customer
inspection. Requested trial counts are not interchangeable with CPU, RAM, disk,
available sandboxes or provider model capacity.

For example, a concurrency semaphore is insufficient when tasks have different
resource requirements. The Runtime’s admission mechanism respects trial count,
CPU, memory and storage together. It checks each immutable task’s requirements
against its grant before creating a sandbox, waits until all dimensions fit,
and releases the allocation on completion, failure or cancellation. A small
task should not inherit an unnecessarily large default, nor should a large one
silently exceed its budget.

Model-route capacity is a different resource boundary. Loading or sampling a
model, staging its evidence and running the agent’s tools have different owners
and bottlenecks. Likewise, a Kubernetes worker being Ready is not the same as
an admitted run finishing or an external sandbox being cleaned up. Worker
delivery and disruption policies have to preserve the application’s leases,
attempt fences and draining behavior rather than substitute for them.

In the CLI, that becomes a coherent operational surface: submit a task or
dataset with a selected profile, retain the returned run identity, inspect trials
and events, retrieve results, and find the checkpoints training actually produced.
The same run history explains evaluation and training without fabricating
different identities for the same work.

A slow Session export showed why operating the platform mattered. Comparisons
between two API pods running the same image localized intermittent connection
failures to one pod. Numeric-IP probes reproduced the failure without DNS, TLS,
authentication or SQL. Replacing that Dev pod with the same image mitigated the
symptom: exports that had taken roughly 88 seconds returned in under two seconds.
The deeper node or network cause remained unproven. The investigation supported
a targeted mitigation and avoided an application or query rewrite in response
to a lower-level fault.

## What actually ran

These retained runs show different parts of the system: a managed
training-to-consumed-checkpoint path, a larger direct Runtime campaign, and
managed evaluation with complete outcome accounting. The
[structured evidence summary](/assets/synth-platform/execution-evidence.json)
records their counts and qualifications in redacted form.

Four selected July direct Runtime campaigns contain **21,500 distinct recorded
rollout sessions**, deduplicated by Session identity: 17,300 training rollouts
and 4,200 fresh evaluation attempts. This is a bounded sample, not a lifetime
total. It includes failed and resumed work; it measures agent attempts rather
than unique tasks or successful solves. Executed updates, progress on a resumed
policy lineage and saved checkpoints are recorded separately.

### A managed training-to-checkpoint path

An August 30 Dev run was submitted through the normal Synth CLI, executed four
scored Harbor trials across two groups, produced four eligible datums, performed
two optimizer updates and saved two checkpoints. The next group used the sampler
from the previous update. All nineteen artifacts finalized.

An earlier attempt performed its updates but failed final publication. It
remained a failed run: numerical training success was not substituted for a
complete, retrievable result.

A separate inference invocation consumed the final checkpoint successfully;
its retained export receipt records matching generated-token and logprob counts.
The run used deterministic synthetic rewards. It establishes execution, update,
publication and checkpoint-consumption mechanics—not an improvement in task
performance. The installed CLI was a source build, not a newly tagged public
release.

### A larger direct Runtime campaign

A retained July campaign records thirty batches and thirty optimizer updates,
with 3,000 rollout records over 300 manifest entries: 2,023 trainable and 977
excluded rollouts, producing 80,012 training datums. This was a direct
Runtime/operator experiment, not the later Gateway-managed submission path.
It used rank-1 low-rank adaptation (LoRA) of Qwen3.6-35B-A3B through Tinker and included
interruption and checkpoint recovery before its final batch. The model service
provided the gradient computation; I built and operated the surrounding agent
training system.

Recovery created a new sampler URI, and the retained checker reported a
sampler-lineage mismatch. A separate resume-aware review accepted the execution
for evaluation; the checker itself remained red. These records support the
execution-volume account, not a claim that every recovery invariant passed.
Configured concurrency is not a measured sustained-capacity guarantee.

The run illustrates why the system records trial outcomes, exclusions, updates
and checkpoint lineage separately.

### Managed evaluation with complete outcome accounting

A managed evaluation retained 100 distinct task/Session outcomes: 96
execution-completed and four errors, across 5,983 recorded model Interactions.
Scoring was recorded separately; 95 rows had a verifier reward. Its fixed task
subset and answer-key retrieval contamination rule out a benchmark-quality
claim. The execution and accounting evidence remains useful without one.

## The result

The useful result is an operator-visible chain from accepted work to trial
outcomes, eligible training evidence, optimizer updates and a checkpoint that a
separate inference invocation can consume.

The platform keeps the agent’s executable harness separate from its current
weights, and successful task execution separate from trainable evidence. Those
distinctions make an experiment interpretable: what changed, which attempts
supplied the learning signal, and what state can safely be resumed?

My work carried those distinctions across the places where they are easiest to
lose: native model protocols, Python/Go execution, concurrent Runtime work,
remote optimizer operations, database/object publication and cloud lifecycle.
That was the central engineering task: making a changing, tool-using agent into
a controlled ML workload without flattening away what made the agent useful.

## Further reading

- [How Synth fits together](https://synthlabs.mintlify.app/concepts/product-model):
  the task, agent, assessment and model-state boundaries.
- [Agent profiles](https://synthlabs.mintlify.app/concepts/profiles-and-candidates):
  the executable agent recipe.
- [Managed execution](https://synthlabs.mintlify.app/guides/managed-execution) and
  [training](https://synthlabs.mintlify.app/guides/managed-training): the operator interface.
- [Lifecycle and recovery](https://synthlabs.mintlify.app/operations/lifecycle-and-recovery)
  and [limits](https://synthlabs.mintlify.app/operations/limits).
- [Public CLI releases](https://github.com/SynthLabsAI/synth-releases/releases).
- [Training a code reviewer we actually use](/training-a-code-reviewer-we-actually-use):
  a separate, dated case study of task construction, assessment and learning.

*This account is based on repository history, original design discussions and
retained execution records. The mechanisms span July–September 2026; the
reusable recipe/profile implementation is a later stage, not an early-July
feature. Internal identities, credentials, private trajectories and company
source code are not reproduced here.*

<style>
.platform-architecture { border-top: 1px solid var(--rule); border-bottom: 1px solid var(--rule); padding: 18px 0; }
.platform-lane { display: grid; grid-template-columns: 125px minmax(0, 1fr); gap: 14px; padding: 14px 0; border-bottom: 1px solid var(--rule); }
.platform-lane:last-of-type { border-bottom: 0; }
.platform-lane strong { font-size: 12px; line-height: 1.7; }
.platform-lane p { display: flex; align-items: baseline; flex-wrap: wrap; gap: 6px 10px; margin: 0; font-size: 13px; line-height: 1.8; }
.platform-lane p b { font-weight: 400; }
.platform-architecture figcaption { margin-top: 18px; }
@media (max-width: 550px) { .platform-lane { grid-template-columns: 1fr; gap: 6px; } }
</style>

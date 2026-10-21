---
title: "From real software work to specialized agents"
description: "Task factories, independent actors and judges, and cloud workflows that construct repository-specific reviewers from code and engineering history."
image: "/assets/synth-specialists/article-cover.png"
imageAlt: "From real software work to specialized agents: task factories and repository-to-reviewer construction."
updated: 2026-10-21
---

At SynthLabs, I built systems that turn software-engineering work into two
reusable artifacts: **tasks that reconstruct the job, and agent profiles that
specialize the worker.** Task factories captured specialist assignments,
partitioned ML-framework transformations and compiled historical review
opportunities. A separate construction workflow researched repository code and
engineering history and returned a runnable, repository-specific reviewer.

The two sides solve different problems. Factories make work repeatable across
agents and model versions. Construction specializes the worker through repository
knowledge and investigation procedures, without changing model weights. Their separation lets a
workflow produce the assignment or the worker, then evaluate and improve each
independently.

The reviewer application makes this concrete: repository URLs go into
construction; a reviewer profile comes out. A second workflow takes that profile
and a PR URL, reconstructs the change, and returns a review and its artifacts.

The reviewer targets **contract-sensitive changes**: producer–consumer
guarantees, authorization and isolation, resource ownership, accounting and
lifecycle, and supported compatibility. The scope requires a concrete guarantee
and an affected execution path—not merely a change touching an API.

These workflows share task and agent-profile abstractions with my
[distributed agent platform](/distributed-agent-training-and-evaluation/).
Here I focus on constructing the assignments, specialists and application
workflows that use those contracts.

<nav class="specialist-contents" aria-label="In this article"><a href="#work-and-behavior-are-separate-artifacts">The abstraction</a> · <a href="#three-ways-to-construct-executable-work">Task factories</a> · <a href="#hold-the-work-fixed-change-the-evaluator">Actors and judges</a> · <a href="#a-creator-that-builds-the-reviewer">Constructing a specialist</a> · <a href="#knowledge-that-an-agent-can-navigate">Knowledge and retrieval</a> · <a href="#turning-context-into-investigation">Review execution</a> · <a href="#construction-and-use-as-cloud-workflows">Cloud integration</a> · <a href="#following-a-contract-across-components">An external application</a></nav>

<div class="workflow-interface" aria-label="The two workflow interfaces"><p><strong>Construct</strong><span>Repository URLs → creator task → runnable reviewer profile</span></p><p><strong>Review</strong><span>PR URL + profile → review task → review and artifacts</span></p></div>

## Work and behavior are separate artifacts

A review opportunity is more specific than a PR number. It includes the source
being compared, the available context, the responsibility assigned to the
reviewer, and the evidence that can establish whether a finding is correct.
Likewise, an agent is more specific than a model name: its tools, instructions,
setup, context and execution behavior all affect the work it can do.

I separated those responsibilities deliberately. The task supplies the starting
environment and assignment. The profile supplies the complete agent-side recipe:
model, native engine, files, setup, invocation, input handling and required outputs.
The task defines the assignment; the profile controls how it reaches the native
agent. Task packages therefore do not have to encode one harness's invocation
conventions.

That separation makes comparisons meaningful. I can hold a task fixed while
changing the model, investigation method or repository knowledge. I can retain an
answer while changing the judge. And a workflow that constructs an agent can
return a profile that another workflow executes, rather than a prose description
that someone must manually translate into a working agent.

## Three ways to construct executable work

I developed task-production workflows around three different sources of software
work. Their common output is a reconstructable assignment with explicit source,
scope, artifacts and assessment context. They differ in where the assignment is
defined: a parent delegates the next specialist problem, a transformation plan
partitions a repository change, or a review policy selects and reconstructs an
existing opportunity.

<figure class="specialist-figure specialist-wide" id="task-production-approaches" aria-labelledby="factory-caption">
  <div class="factory-headings" aria-hidden="true"><span>Work source</span><span></span><span>Define the assignment</span><span></span><span>Prepare the episode</span><span></span><span>Reusable work</span></div>
  <div class="factory-route"><div><strong>Source-grounded scenario</strong><span>Evolving workspace and specialist delegation</span></div><b aria-hidden="true">→</b><div><strong>Bounded specialist request</strong><span>Objective, edit surface and evidence contract</span></div><b aria-hidden="true">→</b><div><strong>Pre-call capture</strong><span>Current files and self-contained request</span></div><b aria-hidden="true">→</b><div class="factory-product"><strong>Captured assignment</strong></div></div>
  <div class="factory-route"><div><strong>Framework repository</strong><span>Algorithmic semantics and execution substrate</span></div><b aria-hidden="true">→</b><div><strong>Transformation blueprint</strong><span>File inventory and explicit ownership</span></div><b aria-hidden="true">→</b><div><strong>Mechanical materialization</strong><span>Validate partition, render instruction, package source</span></div><b aria-hidden="true">→</b><div class="factory-product"><strong>Migration task</strong></div></div>
  <div class="factory-route"><div><strong>Historical PR and review event</strong><span>Actual code change and engineering evidence</span></div><b aria-hidden="true">→</b><div><strong>Review opportunity</strong><span>Comparison, assignment scope and evidence policy</span></div><b aria-hidden="true">→</b><div><strong>Source compilation</strong><span>Pinned trees, diff and separate role views</span></div><b aria-hidden="true">→</b><div class="factory-product"><strong>Historical review task</strong></div></div>
  <figcaption id="factory-caption">Three approaches to producing executable work. Each preserves a starting problem and explicit outputs; the task can be replayed with a different worker. The rows describe distinct factory workflows, not a single combined dataset or execution backend.</figcaption>
</figure>

### Capture specialist assignments as the work evolves

In one workflow, a parent agent works through a source-grounded engineering
scenario and delegates bounded assignments to a specialist. The capture point is
immediately before the specialist runs: the current workspace and request define
the problem another actor should be able to attempt.

I built scenario materializers that separate the domain contract, starting files
and runtime configuration. The domain defines the work's vocabulary and evidence
requirements; the scenario defines a concrete starting state; the runtime layer
defines model access, resources and execution limits. Composing these layers
produces the parent task; its specialist calls then supply the captured child
tasks. Scenario authoring and child-task capture remain separate responsibilities.

The shared skeleton reused capture mechanics across source packs with different
proof obligations, such as generated-schema consistency and query-result
equivalence. Domain-specific evidence could change without redesigning the
capture and replay loop.

Each capture becomes replayable before the specialist has answered it. Original
solver traces and results remain separate from the promoted task's starting
files, while their lineage is retained for assessment and analysis.

The assignments must stand on observable files and a self-contained request.
“Continue from the previous response” is not a replayable problem. The request
instead names the objective, allowed edit surface, acceptance checks and expected
evidence. An audit can legitimately return a reproduction without a repair; an
implementation task has a different completion contract.

This supported evolving work on model rendering, data contracts, asynchronous
lifecycle, checkpoint and sampler state, and training-workflow integration.
A checkpoint assignment, for example, had to distinguish resumable trainer state
from the sampler used for generation: the two handles describe different
capabilities, not interchangeable model paths.

In the replay workflow, a worker attempts the captured problem in a separate workspace,
a judge assesses its artifacts, and the resulting changes and feedback return to
the parent. Subsequent assignments can build on the new file state without
depending on the previous worker's transcript.

My work covered the source-grounded scenarios, normalized materialization,
task contracts, corpus curation and replay integration, building on the team's
specialist-capture and actor/judge runtime foundations.

### Partition a repository transformation before materializing it

For ML-framework migration work, I used a different route: a technical translation
plan, a complete file-level action inventory, a partition into bounded worker
assignments, and mechanical task materialization.

For example, transforming an RL framework toward Tinker-backed computation is
not an import-renaming exercise. The plan must distinguish algorithmic semantics
worth preserving—advantage calculation, losses, response masking, experience
records and checkpoint intent—from the distributed execution substrate being
replaced. Ray actors, local inference engines and optimizer ownership do not map
to the new backend in the same way as a pure PPO loss function.

I made that distinction explicit in transformation plans for frameworks including
verl and OpenRLHF. A file inventory assigns each source path an action and an
owner. Structured worker specifications declare existing and new paths,
deletions, boundaries, validation and expected evidence. The materializer checks
that the assigned source paths cover the inventory without overlapping ownership.

Each task starts from the same pinned repository state and owns a coherent slice
of the transformation. The resulting assignments can be replayed and attempted
in parallel; integrating their patches is a separate operation. Shared package
surfaces have explicit ownership. Instructions are rendered from the structured
specification rather than repaired after the fact from arbitrary prompt text.

One SFT assignment illustrates the semantic boundary. It had to preserve response
loss masking, gradient accumulation, evaluation hooks, checkpoint cadence and
final-save behavior while replacing the training backend with Tinker clients.
The useful work was preserving the training contract, not merely getting the
new imports to resolve.

The semantic planning and partitioning are where domain judgment belongs. Once
those decisions are made, packaging the workspace, instruction, judge assets and
lineage should be deterministic.

### Compile historical review opportunities from source and evidence

For code review, the work already exists in repository history. I built a producer
that surveys submitted review events, applies explicit selection rules, captures
the associated records, resolves source revisions, and compiles runnable review
tasks and dataset manifests.

The compiler exports complete pinned source trees, the comparison base and the
actual diff. It can include companion repository snapshots where a contract
crosses a repository boundary. Actor context and private assessment evidence are
projected into separate views before packaging.

That distinction matters for historical work. A later fix or review discussion
may help assess an answer, but must not become the actor's answer key. The source
object database is not simply copied into the review environment, where future
commits could defeat that boundary. Evidence retains its source identity,
publication and observation information; unavailable historical versions are not
silently replaced with their current text.

Independent capture and compilation use bounded parallel workers.
Each case depends on its own opportunity and inputs, not the other cases selected
beside it. Immutable identities connect the visible work, private assessment
view, compiled package and uploaded task version. Changing the actor or judge
does not require recollecting the underlying problem.

## Hold the work fixed, change the evaluator

Separating the task, actor and judge creates useful experimental controls.
An actor can produce work without any automated score. Fresh attempts can be
paired with a task verifier or a selected judge profile. Retained outputs can
also be reassessed without asking the original actor to solve the work again.

For review tasks, I built a reusable judge profile containing its own rubric,
evidence-prompt preparation, structured judgment checks and deterministic reward
calculation. Each task supplies the case-specific private references in its
verifier environment. The model produces a structured judgment; the profile's
Stop hook validates it and computes the reward. The execution runtime launches
the recipe and collects the result; it does not need a hidden code-review-specific
grading policy.

This lets a judge serve a task family while its model, instructions or rubric
change independently of the actor. Repeated assessments of fixed outputs can
expose judge variability; comparing different judges does not require paying to
recreate the original work. The platform article explains the
[retained-output reassessment mechanism](/distributed-agent-training-and-evaluation/#actors-and-judges-can-run-independently).

For historical-reference tasks, this judge scores agreement with qualified
recorded evidence. Reviewer-quality comparison was a separate local workflow.
I developed it with coding agents around a per-opportunity evidence ledger,
preserving the original candidate and recorded Codex/CodeRabbit reviews and
linking judgments to pinned source and affected consumers. The same underlying
issue received one identity across different wording and output sections;
repeated descriptions did not multiply credit.

Diagnoses and proposed remedies were assessed separately. Known misses,
incomplete leads and alternative interpretations remained explicit. New source
evidence could revise an earlier judgment while preserving its history.
Deterministic tooling checked custody and whether every emitted item had an
assessment, then aggregated accepted judgments over paired opportunities.
Defect detection, misleading assertions and harmful advice stayed separate in
reporting. Source investigation determined whether a claim was true; historical
reviews were comparators, not exhaustive answer keys.

Separating the actor from assessment also matters outside experiments.
Deployment can use the task factory and chosen actor profile without attaching
a judge to every work item.
Evaluation and supported weight training remain separate choices.

## A creator that builds the reviewer

The next step was to make specialization itself repeatable. I built a construction
workflow that starts from repository URLs and authorized read access,
not a hand-written organization specification or a previous reviewer to repair.

The workflow collects two distinct sources of engineering knowledge. Git provides
code evolution and exact revisions. GitHub provides PR descriptions, reviews,
threaded discussion and decisions that the code alone may not explain. The
collector builds Git bundles and a searchable SQLite history, with recorded refs,
collection times, coverage and content identities.

Joining those sources takes more than cloning the default branch. A review may
refer to a force-pushed revision no longer reachable from current advertised
refs. I added an audit of authenticated review commit pointers against bundled
ancestry, followed by recovery and pinning of fetchable missing revisions. The
resulting history retains source that would otherwise disappear precisely where
a historical discussion needs it.

A factory turns that material into a creator task: restored Git mirrors,
searchable discussion history, the shared reviewer base, trusted assembly tools
and writable research space. The creator is an ordinary agent operating on that
task. Its output is another agent's repository-specific knowledge and runnable
profile.

The creator's job is semantic research. It discovers architecture, guarantees,
producer–consumer relationships, adopted decisions, intentional exceptions and
useful investigation procedures. It must distinguish adopted decisions from
discarded proposals and unresolved interpretations: a historical review comment
is not automatically a rule. The shared base owns the stable execution machinery:
model and engine settings, tools, review discipline, output format, validators
and launch behavior.

<figure class="specialist-figure specialist-wide" id="specialist-construction" aria-labelledby="construction-caption">
  <picture><source media="(max-width: 760px)" srcset="/assets/synth-specialists/construction-and-use-mobile.svg" width="420" height="1600"><img src="/assets/synth-specialists/construction-and-use.svg" width="1000" height="850" alt="Construction acquires repository history, prepares a creator task and runs a creator agent. Trusted assembly combines generated semantic knowledge with the shared executable base to produce a stored reviewer profile. A separate review factory prepares each PR task, which the chosen reviewer executes." loading="lazy"></picture>
  <figcaption id="construction-caption">The creator generates repository knowledge; trusted code preserves the executable contract. Construction produces a reusable profile, while each use reconstructs a separate review opportunity.</figcaption>
</figure>

Trusted code assembles those parts. The creator does not have to reinvent
launcher conventions, executable helpers or plugin metadata, and generated
knowledge cannot silently replace them. The assembler validates the structured
data, references and relationships and produces the runnable profile. At export,
the controller independently rebuilds it from the approved base, generated
knowledge and history manifest, and requires an exact match.

This division puts inference where it adds value—discovering and expressing
repository knowledge—and deterministic code where it can enforce a precise
contract. Structural validation and subsequent quality assessment are different
operations.

The separation also makes maintenance cheaper. An approved shared-base update
can be assembled with the exact existing specialization without repeating the
creator's research. The new profile records both inputs rather than silently
changing what an older profile identity means.

## Knowledge that an agent can navigate

Construction happens infrequently; review happens on every relevant change.
That asymmetry justifies deeper repository research during construction, but
only if the reviewer can use its results efficiently.

I organized specialization as a local knowledge library rather than flattening
it into one read-once prompt. The profile carries architecture, contracts,
repository-specific instructions, native skills, limitations, provenance and
navigation routes.

Each contract has more than a description. It records applicability, triggers,
producer and consumer paths, exceptions, investigation checks, counterevidence,
related skills and source references. A local lexical router supports orientation,
search and complete-record lookup. Behavioral terms, symbols and changed paths
return compact routes; the reviewer can then open the full relevant record.
Setup reconstructs these named files from a verified canonical representation:
transport compression does not summarize away their contents.

The creator also exercises the assembled library with path and behavioral
queries, checking which records are found and whether their full applicability
conditions, exceptions and related routes remain available. This makes retrieval
usability part of construction, not a formatting concern postponed until
deployment.

An actual generated OpenFGA contract concerned ordering-sensitive iterator
pruning. Two sorted inputs do not make their concatenation globally sorted; an
algorithm using ordering to prune candidates must receive the guarantee it
actually relies on. The generated record connected storage iterators and their
wrappers to the set-operation consumers using that guarantee. Its procedure
covered ordering flags, SQL ordering and collation, wrapper forwarding and pruning
guards. A related skill covered iterator lifetime and cleanup as well as ordering.

<figure class="specialist-figure knowledge-record" id="generated-knowledge-record" aria-labelledby="knowledge-caption">
  <div class="knowledge-record-heading"><span class="specialist-eyebrow">Inside an actual generated specialist</span><strong>Ordering-sensitive iterator pruning</strong></div>
  <dl><div><dt>Applies when</dt><dd>A changed iterator or wrapper supplies an ordering-dependent set operation.</dd></div><div><dt>Trace</dt><dd>Storage iterator → merge or concatenation wrapper → pruning consumer.</dd></div><div><dt>Check</dt><dd>Ordering flags, SQL order and collation, wrapper forwarding, cache replay and the consumer's guards.</dd></div><div><dt>Not sufficient</dt><dd>Sorted inputs alone do not establish globally sorted concatenation.</dd></div><div><dt>Related procedure</dt><dd>Inspect <code>Next</code>, <code>Head</code>, <code>Stop</code> and <code>IsOrdered</code>, including lifetime and cleanup.</dd></div><div><dt>Evidence</dt><dd>Pinned source references and the disposition of relevant engineering discussions.</dd></div></dl>
  <figcaption id="knowledge-caption">Abbreviated in original prose from the generated OpenFGA knowledge. A contract links an investigation trigger to producers, consumers, exceptions, procedures and evidence; it is not a precomputed finding for a later PR.</figcaption>
</figure>

That is more useful than “check iterator correctness.” It tells the reviewer
where a seemingly local wrapper change can break a downstream algorithm, and
which counterconditions could make the suspicion wrong. Construction-time
knowledge guides the investigation; the current task's source still decides
whether the defect exists.

## Turning context into investigation

A review factory resolves the requested PR snapshot and prepares the source the
agent will actually investigate. The reviewer gets complete files or enclosing
source scopes, numbered locations and continuation routes for long contexts,
alongside the diff and relevant repository knowledge.

The shared base separates two jobs: discover plausible problems broadly, and
investigate each candidate deeply enough to support a useful claim. Parallel
workers inspect complementary source paths; source-first discovery can proceed
without inheriting the parent's leading allegation. The parent must reconcile
the actual producer, controlling guards and consumer behavior, rather than count
how many agents agree.

I also built a whole-draft challenge stage. A trusted helper snapshots the actual
structured review, including its proposed remedies, alternatives, reassurances
and coverage claims, and resolves its references to exact source. A fresh
challenger receives that packet rather than a favorable summary written by the
author of the finding. Its response and the draft it inspected remain linked.
This is an actor-side investigation step, separate from a judge selected to
assess the completed review.

The output distinguishes defects, resolved concerns, trade-offs, specific open
questions and coverage. These categories have no quotas. A useful review can
explain why a suspicious path is safe or which condition changes a trade-off,
without disguising either as a bug. Findings and proposed fixes are separate:
a correct diagnosis does not automatically make every suggested remedy safe.

The parent and its delegates share an execution deadline and budget. An early
valid output protects the work, while remaining time goes into further source
investigation and refinement. The purpose of parallelism is more useful evidence
within the review window, not more agents or a longer final report.

### Improve the responsible component

I developed these profiles by examining completed reviews, their source evidence
and their execution traces. A missed candidate and an incorrectly classified
candidate call for different interventions: one is a discovery problem, the
other a verification problem.

The component boundary determines where a reusable improvement belongs. Missing
or misleading source presentation belongs in the task factory. Missing repository
knowledge belongs in construction and retrieval. Weak investigation or evidence
integration belongs in the shared reviewer behavior. An unreliable assessment
belongs in the assessment method, rather than being treated as an actor defect.

This kept development focused on transferable changes to the creator, base and
supporting machinery. Reserved comparison work tested a frozen composition rather
than becoming another repository-specific repair instruction. The external
application below exercises that distinction: the same reusable construction
method builds a new specialist from the other organization's own sources.

## Construction and use as cloud workflows

I exposed two cloud development workflows through GitHub Actions: build a
reviewer and review a PR. Construction
collects the repository inputs, prepares a creator task, runs the creator,
validates and assembles its output, and stores a content-addressed reviewer
bundle. Use downloads a selected profile, resolves a PR's source and context,
constructs a review task and returns the review and artifacts.

The October workflows run complete profiles through standalone Harbor and native
Claude Code, with direct Anthropic inference and disposable Daytona environments.
They preserve the profile's setup, files, skills, tools, hooks and output
semantics. This is the same agent-profile format used by the platform, with a
different inference and orchestration route for this application.

Source acquisition stays on the control side, using repository-scoped read
authority. Execution credentials are injected separately rather than embedded in
the profile or generated knowledge. Repository content and discussion are research
inputs, not trusted configuration. Tools and launch settings come from the shared
base; assembly and export checks prevent generated knowledge from replacing that
executable contract.

The workflows retain exact profile and source identities, outputs, traces, model
usage, reported inference cost and timing. Profiles have durable private storage separate from
temporary diagnostic artifacts. An authorized operator can return to the result
without essential profile files or a controller left running on my laptop.

Follow-up review adds another kind of state. The implementation carries prior
findings alongside the old and new source, with stable finding origins and
versioned events for persistence, change, resolution and recurrence. Uncertain
identity remains explicit rather than merging allegations by guesswork. The full
current review stays intact; a separate private-history delta highlights new,
changed and resurfacing findings.

I also implemented on-demand PR invocation with operator, repository and profile
authorization and source pins established at admission. Request identity and
finding identity solve different problems: request deduplication prevents duplicate
execution, while finding identity tracks the same issue across source changes.
Source and authorization are checked again before publication, which anchors the
review to the admitted commit. These integration paths were exercised through
cloud workflows and PR publication.

These are implemented and exercised development workflows, not a generally
available service. Their interfaces make construction and use remotely operable
while keeping repository, operator and execution authority explicit.

## Following a contract across components

I used the reusable construction method beyond SynthLabs to build an
OpenFGA-specific reviewer from programmatically acquired source and engineering
history preceding the comparison period. The generated profile then reviewed
later historical changes without an
OpenFGA-specific repair packet or changes to the shared creator and reviewer base.

[OpenFGA](https://openfga.dev/docs/concepts) is an authorization service; its
stores group authorization models and relationship data.
One consequential example came from a historical snapshot of
[OpenFGA's MySQL read-replica work](https://github.com/openfga/openfga/pull/3290).
The change routed a store lookup to a replica. The important consequence appeared
in a consumer of that lookup: the command that deletes a store.

A store could be committed on the primary before replication made it visible to
the secondary. The delete command first performed the replica-backed lookup.
“Not found” was treated as successful idempotent deletion, so the command could
return success without issuing the actual delete against the primary. Once the
replica caught up, the supposedly deleted store remained visible.

<figure class="specialist-figure specialist-wide" id="replica-delete-contract" aria-labelledby="replica-caption">
  <picture><source media="(max-width: 760px)" srcset="/assets/synth-specialists/replica-delete-contract-mobile.svg" width="420" height="1030"><img src="/assets/synth-specialists/replica-delete-contract.svg" width="1000" height="640" alt="In the historical snapshot, a store exists on the primary but is not yet visible on the replica. DeleteStoreCommand uses the replica lookup's not-found result to return success before calling the primary delete, leaving the store present." loading="lazy"></picture>
  <figcaption id="replica-caption">The verified path in the evaluated historical snapshot. The defect crosses storage routing and command behavior: an acceptable stale read becomes an invalid reason to skip a mutation.</figcaption>
</figure>

<details class="historical-source-note"><summary>Source for the evaluated historical path</summary><p>The linked PR subsequently changed. The evaluated snapshot's <a href="https://api.github.com/repos/openfga/openfga/git/blobs/6c9ac4f0b069b50894345acc2569ce2eb18352b0">MySQL source blob</a> contains the primary creation, replica-backed lookup and primary deletion. Its <a href="https://api.github.com/repos/openfga/openfga/git/blobs/9fbf8940e3bb1191aab7a17bbbc65378d83d7e18">delete-command source blob</a> contains the early return. These links return immutable Git Data records as JSON with base64-encoded source. They identify the files used for the analysis rather than substituting today's implementation.</p></details>

The issue was not merely that a replica can return stale data. A stale read was
being used as authority to skip a mutation, violating the operation's intended
postcondition. Establishing that required tracing creation, consistency routing,
the lookup's error translation, the command's early return and the primary-bound
delete. The generated reviewer identified this path; source-backed assessment
confirmed it, and it was absent from the recorded baseline review.

In the historical comparison, the constructed reviewer found more
source-confirmed actionable and consequential defects than the recorded
CodeRabbit reviews. The assessments were internal and performed with coding
agents, checking pinned source and affected consumers. They compared complete
reviewers; they did not isolate the contribution of generated knowledge from the
model, shared harness or source preparation. The example describes the evaluated
historical snapshot, not a claim about a current OpenFGA vulnerability.

The value of the system is broader than the individual finding: a repeatable
construction method produced a repository-specific agent, and a separate task
factory let that same agent investigate real changes under controlled source
conditions.

## How this connects to learning

Tasks, profiles and assessment create independent improvement levers. Better
source preparation changes what the actor can inspect. A better creator changes
the reusable knowledge it receives. A better base changes how it investigates.
A better judge changes how outcomes are assessed. Weight training changes the
model itself.

The reviewer construction described here specializes knowledge and harness
behavior without updating model weights. The
[distributed platform](/distributed-agent-training-and-evaluation/) supplies the
separate execution, evaluation and supported weight-training primitives: assessed
task experience can produce a model checkpoint that returns to the same harness.

My contribution was connecting these layers into reusable engineering workflows:
task production, independently configurable actors and judges, repository research,
knowledge assembly, agent investigation and remote operation. I built this with
the SynthLabs team and extensive use of coding agents, using Harbor, native coding
harnesses, model providers and sandbox infrastructure as foundations.

The resulting capability is to turn existing software work and engineering
knowledge into executable tasks and reusable specialists—and to improve the work,
the worker and the assessment without rebuilding the entire system each time.

## Further reading

- [The distributed execution and learning platform](/distributed-agent-training-and-evaluation/)
- [Task packages and versioning](https://synthlabs.mintlify.app/concepts/tasks-and-versions)
- [Executable agent profiles](https://synthlabs.mintlify.app/concepts/profiles-and-candidates)
- [Public CLI command reference](https://synthlabs.mintlify.app/reference/cli)

<style>
  .specialist-contents { font-size: 12px; line-height: 2; margin: 30px 0 44px; }
  .specialist-contents a { display: inline-block; padding: 3px 0; }
  .workflow-interface { border-top: 1px solid var(--fg); border-bottom: 1px solid var(--rule); padding: 16px 0 4px; margin: 32px 0 44px; }
  .workflow-interface p { display: grid; grid-template-columns: 90px 1fr; gap: 16px; font-size: 13px; margin-bottom: 12px; }
  .workflow-interface strong { text-transform: uppercase; letter-spacing: .04em; }
  .specialist-figure { margin: 38px 0 44px; }
  .specialist-figure figcaption { max-width: 660px; margin: 14px auto 0; }
  .specialist-wide { width: min(1000px, calc(100vw - 56px)); position: relative; left: 50%; transform: translateX(-50%); }
  .specialist-figure picture, .specialist-figure img { display: block; width: 100%; }
  .specialist-figure img { height: auto; border: 1px solid var(--rule); background: #fff; }
  .factory-headings, .factory-route { display: grid; grid-template-columns: 1fr 20px 1.2fr 20px 1.2fr 20px .85fr; gap: 10px; align-items: center; }
  .factory-headings { font-size: 12px; text-transform: uppercase; letter-spacing: .05em; padding: 0 12px 12px; }
  .factory-route { padding: 18px 12px; border-top: 1px solid var(--rule); font-size: 13px; line-height: 1.7; }
  .factory-route:last-of-type { border-bottom: 1px solid var(--rule); }
  .factory-route > div { min-width: 0; align-self: stretch; padding: 12px; border: 1px solid var(--rule); }
  .factory-route strong, .factory-route span { display: block; }
  .factory-route span { color: var(--dim); margin-top: 9px; font-size: 12px; }
  .factory-route > b { font-size: 19px; text-align: center; font-weight: 400; }
  .factory-route .factory-product { border-color: var(--fg); display: flex; align-items: center; }
  .specialist-eyebrow { display: block; font-size: 11px; text-transform: uppercase; letter-spacing: .05em; color: var(--dim); margin-bottom: 8px; }
  .knowledge-record-heading { border-top: 1px solid var(--fg); border-bottom: 1px solid var(--rule); padding: 18px 0; }
  .knowledge-record dl { margin: 0; font-size: 13px; }
  .knowledge-record dl > div { display: grid; grid-template-columns: 145px 1fr; gap: 18px; padding: 14px 0; border-bottom: 1px solid var(--rule); }
  .knowledge-record dt { font-weight: 700; }
  .knowledge-record dd { margin: 0; }
  .historical-source-note { font-size: 12px; line-height: 1.8; border-top: 1px solid var(--rule); border-bottom: 1px solid var(--rule); padding: 12px 0; margin: -18px 0 32px; }
  .historical-source-note summary { cursor: pointer; }
  .historical-source-note p { margin: 14px 0 4px; }
  @media (max-width: 760px) {
    .specialist-wide { width: 100%; position: static; transform: none; }
    .factory-headings { display: none; }
    .factory-route { grid-template-columns: 1fr; padding: 18px 0; gap: 6px; }
    .factory-route > b { transform: rotate(90deg); line-height: 1; }
    .factory-route > div { padding: 12px 14px; }
    .factory-route span { font-size: 12px; margin-top: 4px; }
    .factory-route strong { font-size: 13px; }
  }
  @media (max-width: 620px) {
    .workflow-interface p { grid-template-columns: 1fr; gap: 5px; }
    .knowledge-record dl > div { grid-template-columns: 1fr; gap: 5px; }
    .knowledge-record-heading strong { font-size: 13px; }
  }
</style>

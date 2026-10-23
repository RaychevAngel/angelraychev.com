---
title: "Model specialization and training agents"
description: "Knowledge distillation, synthetic-data factories, tool-using model training, and agents that inspect and improve the training workflow itself."
image: "/assets/model-specialization/article-cover.png"
imageAlt: "Three nested levels: a researcher improves a training agent, which constructs data and trains a specialist model."
updated: 2026-10-23
---

At SynthLabs, I implemented document-adaptation, supervised fine-tuning and
on-policy distillation pipelines for open-weight models. I then built agents to
prepare, run and investigate that work. A training agent turned a specialization
request into a model specification, data, assessments and checkpoints. An outer
researcher agent inspected those episodes and revised the training agent's
reusable skills and tools. I connected generated tasks to teacher demonstrations,
student training and checkpoint assessment, and implemented on-policy updates
from a student's own tool-using trajectories.

<figure class="specialization-figure" aria-labelledby="levels-caption">
  <div class="research-loop">
    <div class="loop-heading"><span class="diagram-label">Outer researcher</span><strong>Improve the training agent's reusable process</strong><span>Inspect episodes, diagnose the responsible component, revise skills or tools, compare the next attempt.</span></div>
    <div class="training-loop"><div class="loop-heading"><span class="diagram-label">Training agent</span><strong>Carry out a specialization assignment</strong><span>Understand the goal, construct data and assessment, run training, inspect the result.</span></div><div class="weight-loop"><div><span class="diagram-label">Training inputs</span><strong>Data + model + objective</strong></div><span class="diagram-arrow" aria-hidden="true">→</span><div><span class="diagram-label">Weight updates</span><strong>Specialist checkpoint</strong></div></div></div>
    <div class="loop-return">Episode traces, data checks and checkpoint comparisons inform the outer researcher.</div>
  </div>
  <figcaption id="levels-caption">Three objects of work. Training changes a specialist's weights. The training agent conducts that work. The researcher changes the training agent's harness and procedure. Improving the outer process does not require training the researcher's own weights.</figcaption>
</figure>

The underlying question was practical: **what should a model learn, and what
should its surrounding system supply?** A company-specific assistant might need
to recall a stable convention, retrieve a changing specification, call a tool,
write code, or follow a particular workflow. Those are different capabilities.
Providing the same pile of documents to every component does not define how to
train or evaluate any of them.

This article describes that January–May 2026 work, followed by a related
May–June team application. It precedes my
[distributed training and evaluation platform](/distributed-agent-training-and-evaluation/)
and complements the later
[repository-specific agent construction workflows](/from-software-work-to-specialized-agents/).
The connection is deliberate: model weights, executable environments and
reusable agent behavior have to fit together, but they remain independently
adjustable parts of the system.

<nav class="specialization-contents" aria-label="In this article"><a href="#choosing-what-to-specialize">The specialization target</a> · <a href="#compiling-document-knowledge-into-weights">Knowledge experiments</a> · <a href="#a-teacher-with-information-the-student-does-not-have">Context distillation</a> · <a href="#making-training-an-agent-task">The training agent</a> · <a href="#a-researcher-for-the-training-workflow">The outer researcher</a> · <a href="#building-the-training-distribution">Data factories</a> · <a href="#distilling-tool-using-policies">Tool-using policies</a></nav>

## Choosing what to specialize

An assistant can become more useful without changing its weights. Better
instructions can direct its investigation. Searchable resources can expose
organization knowledge. Tools can give it the operations that the work requires.
Training can then change how the model uses those affordances, or internalize
information that would otherwise have to be supplied repeatedly.

I treated these as separate optimization choices rather than different names
for fine-tuning.

<div class="tablewrap">

| What changes | What it can accomplish | What has to match |
| --- | --- | --- |
| Model weights | Learn domain behavior, answer patterns and tool-use policies; internalize recurring knowledge | Training examples, update objective and intended inference behavior |
| Instructions and workflow | Change how an agent investigates, plans, delegates, checks and submits work | The actual tools and execution environment |
| Resources and retrieval | Make source information, procedures and examples available when needed | Organization, navigation and the ability to find relevant evidence |
| Tools and environment | Expose the actions needed to complete the job | Input/output contracts, permissions and observable results |

</div>

For example, training a closed-book model to answer questions about company
documentation tests what it can answer unaided after weight updates. Training an agent
to locate the right document tests a different behavior. Giving the model the
answer-bearing document at evaluation time changes the question again.

The target also extends beyond factual question answering. A specialist might
have to produce a script, make a recommendation under company policy, transform
structured data, or perform a sequence of actions. Each calls for representative
work and an assessment appropriate to that output. A question-answer benchmark
cannot stand in for all of them.

That distinction shaped both the early experiments and the later training-agent
design: define the behavior and deployment conditions before choosing the
training procedure.

## Compiling document knowledge into weights

PostHog's public handbook supplied organization-specific engineering and
operating guidance for a concrete specialization testbed. Nathan built
document-to-data generation machinery; I developed and exercised the training
and evaluation pipelines around these sources.

One actual training example asked when an engineer would choose Celery rather
than Temporal or Dagster. The supporting
[engineering-stack section](https://github.com/PostHog/posthog.com/blob/0128752787534696b414242c9c39a3801f0b7a82/contents/handbook/engineering/stack.md)
described PostHog's adopted division of work: tiny, low-latency, fire-and-forget
jobs for Celery, reliable complex workflows for Temporal, and scheduled data
transformations for Dagster. The target was the organization's particular
engineering guidance, rather than a generic comparison of the three systems.

The central experiment was intentionally demanding: **could a model answer
domain questions without receiving the supporting document at inference time?**
That separated knowledge in weights from the immediate benefit of supplying
context.

I built a shared data representation containing a question, supporting context
and a reference answer. Different training procedures consumed different views
of the same information. Storing them in one record did not expose the context
to the question-only student.

The implemented routes included:

- Documentation adaptation: train on packed source documents with their file and
  section information.
- Synthetic question-answer SFT and answer distillation: generate supervision
  from source material, including answers from a context-grounded teacher, then
  train on question-answer pairs. General instruction-following examples could
  be mixed into that supervision.
- On-policy context distillation: let the student generate an answer, then use a
  context-privileged teacher to score those generated tokens.
- Context annealing: progressively reduce the source context available to the
  student during training.

These alternatives ask different things of the optimization process. Training on
documents exposes content directly. Question-answer supervision rehearses ways
that content is used. A contextual teacher can supply a stronger answer than a
closed-book model. On-policy distillation directs supervision toward what the
student currently produces, rather than only answers produced by another model.

I compared data volumes, teacher-generated supervision, initial training states
and distillation settings. Evaluation tracked domain performance separately from
general instruction following. That second measurement matters: acquiring
specialized knowledge is less useful if the resulting model stops reliably
following the instructions through which that knowledge is requested.

<figure class="specialization-figure specialization-wide" aria-labelledby="data-scale-caption">
  <div class="empirical-scroll" tabindex="0" role="region" aria-label="Data-volume experiment figure; scroll horizontally on small screens"><img src="/assets/model-specialization/specialization-data-scale.svg" width="1919" height="1102" alt="Five mean source-grounded QA score curves for 2,500 through 39,500 synthetic training pairs, plotted against training-set equivalents processed. Larger training sets reach higher recorded scores." loading="lazy" /></div>
  <figcaption id="data-scale-caption">Rank-32 LoRA SFT of Qwen3-4B-Instruct-2507 on differently sized sets of context-generated QA. The student answers without source context; a context-grounded Qwen3-30B-A3B judge provides a mean answer score from 0 to 4. The curves share the recorded starting-model baseline. Training-set equivalents are 64 × recorded optimizer step / training-set size, not exact completed epochs. Larger sets require more updates for the same exposure. This is a supervision-budget comparison, not a controlled scaling-law estimate. <a href="/assets/model-specialization/specialization-data-scale.svg">Open full figure</a>.</figcaption>
</figure>

The larger supervision sets reached higher recorded scores. Within each fixed
set, the recorded scores changed less with further training. More distinct examples also meant
more updates for each training-set equivalent, so this comparison does not isolate data quantity from
compute. It nevertheless exposed a useful decision: whether to spend the next
training budget repeating the existing supervision or expanding its coverage.

<figure class="specialization-figure specialization-wide" aria-labelledby="instruction-mix-caption">
  <div class="empirical-scroll" tabindex="0" role="region" aria-label="Domain and instruction-following experiment figure; scroll horizontally on small screens"><img src="/assets/model-specialization/specialization-instruction-mix.svg" width="1967" height="1563" alt="Two panels compare domain-only SFT with mixed domain and instruction training. Both learn domain QA; the mixed run retains higher recorded strict IFEval accuracy at shared checkpoints, while domain-only QA scores are usually higher." loading="lazy" /></div>
  <figcaption id="instruction-mix-caption">Domain-only SFT versus a roughly 70/30 mixture of domain QA and general instruction examples generated from Tulu 3 prompts. Mean QA score and IFEval prompt-level strict accuracy measure different capabilities. The horizontal axis counts optimizer updates; training tokens, domain exposure and learning-rate schedules are not matched. <a href="/assets/model-specialization/specialization-instruction-mix.svg">Open full figure</a>.</figcaption>
</figure>

The mixture retained higher recorded instruction-following accuracy at the
shared measured checkpoints. Domain-only training usually scored higher on the
domain questions. Tracking both made that trade-off visible instead of hiding
it behind a single specialization score.

These are reconstructed exploratory historical measurements, with one training
run per condition. The preparation protocol split by question rather than source
document: the target was answering about the supplied corpus, not transfer to
unseen documents. The QA score comes from a source-grounded model judge, not
independently verified task success, and the historical dataset revision was not
pinned.

The broader experiments included SFT data-volume sweeps, teacher comparisons,
documentation-adaptation comparisons, distillation from an instruction-tuned
starting model, SFT-warm distillation, and subsequent instruction-following
training. The value was an experimental framework in which these choices could
be changed and measured, rather than a fixed one-off training script.

## A teacher with information the student does not have

The SFT sweeps varied the supervision supplied to the learner. The on-policy
route changed where that supervision came from: the learner's own current
responses became the trajectories on which the teacher supplied feedback.

Context distillation makes the information boundary explicit. The teacher sees
a question and its supporting context. The student sees the question alone.
The objective is to transfer some of the teacher's context-conditioned behavior
into the student's parameters.

In the on-policy route I implemented, the student first samples a response.
The teacher scores that same response under its richer input. For a sampled
response token, the training signal uses the difference between its
teacher-conditioned and student-conditioned log probabilities. Tokens are
selected by the student; the teacher evaluates those tokens with additional
information.

For question $q$, context $c$ and response prefix $a_{<t}$, the sampled
token-level signal has the form

$$
\delta_t = \log \pi_T(a_t \mid q,c,a_{<t})
           - \log \pi_{\mathrm{rollout}}(a_t \mid q,a_{<t}).
$$

This is a sampled reverse-KL-style distillation signal. It is not a comparison
of two independently written answers, and it does not require the teacher to
generate a replacement response for every student attempt.
The signal is positive when the contextual teacher gives a sampled token more
probability than the rollout policy did, and negative in the opposite case.

<figure class="specialization-figure" aria-labelledby="distillation-caption">
  <div class="distillation-diagram"><div class="shared-question"><span class="diagram-label">Shared input</span><strong>Domain question</strong></div><div class="distillation-pair"><div><span class="diagram-label">Student</span><strong>Question only</strong><p>Samples a response and records the generated tokens and sampling log probabilities.</p></div><div><span class="diagram-label">Teacher</span><strong>Question + supporting document</strong><p>Scores the student's same response tokens with access to the source information.</p></div></div><div class="distillation-update"><strong>Teacher token log-probability − recorded student token log-probability</strong><span>Response-token signal → parameter update → refreshed student sampler</span></div></div>
  <figcaption id="distillation-caption">The teacher's extra information is the document context. The student supplies the trajectory. Recorded rollout log probabilities are fixed inputs to the update; the learner is updated through the training loss, not by differentiating through this displayed subtraction.</figcaption>
</figure>

The implementation had to preserve the teacher's extra context, align response
tokens and masks, obtain the relevant log probabilities, and turn the resulting
signal into Tinker training updates. The updated model's sampler then supplied
the next student responses. Model identity and checkpoint identity were part of
the experiment, rather than inferred from a run's display name.

The log-probability difference was supplied as a detached per-token advantage
to the learner, alongside the captured sampling log probabilities and response
masks. Tinker's [importance-sampling training loss](https://tinker-docs.thinkingmachines.ai/tinker/losses/importance-sampling/)
then applied the student update.
Keeping those roles separate matters: the teacher score supplies supervision;
the loss determines how that supervision changes the student's weights.

There are two important operational distinctions here. First, the teacher's
information advantage is separate from model size: the same model family can be
used on both sides with different visible context. Second, answer distillation
and token-level distillation impose different compatibility requirements.
Text answers can be retokenized for a different student. Directly comparing
teacher and student token likelihoods requires an explicit alignment contract;
passing one model's token IDs to an incompatible tokenizer is not that contract.

Teacher privilege also has a behavioral boundary. The teacher can consult extra
evidence to improve its supervision, but the behavior the student is trained to
imitate must still fit its deployed job. An answer that tells the student to
inspect a hidden solution file or call an unavailable tool teaches a different
contract. This is not a ban on the teacher's extra information—that advantage is
the point. I incorporated the distinction into the later training agent's
data-generation and method-selection skills, for both teacher-generated SFT
answers and on-policy distillation.

I also explored the starting distribution. An SFT warm start can make relevant
answers more accessible before on-policy training, while later
instruction-following distillation can address another capability. The order of
these stages is a substantive experimental choice, not interchangeable launch
syntax.

## Making training an agent task

The next problem was repeatability. Running a known recipe is useful, but many
specialization requests arrive before the dataset, evaluation and deployment
behavior have been specified.

I built Claude Code-based training agents that could work through that preparation
as well as execute the training. These agents operated the training workflow;
the specialist model checkpoint was their output. An episode began with a goal and available resources,
not a completed configuration file. The agent inspected the material, clarified
what the resulting model was supposed to do, proposed a plan, prepared data,
ran checks, launched training and exposed the resulting checkpoints and
evaluation artifacts.

One March assignment asked for a PostHog technical assistant trained from
Qwen3.5-4B and the public product documentation. The request named example jobs
such as configuration, feature-flag behavior and HogQL queries, but did not
provide the finished training recipe. The agent had to turn that request into
a concrete preparation and training plan. This was a broader product-support
task than the earlier handbook-knowledge experiments.

The workflow separated decisions that are easy to conflate:

1. **The intended model behavior.** What inputs will it receive? Which tools and
   resources will it have? What counts as a useful response or completed action?
2. **The training distribution.** Where do examples come from, what do they cover,
   and how is their correctness established?
3. **The training procedure.** Which supported method, model, data rendering and
   update settings fit that behavior?
4. **The assessment.** How will the resulting model be compared and inspected
   without treating successful job completion as sufficient evidence of quality?

I introduced a model specification that represented the intended behavior
alongside its instructions, tool definitions and resources. Creation and
validation tools checked the referenced artifacts. A renderer could translate
the specification into a harness configuration for synthetic-data generation.
That gave the training agent a concrete object to build and inspect, rather than
leaving the desired model as an informal paragraph.

The agent's own tools mattered just as much. They needed to expose real training
parameters, distinguish failed launches from completed jobs, provide logs and
status, and return usable checkpoint and sampler handles. A tool accepting a
parameter internally was insufficient if the CLI through which the agent acted
never forwarded it. I worked on those interfaces together with the skills that
taught the agent how to use them.

Onboarding had a persistent handoff: a versioned JSON plan for downstream stages
and a readable view for approval. It recorded deployment tools, expected queries,
data sources, the training procedure and assessment criteria. The profile called
for a small generation probe before bulk work, with a fresh-context reviewer
checking relevance and coverage against the intended query distribution, then
the user's approval of that direction. These were agent workflow instructions,
distinct from the structural validation performed by code.

The orchestration agent retained the goal and decisions while data-intensive
preparation, independent quality checks, training and evaluation could be
delegated to specialist agents. A trained model came with inspectable artifacts,
so the next decision did not depend on trusting a summary that training had
succeeded.

There were two distinct assessments. Task verification checked whether the
training workflow had fulfilled its execution and artifact contract. Checkpoint
evaluation examined the resulting model's behavior. Completing the first did
not answer the second.

These components were integrated through
[Claude Code plugins](https://code.claude.com/docs/en/plugins), training tools,
[Harbor tasks](https://docs.harborframework.com/tasks/overview) and sandbox
execution. I added plugin-directory support to our Harbor adapter so the same
training-agent configuration could be exercised as an
executable task rather than only in a developer's interactive session.

## A researcher for the training workflow

A training agent can complete an episode while still preparing weak data,
using a poor experiment, or spending its effort in the wrong place. That makes
the agent's reusable process another object worth improving.

I built an outer researcher around the training agent. The training agent
attempted the specialization task and produced data, model checkpoints and
artifacts. The researcher inspected what happened and could revise the
training agent's plugin: instructions, skills, tools, data preparation or
experiment procedure. It then launched further episodes and assessed their
outputs.

The researcher had operations for launching and managing sandboxes, inspecting
status and logs, retrieving artifacts, sending follow-up messages, and reloading
or restarting the inner agent when appropriate. A trace parser exposed relevant
segments instead of forcing every investigator to read an entire conversation.
Persistent journals retained observations, hypotheses, changes and comparisons
across sessions.

For research episodes, the launcher supplied a focus task and assigned the
outer agent the run–inspect–revise–restart loop, including the operator role at
the inner agent's routine approval turns.

The distinction between the two loops is important. The inner episode optimizes
or constructs a specialist model. The outer loop changes how that episode is
conducted. Its useful mutations can be source-selection rules, better checks,
correct tool interfaces or revised instructions, rather than another learning
rate.

### Turning a run's discovery into a reusable skill

One concrete example came from generating training data from documentation.
Some MDX files contained imports and component wrappers rather than the facts
their filenames suggested. A character-count filter could accept them as
substantial documents, leaving the generator without the underlying information.

The training agent diagnosed that distinction during an episode, changed its
content check and regenerated the data. The resulting data passed a subsequent
quality check, and a trained checkpoint was evaluated repeatedly. The researcher
then incorporated the lesson into the shared data-generation skill, including
checks for wrapper-only files and references to externally loaded content.

Other investigations concerned consistency between training and inference
instructions, the relationship between dataset size and the actual number of
optimizer steps, and parameters that did not survive the path from the agent's
CLI to its training backend. These examples demonstrate why optimizing a
training agent involves its entire working environment.

The researcher was implemented and exercised, with retained source changes,
experiment journals, checkpoint identities and repeated model comparisons.
Those comparisons guided development; repeatedly used evaluation prompts did
not provide independent confirmation of improvement. The record makes the
research process inspectable, including
which reusable component changed and which model was subsequently assessed.

### Shorter loops for data-generation research

Not every question needed a complete training-agent episode. In April I also
separated task-specification extraction, instance generation and diagnostic
comparison into a smaller artifact-based workflow. These task specifications
defined the learning work; the earlier model specification defined the
specialist, and the plan its construction. One agent derived a task
specification from source material and a standalone guide. Another
was assigned the specification and a general generation recipe. A separate agent
inspected a shuffled, unlabeled mixture of generated and comparison examples,
returning classifications and reasons. The comparison labels were stored in a
separate file.

The reusable components were independently editable: the specification guide,
extraction instructions, generation recipe and comparison preparation. The
recipe gained explicit output-style checks and representation normalization;
the retained handoffs and generated artifacts made it possible to inspect what
each stage had actually received and produced. This gave me a shorter route to
investigating data-generation behavior before paying for a downstream training
comparison.

The discriminator was a diagnostic, not a task-correctness oracle. Matching
presentation or making two sets harder to distinguish does not by itself show
that the generated work is correct or that training on it improves a model.

## Building the training distribution

Beyond operating a training recipe, I worked on constructing the learning
distribution: representative tasks and feedback suited to the target capability.
A desired capability is not a training set, and a benchmark's examples are not
a recipe for producing more of the right work. Alongside the training-agent
and researcher stack, I built a separate task/data pipeline connecting
task specification, independent source material, generation, executable
verification and policy training. The factory—not just the training run—was an
object of research and engineering.

I used [MMTU](https://arxiv.org/abs/2506.05587), a table-understanding and
reasoning benchmark, as a concrete testbed. Its task families include question
answering, SQL generation, table transformation, schema matching and relationship
detection. They do not all share the same inputs, answer format or definition of
correctness. That made it a useful setting for building beyond synthetic Q&A.

### Specifications and generation are different objects

A task specification recorded the action, visible input, output contract,
source material, selection rules, ground-truth derivation and scoring. Source
allocation specified which task families each source would supply and what
variation in column subsets, row counts and operations to cover. The procedure
that turned those decisions into instances
was independently adjustable: improve the generator without silently changing
the task, or change the distribution without rewriting execution machinery.

The factory assembled a working directory for each task-family/source generation
job. Each job could produce multiple learning instances. It rendered
instructions from task-specific contracts and shared templates,
connected the source files, and attached validation. This helped both coverage
and parallel execution. A long generation session can converge on repetitive
examples; many isolated calls can return the same obvious example. Each unit
of work therefore carried an explicit allocation instead of asking every worker
to invent its own interpretation of “diverse.”

I separated the controller from bulk generation. The controller could use a full
coding-agent environment to research sources and revise the procedure. Repeated
generation used an API model with a lightweight file-and-tool harness. It could
inspect a CSV's schema, sample relevant rows, use Python for computation, and
write output to disk. It did not have to load every source row into its
conversation or regenerate a long response to repair a small file error.

An asynchronous sampler ran these jobs concurrently, retained tool trajectories
alongside token and estimated-cost records, and returned validation errors to the same working
conversation. The generator could correct its existing artifacts while keeping
the context of how they had been produced. Resume logic checked saved output
before deciding to skip a job.

### Follow one generated SQL task through the factory

One generated SQL task combined three named tables: `patients`, `medical` and
`billing`, linked by `PatientID`. Its reference joined those tables, filtered a
medical condition and selected the corresponding name, doctor and billing
fields in name order:

<pre class="sql-specimen" tabindex="0" role="region" aria-label="Generated three-table reference SQL; scroll horizontally on small screens"><code>SELECT p."Name", m."Doctor", b."Billing Amount"
FROM "patients" p
JOIN "medical" m ON p."PatientID" = m."PatientID"
JOIN "billing" b ON p."PatientID" = b."PatientID"
WHERE m."Medical Condition" = 'Asthma'
ORDER BY p."Name";</code></pre>

The packaged task contained a SQLite database with those same named tables and
an expected-result CSV with matching output columns. The assembly code cleaned
the reference SQL, executed it, and stored the database and reference output in
the task's verification information. During assessment, the verifier executes
the candidate's SQL and compares returned values. Correctness is not defined
as reproducing one reference SQL string:
different queries could express the same solution.

<figure class="specialization-figure" aria-labelledby="factory-caption"><ol class="factory-chain"><li><span class="diagram-label">Define</span><strong>SQL task contract + source allocation</strong><span>Visible schema, question, query coverage and output requirements</span></li><li><span class="diagram-label">Generate</span><strong>Question and reference query</strong><span>Inspect source data, write instances, receive validation feedback</span></li><li><span class="diagram-label">Materialize</span><strong>Database and expected result</strong><span>Execute the reference and package task-specific checking information</span></li><li><span class="diagram-label">Use</span><strong>Policy tools and executable assessment</strong><span>Sample demonstrations or policy actions; execute and compare results</span></li></ol><figcaption id="factory-caption">A concrete learning artifact passes through several different components. The generator prepares the work; assembly constructs checking material; the policy attempts the task with its own tool harness; the verifier computes feedback from the output.</figcaption></figure>

Other task families required different assembly: normalizing labels, carrying
reference files for Python transformations, removing duplicate prompts and
creating stratified training and evaluation splits. Structural validation,
reference execution and source boundaries each addressed a different part of
quality; none alone established that every generated task was correct.

### Connect generated work to the learner

The policy being trained had its own table-parsing, Python and SQL tools,
separate from the generation harness. A teacher could solve the generated
tasks with those tools; I rendered its assistant actions and tool observations
into SFT records while preserving which tokens were training targets. For
reinforcement learning, the student attempted the tasks and the verifier scored
its output. The task data, policy plugin and verifier were combined with the
selected model or SFT checkpoint in the training entry point.

I exercised the connection with a Haiku 4.5 teacher using the policy tools. The
sampling stage saved its conversations and task-scorer results; a filtered
trajectory set then fed SFT with assistant actions and tool observations rendered
under explicit trainable-token boundaries. A Qwen3.5-4B run reached final
trainer-state and sampler checkpoints. I then assessed the final sampler on tasks
through the policy tools, exercising the complete path from generated work
through tool-using demonstrations and student training to checkpoint assessment.

## Distilling tool-using policies

Knowledge-only training leaves out much of what makes an agent useful. An agent
may have to inspect files, execute code, interpret tool output and decide what
to do next. Training on those trajectories introduces a different integration
problem from training on plain question-answer pairs.

In April, I implemented a tool-trajectory on-policy distillation path alongside
the coding-agent training work. Unlike the teacher-generated SFT demonstrations,
the student supplied the trajectory by acting in a sandbox. Its record
retained the model-native tokens and sampling log probabilities, and the teacher
scored the same student-generated actions under a causal view of the interaction.
Tinker performed the parameter updates, after which the sampler was refreshed
for subsequent rollouts.

Here the teacher received the causal conversation and tool history. In the
retained runs, a larger fixed teacher supplied a different policy over that
same history. Its advantage was not extra document context or access to future
outcomes before scoring an earlier action. That is a different teacher–student
relationship from the earlier knowledge-compilation experiments.

The response mask was central. A trajectory contains model output, prompts and
tool observations. The model should learn from the tokens it generated, not be
credited with producing a compiler message or a file's contents. Teacher scoring
also has to respect next-token alignment and the information available at each
action. A final transcript rendered as convenient text is not automatically a
correct training record.

The teacher term was added to verifier-reward advantages in the training
integration. That made it important not to infer the response mask from nonzero
advantages. If every attempt
received the same verifier reward, the relative advantages could all be zero
while teacher feedback still supplied a learning signal. I retained an
independent mask for generated tokens and shifted it with the targets and
captured probabilities. That kept teacher supervision on the model's actions
without accidentally applying it to observations—or suppressing it altogether.

<figure class="specialization-figure" aria-labelledby="trajectory-caption"><div class="trajectory-diagram"><div class="trajectory-item observation"><span class="diagram-label">Input</span><strong>Prompt and available context</strong><span>Conditioning only</span></div><div class="trajectory-item action"><span class="diagram-label">Model action</span><strong>Tool call</strong><span>Generated tokens · update mask on</span></div><div class="trajectory-item observation"><span class="diagram-label">Observation</span><strong>Tool result</strong><span>Conditioning only · update mask off</span></div><div class="trajectory-item action"><span class="diagram-label">Model action</span><strong>Next action or answer</strong><span>Generated tokens · update mask on</span></div></div><figcaption id="trajectory-caption">A tool trajectory mixes generated actions and external observations. Both can condition the next action, but only the model's generated response tokens belong in its response-loss mask. The pattern repeats across tool calls.</figcaption></figure>

I joined task results to their generating trajectories, checked token and mask
alignment, and retained update and sampler identities so an update could be
traced back to its training evidence.

In May, I trained specialist policies with GRPO using grouped sandbox rollouts
and checkpointed updates. One target was [Promptfoo](https://github.com/promptfoo/promptfoo),
an LLM-testing and red-teaming framework. I evaluated a trained checkpoint and
its starting model on work involving configuration, provider integrations,
diagnosis and red-team design. The analysis joined actor trajectories and
separate verifier reports to task-specific criteria, completion state, tool use,
elapsed time and token usage. That supported investigation of how a policy
carried out the work, rather than treating a shorter response or one aggregate
reward as sufficient evidence of improvement.

This connects the specialization research to the execution and trace machinery described in the
[platform article](/distributed-agent-training-and-evaluation/).

## A related application in Nemoral

In the Stanford CS194 team project
[Nemoral](https://github.com/StanfordCS194/spr26-Team-26), I worked on a
user-facing application of related ideas: a prompt and budget leading to a
fine-tuned model with an inspectable training and experiment history.

The application connected data acquisition and curation, approval of a plan,
fixed training and validation data, Tinker LoRA SFT, and budgeted experiment
selection. Candidate changes were evaluated and either kept or reverted, with
checkpoint and metric artifacts available through the application.

I implemented the Tinker LoRA/SFT runner and budgeted experiment-loop integration,
then worked on real validation, token-normalized loss and usable model/artifact
outputs. Nemoral was a separate Stanford team project, with collaborators owning
substantial components. The [final project documentation](https://github.com/StanfordCS194/spr26-Team-26/blob/934b10468c423e1c3231ea8d8c459eed6ac01f4e/docs/final-documentation.md)
and my [training](https://github.com/StanfordCS194/spr26-Team-26/pull/114)
and [AutoResearch integration](https://github.com/StanfordCS194/spr26-Team-26/pull/116)
contributions provide public source material.

## What carries forward

This work made the intended capability, training distribution, tool environment,
sampled actions and checkpoint state explicit parts of one engineering problem.
A useful improvement could come from a better source allocation, an aligned
teacher, a working tool interface, or a reusable investigation procedure—not
only a change to the optimizer. The training agent could carry out that work;
the outer researcher could improve how it was carried out.

That experience shaped the later
[distributed platform](/distributed-agent-training-and-evaluation/), which
generalized the execution and learning machinery. The
[repository-specific construction workflows](/from-software-work-to-specialized-agents/)
applied the same attention to information, tools and reusable procedure without
requiring a weight update. Together, the projects span both ways of building a
specialist: changing what the model has learned and changing the system through
which it does the work.

## Sources and contribution

This account is based on the original training implementations, versioned
agent plugins, experiment records, source-derived datasets and contemporaneous
design discussions. The PostHog material came from public documentation and the
handbook; this work does not imply a PostHog customer relationship.

I led the training-method implementations, specialization experiments,
training-agent and researcher integration, and the later executable-task/data
factory described here. The early PostHog work built on Nathan's document-to-data
generation machinery and the team's wider tooling. I used coding agents
extensively in developing and operating these systems. Nemoral was a separate
Stanford team collaboration. The underlying SynthLabs training implementations
remain private; this article explains the mechanisms without releasing
proprietary source or original conversations.

For the underlying training foundations, see the public
[Tinker Cookbook](https://github.com/thinking-machines-lab/tinker-cookbook) and
Thinking Machines' explanation of
[on-policy distillation](https://thinkingmachines.ai/blog/on-policy-distillation/).

<style>
.specialization-contents{font-size:12.5px;line-height:2;margin:30px 0 38px;color:var(--dim)}
article .katex{white-space:nowrap}
.specialization-figure{margin:38px 0 42px}.specialization-figure strong{font-size:13px;line-height:1.55;display:block}.diagram-label{display:block;font-size:11px;letter-spacing:.025em;color:var(--dim);margin-bottom:7px}.research-loop{border:1px solid var(--fg);padding:22px}.loop-heading>span:last-child{display:block;font-size:12px;line-height:1.65;margin-top:9px}.training-loop{border:1px solid var(--rule);margin-top:20px;padding:19px}.weight-loop{display:grid;grid-template-columns:1fr 26px 1fr;align-items:center;gap:10px;margin-top:19px;border-top:1px solid var(--rule);padding-top:18px}.diagram-arrow{text-align:center}.loop-return{font-size:11.5px;line-height:1.65;margin-top:18px;padding-top:15px;border-top:1px dashed var(--rule)}.shared-question{border-bottom:1px solid var(--rule);padding:15px 20px}.distillation-diagram{border:1px solid var(--fg)}.distillation-pair{display:grid;grid-template-columns:1fr 1fr}.distillation-pair>div{padding:19px 20px}.distillation-pair>div+div{border-left:1px solid var(--rule)}.distillation-pair p{font-size:12px;line-height:1.7;margin:10px 0 0}.distillation-update{border-top:1px solid var(--rule);padding:17px 20px}.distillation-update>span{font-size:11.5px;line-height:1.7;display:block;margin-top:8px}.trajectory-diagram{display:grid;grid-template-columns:1fr 1fr;gap:12px}.trajectory-item{padding:17px;border:1px solid var(--rule)}.trajectory-item.action{border:1px solid var(--fg)}.trajectory-item>span:last-child{display:block;font-size:11px;line-height:1.65;margin-top:9px}.specialization-figure figcaption{font-size:12px;line-height:1.7}
.empirical-scroll{overflow-x:auto;border:1px solid var(--rule);padding:10px;background:#fff}.empirical-scroll img{width:100%;min-width:600px;height:auto}.factory-chain{list-style:none;counter-reset:factory;display:grid;grid-template-columns:1fr 1fr;gap:12px;margin:0;padding:0}.factory-chain li{counter-increment:factory;margin:0;border:1px solid var(--rule);padding:17px}.factory-chain .diagram-label:before{content:counter(factory) ". ";color:var(--fg)}.factory-chain li>span:last-child{font-size:11.5px;line-height:1.7;display:block;margin-top:9px}
.specialization-wide{width:min(1000px,calc(100vw - 56px));position:relative;left:50%;transform:translateX(-50%)}.specialization-wide figcaption{max-width:660px;margin:14px auto 0}
.empirical-scroll:focus-visible,.sql-specimen:focus-visible{outline:2px solid var(--fg);outline-offset:4px}
@media(max-width:760px){.specialization-wide{width:100%;position:static;transform:none}}
@media(max-width:520px){.research-loop{padding:17px}.training-loop{padding:15px}.distillation-pair{grid-template-columns:1fr}.distillation-pair>div+div{border-left:0;border-top:1px solid var(--rule)}.weight-loop{grid-template-columns:1fr}.diagram-arrow{transform:rotate(90deg)}.trajectory-diagram{grid-template-columns:1fr}.specialization-figure strong{font-size:12.5px}}
@media(max-width:520px){.factory-chain{grid-template-columns:1fr}}
</style>

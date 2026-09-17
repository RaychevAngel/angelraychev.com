---
title: "Training a Code Reviewer We Actually Use"
description: "A living engineering case study: turning our own review history into useful practice, credible rewards, and a reviewer worth using."
updated: 2026-09-17
---

*Project synthesis · [Method and system](/training-a-code-reviewer-we-actually-use/method/) · [Development record](/training-a-code-reviewer-we-actually-use/progress/)*

We already use capable AI code reviewers. Why train another one?

The question is whether our own review history can teach a model to review our
code more usefully: to follow the contracts between our systems, recognize
consequential mistakes, and avoid convincing objections that waste the team's time.
A model that knows more general programming advice is not the point.

Before asking another business to trust us to develop its agent, I want an example
that earns its place inside SynthLabs. The title describes that destination.
It is not an announcement that we have arrived.

## Where things stand

**Evidence through 17 September 2026, 3:30 AM Pacific.**

We can turn historical review opportunities into runnable tasks, collect independent
reviews, and grade saved outputs separately. We have observed both meaningful
catches and misses, compared reviewer instructions, and completed an initial
on-policy training canary with **two actual optimizer updates**.

Only its first checkpoint passed the training-data and update-lineage checks for
reload testing. The second remains unqualified because its grading did not meet
the acceptance standard used for that run. We subsequently clarified one reward
decision and tested the new rule separately; that does not rewrite the old result.

**We have not yet demonstrated that the trained reviewer is more useful than the
untrained baseline.** Checkpoint reload, protected comparisons and repeated team
use remain ahead at this checkpoint. Automatic GitHub comments are not enabled.

The important distinction is not “nothing works” versus “the project works.”
Execution, measurement, learning and usefulness each need their own evidence.

## Two claims to earn

**The reviewer is useful. Training made it more useful.**

A useful untrained reviewer establishes only the first. A higher historical score
does not establish either if the resulting reviews are distracting or wrong.

The intended comparison separates three configurations:

1. The original model with a basic harness.
2. The same model with a competent review-specific harness and adequate context.
3. The trained model under that same competent setup.

Here, a harness is the instructions, tools and execution rules around the model.
Changing those rules, adding missing dependencies or supplying relevant code can
improve behavior without changing weights. Those improvements are valuable, but
they are not training results. Existing commercial reviewers remain practical
comparators; beating our own weak setup would not establish a reason to switch.

Company-specific understanding is a hypothesis to test, not a property bestowed
by using a private repository. The interesting work involves local responsibilities,
cross-service assumptions, intentional exceptions and historical decisions.
Stable patterns might become learned judgment; changing facts still need to be
retrieved from current, legitimate evidence.

The initial responsibility is review, not repair. The agent may investigate in
isolated scratch space. It must not edit the authoritative change, approve it or
merge it. A good finding need not prescribe the single best fix.

## One review that changed the reward question

A historical export workflow used a small marker to control retries. In one
failure path, an unreadable or malformed marker could leave later attempts stuck.

Qwen identified the problem and ran a reproduction. But its review also offered
an optional alternative: instead of repairing the retry behavior, emit a clearer
diagnostic. Logging would make the failure easier to understand; by itself it
would not make the export recover.

*This is a simplified description of an internal historical case, not a quotation
of the review or a claim about the current deployed system.*

That produced a consequential question. Should a correct, actionable diagnosis
with an inadequate optional suggestion rank below saying nothing?

A strict interpretation of the proposed penalty would have done exactly that.
I decided it was the wrong ordering for the reviewer we want. The diagnosis still
helps. The inadequate alternative should reduce its credit, but should not
automatically erase its value. An instruction genuinely opposing the accepted
behavior remains a different, more serious error.

For this three-issue reference, the revised policy produced:

| Review variant | Score |
| --- | ---: |
| Correct diagnosis, without the inadequate alternative | 1/3 |
| Correct diagnosis, with the inadequate optional substitute | 1/6 |
| Empty review | 0 |

The two diagnosis variants were each graded twice with the same result. The empty
score follows the unchanged deterministic calculation and was checked offline.
A broader fixed panel covered eight inputs with two judgments each, including
genuinely opposing advice; all repeat pairs agreed on credit and error categories.
These are **retained reviews and labeled controls**, not sixteen new independent
reviews or proof of universal judge reliability.

The new rule was adopted for subsequent work. Original grades and the unqualified
checkpoint were preserved.

The lesson is larger than this fraction: **the judge cannot decide our product
values for us.** Better instructions cannot resolve a reward policy whose desired
ordering has not been made clear.

## How the learning setup works

<figure>
<svg width="360" viewBox="0 0 360 316" style="margin: 0 auto" role="img" aria-labelledby="review-flow-title review-flow-desc" xmlns="http://www.w3.org/2000/svg">
<title id="review-flow-title">The reviewer and judge see different evidence</title>
<desc id="review-flow-desc">Historical work becomes a frozen task. The reviewer produces a captured review. The judge compares that review with private historical evidence. Training uses eligible reviewer trajectories and rewards.</desc>
<g fill="none" stroke="#000" stroke-width="1">
<rect x="20" y="1" width="320" height="50"/><rect x="20" y="81" width="320" height="50"/>
<path d="M180 51 V75 M175 68 L180 75 L185 68 M180 131 V145 H95 V157 M90 150 L95 157 L100 150"/>
<rect x="10" y="163" width="170" height="58"/><rect x="90" y="257" width="180" height="58"/>
<path d="M95 221 V240 H180 V251 M175 244 L180 251 L185 244 M275 221 V240 H180"/>
</g>
<g fill="#000" font-family="ui-monospace,monospace" text-anchor="middle" font-size="14">
<text x="180" y="23">Frozen task</text><text x="180" y="41" font-size="12">Code + allowed context</text>
<text x="180" y="103">Reviewer</text><text x="180" y="121" font-size="12">No historical answers</text>
<text x="95" y="185">Captured review</text><text x="95" y="206" font-size="12">Fixed, reusable output</text>
<text x="275" y="185">Private history</text><text x="275" y="206" font-size="12">Findings + discussion</text>
<text x="180" y="279">Judge</text><text x="180" y="300" font-size="12">Meaning + fixed scoring</text>
</g>
</svg>
<figcaption>The task describes the work and evidence; profiles describe the agents. Collection can stop at the captured review. Training additionally requires rewards and eligible reviewer trajectories.</figcaption>
</figure>

The preparation starts with a **review opportunity**, not merely a pull-request
number. One PR can contain several revisions and review rounds. We pin the code
being reviewed, its comparison base, the requested scope and an information cutoff.

The compiler then prepares the source snapshots, diff, permitted context and
private historical records. This is mainly mechanical work. We do not want
task creation to require somebody to write a bespoke answer key for every PR.
Interpreting evidence is a separate responsibility; ambiguous cases still need
qualification or exclusion.

The reviewer gets a useful environment without the answers. Later reviews,
fixes and explanations stay private. Blocking the internet alone is insufficient:
a local Git store can still contain future commits. Conversely, stripping away
all surrounding code would manufacture a weak baseline. The goal is sufficient,
time-correct evidence.

The current reviewer uses **Qwen3.8-27B in Claude Code**. The selected judge uses
**Kimi K3**, with a shared historical-matching policy. They have separate execution
roles. Only eligible, freshly generated reviewer data contributes to the on-policy
update; the judge's text is not mixed into the actor's training data.

The [method notes](/training-a-code-reviewer-we-actually-use/method/) explain the
task, profiles, output contract, scoring and evaluation boundaries in more detail.

## What the experiments have actually taught us

### Observe reviews before perfecting their scores

We spent too long preparing to measure a distribution we had barely observed.
Some integration repairs were necessary, but that did not make the sequence
efficient. Baseline collection and judge qualification should have progressed
independently.

The first runs contained missing dependencies, investigations that never submitted
a review, and completed empty reviews. Those are different outcomes.
An incomplete run is not an empty review. A missing build tool is not evidence
that a model needs company-specific training.

### A cleaner instruction is not automatically a better reviewer

A matched development campaign compared our baseline instructions with a
diagnosis-only variant across five cases, with four planned attempts per case
and arm.

Each arm produced 17 captured reviews: ten empty and seven nonempty. There were
six failures among the forty planned slots; one occurred before model inference.
We did not replace failures with convenient successful draws.

The diagnosis-only instruction sometimes reduced unwanted repair advice.
It did **not establish better defect detection overall**, so we kept the baseline.
These are small, adaptively selected development cases, not an accuracy estimate
for all Synth PRs. “Nonempty” is an output category, not a quality judgment.

### Reference agreement and useful review can diverge

In another historical case, Qwen reproduced a conflict between a newly introduced
interface and an earlier validation stage. The finding was absent from the selected
historical reviews. A separate source audit supported the bounded claim, and I
accepted it as useful.

Our historical-only score would not reward it.

That is a real limitation of the measurement, not permission to quietly change
the reference after seeing an answer. We kept the original assessment and recorded
the usefulness judgment separately. Whether optimizing that proxy improves the
reviewer we want remains an empirical question.

### Repeatability is necessary, not sufficient

An earlier judge configuration gave the same retained correct review both +1 and
−1 across repeats. It had inferred a contradiction that the review did not state.
That is judge variation, not useful variation in the reviewer's behavior.

We compared judges using the same saved reviews, supplemented by controls that
isolate specific distinctions. Passing obvious controls did not excuse failures
on natural outputs. Nor would consistently applying the wrong policy make a
judge good. The optional-remedy example above required a policy decision as well
as a reliable implementation.

## The next result worth reporting

The training canary established actual updates, successor sampling and saved
checkpoints. It has not established improved reviewing.

The next decisive result is a comparison of original and trained weights under
the same competent harness and information access, followed by protected evaluation
and actual team use. The first learning material is narrow; a few successful
internal cases would not establish company-wide expertise.

We need enough real updates to investigate learning, not a permanently tiny
training smoke test. But scale should follow credible tasks and rewards.
More optimization against the wrong preference would move us faster in the wrong
direction.

Success is a reviewer whose findings we repeatedly want to read, with evidence
that training helped produce that behavior. That is the result still to earn.

---

This is an edited account of work conducted with coding agents, checked against
saved conversations, run reports and retained artifacts. Internal code, credentials,
raw conversations and private artifact locations are not published. It is not an
independently reproduced benchmark report.

The first public version stopped at the September 13 research stage. This revision
replaces that stale “current status,” separates the method from the chronology,
and makes the observed limitations explicit. The
[development record](/training-a-code-reviewer-we-actually-use/progress/) preserves
the sequence and corrections.

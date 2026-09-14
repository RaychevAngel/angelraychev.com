---
title: "Training a Code Reviewer We Actually Use"
description: "A development record: turning historical pull requests into company-specific review tasks, trustworthy rewards, and an agent our team chooses to use."
updated: 2026-09-13
---

*From historical pull requests to a company-specific agent.*

This project began on **13 September 2026, at 2:13 PM Pacific**. The goal is to
train a code reviewer for SynthLabs that our team actually wants reviewing its work.
This is a living development record, not a retrospective success story.

**Current status — 13 September, 7:22 PM Pacific:** we have defined the intended
responsibility, investigated historical review data and public implementations, and
shortlisted task-generation approaches. We have not yet generated and qualified a
reviewer task for this project, run its model baseline, trained a reviewer, or
demonstrated an improvement. The next proposed experiment is a small comparison of
existing task generators on our own review evidence.

## What would count as success?

A reviewer that catches consequential problems, explains why they matter, and does
not bury the team in convincing but incorrect objections. Something we return to
because it helps—not a checkpoint we have to explain into sounding useful.

There are two separate claims to earn. First, **the resulting agent is useful**.
Second, **training contributed to that usefulness**. A useful untrained reviewer
does not establish the second claim. A trained model with a higher score but
annoying reviews does not establish the first.

The intended comparison is therefore an original model with a basic harness, the
same model with our review-specific harness, and the trained model with that same
specialized harness. Here, the harness means the instructions, tools, context
access and execution rules surrounding the model. Existing reviewers remain
practical comparators: beating our own weak configuration would not, by itself,
give us a reason to switch.

The project is bounded to **reviewing code**, not autonomously implementing fixes,
merging changes, or replacing the engineering team. Repository coverage and the
first training corpus are still open decisions. We want to bound the experiment
without making the working environment artificially easy.

## 13 September, 2:13 PM — prove it to ourselves first

The starting point was a conversation about delivery, not model selection. Before
asking another business to trust us to develop an agent, we wanted a useful example
inside our own company. Believing that the machinery can work is different from
showing a colleague work they would accept, at a quality and speed they value.

Code review is a good place to attempt that demonstration because the work already
exists. We have repositories, pull requests, review conversations and engineers
who understand the intended behavior. We do not first need to reconstruct an
unfamiliar company's operations or invent a reason someone would want the service.

That does not make review easy. It makes the difficult parts accessible.

The company-specific hypothesis is also concrete. A reviewer may need to understand
contracts between services, ownership boundaries, intentional exceptions and past
decisions. The question is whether training can help it apply that understanding
more reliably than the original model given a competent harness and the relevant
information. Company-specific work is a reason to investigate specialization, not
proof that changing weights is necessary.

## 13 September, 4:47 PM — the history is the starting material

We already use CodeRabbit and Codex reviews. Their comments, the responses to those
comments, subsequent changes and our own judgments provide possible learning
signals. The initial proposal was to turn that history into realistic review
opportunities rather than manufacture unrelated bugs.

I leaned toward a reviewer rather than an editor. Establishing that a change has a
particular defect is already difficult. Requiring the agent to implement the best
repair would add another problem: several different fixes might be legitimate,
with trade-offs a judge would also have to assess.

Several scope choices remained deliberately unsettled. One repository is easier
to bound, but cross-repository contracts are part of the possible value. Selecting
one defect class could simplify evaluation while excluding dependencies needed to
understand it. Using every PR immediately could increase coverage while admitting
poorly understood examples. A small initial corpus need not imply a permanently
narrow reviewer.

The working actor candidate was Qwen3.8-27B in Claude Code. A judge could use the
same model family, but receive **privileged information**: historical findings,
discussion and later evidence withheld from the acting reviewer. Those were design
candidates, not exercised configurations or a claim that the judge was already
reliable.

The first research pass inspected our material and existing task machinery. It
helped distinguish packaging a task from judging a review, but moved too quickly
from that inspection into a proposed implementation.

## 13 September, 5:42–5:58 PM — correct the research, then the design

I pushed back on that first pass. We should not learn every lesson by repeating
mistakes other teams have already recorded. The next pass examined public reviewer
implementations, evaluation methods, data-selection problems and operational
experience. The earlier recommendation was superseded rather than left alongside
the revised one as an equally current plan.

The most useful outcome was not a larger reading list. It was a better ordering of
the decisions that could invalidate the experiment.

### A PR is not yet a task

One PR can contain several revisions and several review rounds. A comment can be
correct about an earlier revision and wrong about the final merged version. The
task must identify the **review opportunity**: the exact code being reviewed, the
comparison base, whether the requested review is full or incremental, and what
information was available then.

Later fixes and explanations can help establish the assessment standard. They must
not quietly become information the reviewer had before making its decision.
Blocking the internet is not sufficient if the workspace still contains future
commits or answer-bearing files.

The environment should nevertheless be useful. Removing the surrounding code just
to simplify isolation could remove the very evidence needed to understand a
company-specific issue. The target is a time-correct working environment, not an
uninformative one.

### Historical authority is different from historical completeness

A strong review followed by careful discussion and a confirmed correction may be
better evidence than a smaller judge's fresh attempt to reconstruct the whole
investigation. The proposed division of labor is to establish that evidence once,
then let the judge apply it repeatedly.

But two mistakes sit on opposite sides of this approach. Treating every historical
comment as truth would reproduce false alarms. Treating the historical comments as
an exhaustive answer key would penalize an agent for finding a real additional
problem.

We therefore need to preserve what the history actually established: accepted
defect, refuted allegation, partially correct explanation, intentional exception,
deferred fix or unresolved disagreement. A closed thread alone does not settle
these distinctions. Nor does a high severity label or agreement between two bots.

There is a further time distinction: a later conversation can reveal a fact that
was already true, or create a new team decision. The latter does not automatically
make the earlier reviewer wrong.

### A reward needs to order reviews correctly

The current proposal is an agent judge using a graded rubric, with deterministic
aggregation into a scalar reward. It should assess whether a finding identifies
the problem, gets its conditions and consequences right, locates it usefully and
communicates its importance. False allegations and duplicates are quality costs.
Polished prose cannot compensate for a central falsehood.

There is **no efficiency penalty in this experiment's proposed reward**. First we
need to know whether it measures review quality.

Calibration means checking meaningful contrasts. Correcting a wrong condition
should improve the score. Adding an unsupported allegation should worsen it.
Equivalent wording should receive approximately equivalent credit. A partially
correct review should be distinguished from both a correct one and an incorrect
one.

We also need to separate two kinds of variation. Repeated actor runs tell us how
the reviewer varies. Repeated grading of the *same review* tells us how the judge
varies. Different rewards are not evidence of a useful learning signal if they
mostly reflect grading noise. None of this calibration has been demonstrated for
our proposed setup yet.

### Submission is a contract, not just a final paragraph

The preferred output design became one structured `submit_review` call containing
the final findings, including an empty list when appropriate. The submission should
be validated and recorded before the episode ends. Publishing comments to GitHub
is a separate operation.

This has a concrete public precedent: Canonical's
[submission tool](https://github.com/canonical/code-review-harness/blob/15b2e1279a2f88d79de6fc1fb8c1ead48e4c7a7e/packages/core/src/lib/createSubmitReviewTool.ts)
uses an output schema, awaits the sink and returns a termination signal. That is a
reusable mechanism, not a reason to inherit every other policy in the harness.
For an initial generator comparison, retaining its native file output may be
quicker than replacing a working interface before we have tested its substance.

## 13 September, 7:00–7:22 PM — try existing task generators

The next idea was to stop designing everything in the abstract: find existing
Harbor task generators, give a few of them our material, and inspect what they
produce. A Harbor task packages the instruction, environment and verification
needed to run an agent on a particular situation. Producing that package is a
necessary operational step; it does not establish that the task teaches the right
behavior.

The public-source investigation produced two leading candidates and a fallback.
These are **source-inspected candidates, not implementations we have successfully
run**.

**AACR-Bench Harbor** is the most concrete compiler route. Its
[adapter](https://huggingface.co/datasets/osolmaz/aacr-bench-harbor/blob/5fe5b028ed6a63d9ff04c2fe2f94526181b1b142/src/aacr_bench_harbor/adapter.py)
turns pinned review records and repository material into Harbor tasks. Its
[verifier](https://huggingface.co/datasets/osolmaz/aacr-bench-harbor/blob/5fe5b028ed6a63d9ff04c2fe2f94526181b1b142/src/aacr_bench_harbor/task-template/tests/verifier.mjs)
matches submitted findings to reference comments and computes an F1 score.
That gives partial credit for recovering references, but it is not our complete
quality rubric: an additional valid finding need not match a reference. Our own
records would also need to meet its input and repository-materialization contract.

**LangChain's eval-engineering workflow** is the more agent-assisted route.
LangChain describes constructing company-specific review tasks from historical
feedback, including tenant constraints and internal locking conventions. Its
[ReviewBench report](https://www.langchain.com/blog/evaluating-code-review-agents-with-reviewbench)
describes frozen PR context, repository access and grading that allows valid
findings beyond the curated baseline. The released
[authoring skill](https://github.com/langchain-ai/langchain-skills/tree/b7a2a8fc363d1711456f83d24230535c9fff93eb/config/skills/eval-engineering)
is a workflow for an agent, not a deterministic PR importer or a release of the
company's private review corpus. Reuse terms need checking before vendoring it.

**Harbor's own create-task and RewardKit workflows** provide a less specialized
alternative for authoring tasks and graded verifiers. The
[published skills](https://github.com/harbor-framework/harbor/tree/09e555a148f7c0c9995341513efda18449645a5e/skills)
offer reusable structure; they do not supply our historical evidence or establish
that our review rubric is calibrated.

We also found a useful near-match:
[SWE-Review's generator](https://github.com/LegoX/SWE-Review/blob/95b652e095e5ac8f16f08ae52fd3b26513c56097/scripts/data_pipeline/generate_review_tasks.py).
It genuinely produces review tasks, but its verifier scores whether a patch-fix
decision matches a stored outcome. That is a different target from rewarding the
quality of individual findings. A project can have the right task format and still
optimize the wrong responsibility for us.

No generator was installed or exercised as part of this investigation. No reviewer
training occurred.

## The next experiment

The proposed next step is **one frozen review episode through a concrete compiler
and an agent-assisted authoring route**, using comparable actor-visible material
and the same qualified historical evidence. A released public task can provide an
installation smoke test; it cannot substitute for testing our own material.

Start with each implementation's native behavior. Record what had to change:
configuration, an input adapter, the harness, or the judge. Replacing most of an
implementation would not count as it working out of the box.

The comparison has four gates:

1. **Operation:** can the generated task run through the intended execution path
   and preserve the submission and grading evidence?
2. **Meaning:** does it present a realistic review opportunity with enough context,
   no historical-answer leakage, and a defensible assessment standard?
3. **Reward:** do clearly better reviews receive better scores, consistently?
4. **Learning opportunity:** does the actual actor make meaningful mistakes, with
   reward variation corresponding to those mistakes rather than judge noise?

Only after one task survives those checks should we expand to contrasting episodes
and repeat model trials. Before optimization, we need a protected evaluation split
that keeps related revisions and shared defects from crossing between training
and test. A task repeatedly used to tune the judge or choose the harness is part
of development, not an untouched final exam.

The repository mix, final judge, exact rubric, training settings and deployment
choice remain open. We have made the next uncertainty smaller. We have not yet
resolved it.

## How this record will develop

The current-status paragraph will change as evidence changes. Dated entries will
preserve the important decisions, failed approaches and corrections. When there
are experiments, an entry should include the hypothesis, setup, representative
behavior, result and what that result does—and does not—establish.

This first entry was assembled from dated working discussions and source
inspection conducted with coding agents. It is an edited account, not a raw chat
transcript or an independently reproduced benchmark report. Private repository
material and internal discussions are not published here; public examples and
reusable artifacts can be added when cleared for release.

The final criterion remains unchanged: **did we build a trained reviewer that we
actually choose to use?**

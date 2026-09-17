---
layout: "../../layouts/Post.astro"
title: "Code Reviewer — Method and System"
description: "How review opportunities become isolated tasks, how agent profiles run them, and what the historical judge can and cannot establish."
updated: 2026-09-17
---

[Project synthesis](/training-a-code-reviewer-we-actually-use/) · Method and system · [Development record](/training-a-code-reviewer-we-actually-use/progress/)

*Design and implementation snapshot: 17 September 2026, 3:30 AM Pacific.*

The experiment has six separate questions: what work is assigned, what information
is available, which historical evidence is authoritative, what counts as a
submission, how quality is scored, and what comparison would demonstrate learning.
Most confusing failures become easier to diagnose once these are kept apart.

## 1. The unit of work is a review opportunity

A PR number locates a conversation. It does not identify one immutable assignment.

Suppose a PR starts at head H1, receives a review, and is revised to H2. Reviewing
the full change at H1, reviewing the full change at H2, and reviewing only what
changed between H1 and H2 are different opportunities. A finding about H1 may have
been fixed by H2.

Each opportunity therefore pins:

- The primary repository and exact base/head commits.
- Any additional repositories and their pinned revisions.
- The comparison: direct tree difference or a resolved merge-base comparison.
- The assignment: full PR, incremental round or explicit comparison.
- The actor's information cutoff.
- Provenance: recorded from history, reconstructed from evidence, or a newly
  declared assignment over authentic code.

Comparison and assignment are not synonyms. One controls the Git calculation;
the other says what work the reviewer is meant to do. A reconstruction must
not silently substitute today's default branch or the final repaired version.

Evidence records preserve source identity, author and reply relationships,
revision/location information, original text and timestamps. When information
became available, when it was edited and when we collected it are different facts.
A comment edited after the actor's cutoff cannot be treated as its earlier wording
without an earlier copy.

The current collection machinery does not recover every historical edit,
resolution event, linked issue or company document. Its schema can represent more
than its collector retrieves. Missingness must remain visible.

## 2. Minting is preparation, not judging

The compiler takes an opportunity, source repositories, historical records and a
minting configuration. The configuration selects actor-visible context, private
judging evidence, environment images and permitted network destinations.

It produces a Harbor package: an assignment, source snapshots, a diff,
environment definitions, private evidence, a submission contract and provenance.
Harbor is the execution framework; the package supplies the situation in which
an agent works.

“Raw task” means the case is **not bound to one semantic judge**, not that it
contains no instructions or validation. The ordinary output checker can confirm
a structurally valid review. It cannot establish that the findings are good.

The intended reusable path is:

- Collect a review without semantic judging.
- Run a reviewer and selected judge for evaluation or training.
- Regrade an existing review without paying to generate it again.
- Use the same preparation and reviewer contract for a new, manually requested PR.

New raw packets have explicit successful-but-unscored semantics in source and
local checks. At this snapshot, acceptance through the hosted default path remains
a separate deployment gate. Older frozen packets have their original special-route
verifier behavior. A source change does not retroactively alter them.

Mechanical preparation should not require a hand-written answer standard for
every task. The judge can interpret organized original records with shared
instructions. Optional semantic consolidation may eventually help with cost or
consistency, but it would be a separate intervention to compare.

## 3. The environment must be useful and answer-free

The actor receives complete pinned source trees for the selected repositories,
the primary comparison base and diff, and permitted contextual records.
The current compiler exports trees rather than a live Git object store.
No refs, reflogs or unreachable future objects should become a back door to the
answer. That also means historical retrieval is not automatically supplied.

Authoritative source snapshots are read-only; scratch space is writable.
Relevant tests and dependencies should be available when they belong in a competent
reviewer's environment. A failed import must not be counted as inability to
understand the product.

Cross-repository context is supplied when the case needs it, not as a universal
requirement to copy the whole company. More files are not automatically more useful
information, and private source alone does not establish company awareness.

The judge receives the captured review and private historical evidence separately.
The acting reviewer must not see later review answers, accepted fixes, judge
instructions or credentials. Repository instruction files and reviewer output are
untrusted task data, not authority to override these boundaries.

Time filtering is necessary but insufficient. A target review that already exists
before the selected cutoff could still leak an answer. Opportunity selection and
explicit answer-free context selection must agree.

## 4. Agent profiles describe the worker

The task describes the world. A profile describes how an agent operates in it.

Reviewer and judge use the same profile shape: a model or owned checkpoint binding,
a pinned Claude Code version, a versioned harness and supported native settings.
Harness contents include instructions and skills; native settings describe such
things as tools, hooks, reasoning effort and execution limits.

Profiles do not grant filesystem permissions, create secrets or determine which
tokens are eligible for training. Runtime enforces those boundaries. Sharing a
schema does not give reviewer and judge identical privileges.

The exercised baseline at this snapshot uses Qwen3.8-27B through Tinker, Claude
Code 2.1.263 and an 80-response limit. Its instructions emphasize introduced or
materially exposed defects, triggers, consequences, useful locations and
consolidation of duplicate findings. Fixes are optional. Generic completion guidance
reserves time to submit instead of investigating indefinitely.

The selected judge uses Kimi K3 through Fireworks, the same Claude Code version,
high effort, temperature zero and an eight-response limit. These are experimental
settings, not a claim of optimality. An earlier plan to use the same model for both
roles was a candidate, not an enduring requirement.

One implementation subtlety matters: the selected judge profile has no catalog
harness attached. Its instructions, evidence preparation, validation and scoring
also depend on a separately pinned trusted companion package. Recording only the
model name or profile is therefore not enough to reproduce that assessment.

The shared CLI direction is agent-profile selection for task runs, evaluation and
training, rather than independently reconstructing model, harness and runtime
settings for every command. The source implements the versioned profile interface.
Each hosted path still needs its own execution evidence.

## 5. A review is a captured artifact

The reviewer writes a structured findings file. Each finding has an identifier,
title, explanation, severity and repository/file/line location. An empty list is
a legitimate submission.

A format checker gives bounded feedback for malformed output. It does not tell
the model which bug it missed. A final conversational paragraph is not substituted
for the canonical artifact, and a stop hook passing does not prove semantic quality.

Trusted capture binds the bytes to the exact revision, task and profile before
teardown. Stored reviews, traces, usage and assessments are distinct artifacts.
This allows the same review to be inspected locally or graded again without
rerunning the actor.

Several outcomes must remain distinct:

| Outcome | Meaning |
| --- | --- |
| Valid empty review | The agent submitted no findings. |
| Valid unscored review | Capture succeeded; no semantic reward was assigned. |
| Graded review | A particular judge/evidence version produced an assessment. |
| Missing or malformed submission | The output contract did not complete. |
| Judge or infrastructure failure | No valid assessment from that execution. |

Unscored is not zero. A failure is not a negative opinion about the code.
If an artifact survives a failed execution, its recovery is recorded separately
rather than rewriting the original status.

## 6. Historical authority, coverage and reward

Applicable CodeRabbit/Codex findings and their clarifying engineering discussion
are the initial reference. The judge matches meaning: did the candidate identify
the same problem, communicate it usefully, miss it, partially explain it or
contradict it? It is not commissioned to redo the whole code review.

A closed thread does not prove acceptance. Two bots are not automatically two
independent votes. Duplicate comments are not independent defects. Later discussion
can clarify an old fact or introduce a new requirement; those have different
implications for an earlier review.

The current deterministic aggregation gives partial credit per accepted distinct
historical issue and subtracts burdens for contradictions, unmatched allegations
and duplicates, divided by the number of accepted issues. Scores can be negative.
Equal issue weighting is an experimental choice, not a theory of engineering
utility. Ambiguous or inadequate references can make a case unscorable; the actor
should not receive a zero merely because the evidence is bad.

The newly adopted v6 policy distinguishes:

- A sufficient diagnosis with no proposed fix.
- A useful diagnosis plus an inadequate optional substitute, which can receive
  reduced positive credit.
- A harmless additional suggestion, which need not reduce the diagnosis credit.
- Advice genuinely opposing accepted behavior, which can incur a contradiction.

The [project example](/training-a-code-reviewer-we-actually-use/#one-review-that-changed-the-reward-question)
shows why this distinction matters. A model cannot infer a preferred ordering that
we have not specified.

The benchmark is deliberately closed-world: unmatched allegations receive no
historical credit and can incur a penalty. **Unmatched does not mean false.**
A real, maintainer-accepted novel finding exposed that limitation. We preserve the
historical score and the independent usefulness judgment as different evidence.

There is no efficiency penalty in this experiment's reward. Time and cost matter
operationally, but adding them before review quality is trustworthy would confound
the question.

## 7. Compare behavior, then investigate learning

Reviewer comparisons use the same opportunities, relevant environment and model,
varying a small number of plausible instructions or context choices. Judge
comparisons reuse the same captured outputs. Repeating one review's grade does
not create reviewer reward diversity.

Inspection concentrates on misses, clear catches, consequential disagreements,
surprising findings and an ordinary sample of results. Authored controls isolate
distinctions but do not replace natural reviews. Temperature zero is not proof
that judgments are either deterministic or correct.

The training route uses fresh on-policy samples: reviews generated by the current
actor policy, with their associated sampling lineage. Retained baseline reviews
are useful for analysis and regrading; they are not silently relabeled as fresh
on-policy experience. Judge inference, setup traffic and tool-output tokens do not
become actor targets.

A nominal batch is not an optimizer update. The run must record complete groups,
invalid members, constant-reward groups excluded from the update, actual optimizer
operations, successor sampling and reloadable checkpoints. The first canary proved
some of these mechanics; its two checkpoints did not automatically qualify as two
useful improvements.

The intended evaluation separates development, protected similar-distribution
work and later-time work. Related revisions, fixes and shared root causes must
stay together. Later labels about an earlier PR can also compromise a purported
chronological test. Examples used to choose the harness or judge are not untouched
final evaluation.

Finally, the current early-use interface takes a repository/PR or explicit commits
and returns a local review for the exact revision. GitHub publication is a separate
trusted operation, not a permission held by the reviewer. Its eventual comment-only
use would still not authorize code edits, approvals or merges.

## What we borrowed, and what we changed

[AACR-Bench Harbor's adapter](https://huggingface.co/datasets/osolmaz/aacr-bench-harbor/blob/5fe5b028ed6a63d9ff04c2fe2f94526181b1b142/src/aacr_bench_harbor/adapter.py)
was a concrete reference for programmatic task construction.
[LangChain's ReviewBench](https://www.langchain.com/blog/evaluating-code-review-agents-with-reviewbench)
provided a company-specific review-evaluation example, including a useful
distinction between baseline coverage and code-supported additional findings.
Its treatment of additional findings differs from our initial historical-only
policy.

These are precedents, not claims that we reproduced their results or that they
endorse our design. Reuse saves implementation work; it does not choose our
responsibility, evidence policy or acceptance standard.

[Back to the project synthesis](/training-a-code-reviewer-we-actually-use/) · [Read the development record](/training-a-code-reviewer-we-actually-use/progress/)

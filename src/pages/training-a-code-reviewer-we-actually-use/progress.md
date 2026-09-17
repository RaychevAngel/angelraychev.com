---
layout: "../../layouts/Post.astro"
title: "Code Reviewer — Development Record"
description: "Dated findings and corrections: task construction, baseline reviews, judge comparisons and the first on-policy updates."
updated: 2026-09-17
---

[Project synthesis](/training-a-code-reviewer-we-actually-use/) · [Method and system](/training-a-code-reviewer-we-actually-use/method/) · Development record

This is a curated record of decisions and evidence, not an operational event
stream. Dates are Pacific time. The latest entry covers evidence through
**17 September 2026, 3:30 AM**. Private code and raw conversations are not reproduced.

## 17 September — actual updates, and a reward-policy correction

### The training canary

A completed canary ran sixteen reviewer/judge pairs and performed two actual
optimizer updates. The first update used a qualified group with useful reward
variation; a constant-reward group was excluded. The recorded successor sampler
was then used for the next collection, and checkpoints were registered.

That establishes a real update path, not improved reviewer performance.

The first checkpoint passed the training-data and actor-only lineage checks and
was selected for reload testing. The second remained unqualified: its grades
did not satisfy the strict interpretation under which that run had been accepted.
We preserved both checkpoints and their original evidence.

A separate reload attempt failed before inference because of a serialization
mismatch between two components. A bounded source fix was merged. At this cutoff,
successful independent reload and comparison were still outstanding. This failure
was neither evidence of a bad trained model nor a reason to call the reload
successful because source tests passed.

### The distinction the rubric needed

A natural review correctly diagnosed and reproduced a retry failure, then offered
logging alone as an optional alternative to a repair. Under the strict proposed
interpretation, its reward would fall below an empty review.

A reminder added to the judge's instructions did not resolve the comparison on
retained outputs. This was not simply a request for more forceful prompting:
we needed to decide what behavior should be preferred.

I chose the ordering: a clean, actionable diagnosis above a diagnosis with an
inadequate optional substitute, and that useful-but-flawed review above silence.
Genuinely opposing advice remains negative. The exact fraction matters less than
that ordering.

The revised shared policy was tested on eight fixed inputs with two judgments
each. All sixteen assessments completed, and repeat pairs agreed on credit and
error categories. The clean diagnosis scored 1/3; the insufficient-substitute
variant scored 1/6. Empty remained zero by the unchanged scorer. Separate controls
continued to penalize genuine opposition.

This is a bounded qualification using known development outputs and controls,
not a universal reliability result. The new policy applies to subsequent work.
It does not overwrite old grades or retrospectively qualify the second checkpoint.

### Current boundary

The selected reviewer remains Qwen3.8-27B in Claude Code; the selected judge is
Kimi K3 with the historical-matching policy. Local review collection has been
demonstrated. The newer unified capture/checkpoint path still requires live
acceptance, and automatic GitHub comments are not enabled.

Next: finish checkpoint reload, run a substantive multi-update experiment with
the qualified reward, compare original and trained weights under matched
conditions, then evaluate protected cases and practical team use. A running
scoring pipeline is not the destination.

## 16 September — from isolated attempts to informative comparisons

### A matched harness experiment

We compared baseline review instructions with a diagnosis-only variant across
five development cases, four planned attempts per case and arm. The actor model,
task context, tools and route were held fixed within the comparison.

| Outcome | Baseline | Diagnosis-only |
| --- | ---: | ---: |
| Planned attempts | 20 | 20 |
| Captured empty reviews | 10 | 10 |
| Captured nonempty reviews | 7 | 7 |
| Failures / noncompletion | 3 | 3 |

There were 34 captured reviews across forty planned slots. Thirty-nine model
executions started; one slot failed before inference. Failed slots were not
replaced or counted as empty reviews. Earlier runs under other conditions were
not pooled into this comparison.

The changed instruction sometimes produced cleaner findings, but did not establish
better defect detection overall. We retained the baseline. Four draws per case
are not enough to establish a universal prompt effect, and a nonempty review can
still miss the historical defect or introduce an unsupported allegation.

**Interpretation correction:** the initial campaign readout was too categorical
about some conditional or incomplete repair suggestions. Later inspection showed
that those phrases did not by themselves establish a direct contradiction.
We preserved the text and grades while correcting that interpretation. The
subsequent reward-policy decision on September 17 is a further, explicitly
versioned change—not a silent cleanup of inconvenient evidence.

### Twelve more baseline reviews

A separate managed cohort collected four reviews for each of three episodes.
It completed all twelve captures: nine empty and three nonempty.

Those episodes represented **two independent PR groups**, not three: two were
different heads of the same PR. Keeping that grouping matters for both claims
of coverage and future train/evaluation splits.

One actual reproduction identified a defect accepted in later review discussion
on unchanged relevant code. An exact-head linkage rule had excluded that historical
finding from the earlier episode's reference. The correction required explicit
revision-applicability evidence and a separately versioned private reference,
applied consistently to all samples—not selective credit for one attractive answer.

A later instruction comparison showed promising detection on that particular
episode, but did not establish a general harness winner or trained improvement.
Interrupted attempts and incomplete cohorts remained visible rather than being
quietly replaced.

### A useful finding carried forward from September 15

In a dependency-equipped historical review, Qwen executed a small reproduction of
a contract conflict: a newly supported task shape was rejected by an earlier
validation stage on the examined path.

A source audit supported the bounded claim. Late on September 15, I accepted it as useful engineering
feedback. It was not in the selected historical findings, so the historical-only
score and my usefulness judgment disagreed.

We kept them separate. We did not turn an unmatched penalty into proof that the
finding was false, nor add a new reference just to make the score look better.
The example became an explicit risk to examine before trusting optimization of
the proxy.

### Judging the same review twice

Natural retained reviews exposed failures that simpler authored controls did not.
One judge configuration gave the same correct review +1 and −1 across repeats.
The negative result inferred opposition absent from the text.

Changing sampling or reasoning settings did not automatically make the judgment
sound. We compared models and simpler historical-matching instructions on retained
outputs, rather than rerunning the actor for each judging experiment. The selected
Kimi configuration subsequently supported a bounded initial learning experiment;
that adoption was narrower than a claim that the judging problem was solved.

### Shared interfaces and practical use

The execution design was reconciled around reusable tasks, versioned agent
profiles, run-selected reviewer/verifier roles, durable review capture and separate
regrading. A judge change need not force a new task when the task data is unchanged.

A manual interface accepted a repository/PR or explicit base/head and returned
an exact-revision review locally. This kept early use independent of automatic
GitHub publication. Work on profiles and successful-unscored raw tasks continued
alongside the experiments, not as a reason to discard completed evidence.

## 15 September — collect the behavior we are trying to improve

The first managed diagnostics produced two completed empty reviews on one
metadata-retention case, and two incomplete attempts on another runtime case
under different response limits. The empty reviews missed an accepted issue,
but their traces reached the same output for different reasons.

Some environments lacked expected dependencies; some investigations exhausted
their limits without submitting. Capture and publication defects also interrupted
the execution path. These were not interchangeable model failures.

The sequencing correction was to separate review collection from broad judge
qualification. Safe isolation, adequate context, bounded execution and durable
capture were prerequisites for collection. A finished reward policy was not.
Saved reviews could be graded later.

Generic guidance made completion limits explicit and reserved time to submit.
It did not reveal the historical answer. Environment/context changes were recorded
as new conditions rather than mixed into an unchanged baseline.

By the later development checkpoint there were eighteen historical captures across
eight PR groups, plus a separate manual smoke test. Different dependencies,
contexts and judges meant these were **not one frozen performance sample**.
The next need was controlled repetition, not an impressive total assembled from
incompatible runs.

## 14 September — separate preparation from assessment

Early task work exercised programmatic compilation and agent-assisted authoring
around historical review evidence. Prepared-review controls exposed instability
and contradictions receiving credit. A task running successfully had not made it
a good learning task.

The reusable design separated original records and environment construction from
the interpretation of those records. A hand-authored semantic standard was not to
be a mandatory step for every task. Existing standards could remain calibration
fixtures.

Reviewer and judge needed independent configuration and distinct access, despite
using a common execution framework. The output needed to be captured before
assessment, so changing a judge would not require generating another review.

Implementation was authorized end to end, including later training and qualified
comment-only deployment. Authorization was not evidence that any of those stages
had succeeded.

## 13 September — prove useful delivery to ourselves

We selected a company-specific reviewer because the work already exists, the
history is accessible, and our engineers can judge whether a finding matters.
Review was deliberately separated from implementing fixes.

The first research pass moved too quickly toward our own machinery. I asked for
a deeper investigation of public experience: review opportunities, revision
boundaries, leakage, historical dispositions, output contracts and evaluation.

AACR-Bench Harbor and LangChain's review-evaluation work provided useful starting
points. Their mechanisms did not settle our evidence policy. Qualified historical
reviews would initially define scoring authority; a smaller judge would match
meaning rather than conduct a new independent investigation.

The [original public entry](https://github.com/RaychevAngel/angelraychev.com/blob/802fab0f39348a19831a77a9ef192b6c5df00749/src/content/posts/training-a-code-reviewer-we-actually-use.md)
stopped at that evening's research stage. Later thematic and daily-progress drafts
existed locally but were not committed or published. This September 17 update
reconciles those drafts with subsequent records; it is not evidence that the
reorganized pages were previously live.

---

This record is synthesized from dated conversations, experiment readouts and
retained execution evidence. Reported panels are development experiments, not
independent accuracy estimates. Original results, later regrades and changes in
interpretation remain distinguishable.

[Back to the project synthesis](/training-a-code-reviewer-we-actually-use/) · [Method and system](/training-a-code-reviewer-we-actually-use/method/)

---
title: "Scaling Laws for Generative Reward Models"
description: "A study of generative judges as online training signals: reward-model and policy scaling, reasoning versus answer-only pipelines, and the gap between static judging accuracy and downstream policy optimization."
updated: 2026-10-21
---

**Angel Raychev · Nathan Lile · Rafael Rafailov**

[Read the paper (PDF)](/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=903cc32194cb) · [Read on this page](#paper-and-citation) · [Citation](#citation)

<p class="note">Revised research manuscript · 26 pages · 21 October 2026. An arXiv link will be added when available.</p>

## A good judge is not necessarily a good rewarder

A generative reward model reads an instruction and two responses, then decides
which response is better. That makes it useful as an evaluator. Put the same
model inside a training loop, however, and it has a second job: its preferences
determine how another model changes.

Those jobs expose different weaknesses. A fixed benchmark tests judgments on
an existing response distribution. Online training continually changes that
distribution. A policy can improve according to its own judge while moving
away from the behavior that a separate reference evaluator prefers.

Our study asks how to choose and train generative reward models for that
second job. We examine reward-model capacity, policy capacity, judge training,
reasoning, training duration and online-DPO regularization in creative writing.
The experiment is the entire closed loop—not just a leaderboard of judges.

<figure class="grm-diagram">
  <div class="grm-foundation"><strong>Human preferences → learned reference evaluator</strong><span>A fixed learned 32B Gold judge supplies reference preferences and labels data for smaller judges.</span></div>
  <div class="grm-branches">
    <div><strong>Answer-Only rewarders</strong><span>Supervised fine-tuning</span><small>Generate a preference verdict directly.</small></div>
    <div><strong>Thinking rewarders</strong><span>GRPO training</span><small>Generate reasoning before the verdict.</small></div>
  </div>
  <div class="grm-loop"><strong>Current policy → fresh response pairs → proxy judge → online DPO → updated policy</strong><span>Repeat as the policy's responses and the judge's effective input distribution change.</span></div>
  <div class="grm-measure"><strong>Evaluate the resulting policies</strong><span>Compare proxy-judged and Gold-judged trajectories in separately fitted Elo arenas.</span></div>
  <figcaption>Training roles and measurement roles are separate. “Gold” denotes a learned reference evaluator, not direct human adjudication of every generated response.</figcaption>
</figure>

## What we varied

The study uses Qwen3 models, human creative-writing preferences from LitBench,
and policy-generation prompts derived from WritingPrompts. A 32B evaluator
trained on human preferences supplies the reference judgments. Smaller generative
reward models learn from its preferences and then supervise online policy
optimization.

| Experimental axis | Configurations studied |
| --- | --- |
| Generative reward model | 0.6B, 1.7B, 4B, 8B and 14B parameters |
| Policy | 0.6B, 1.7B, 4B and 8B parameters |
| Rewarder pipeline | Answer-Only SFT and Thinking GRPO |
| Rewarder training | Off-the-shelf, trained and intermediate checkpoints |
| Policy optimization | Online DPO, including a sweep over regularization strength |
| Measurement | Static preference accuracy and online policy trajectories under proxy and Gold judging |

These are matched and fixed-axis sweeps, not every combination of every axis.
The comparison also changes the judge's training method: it does not isolate
the causal effect of verbalized reasoning alone.

## The evaluator–rewarder gap

Thinking judges are more accurate than Answer-Only judges on the fixed
Gold-labeled preference set across the model sizes studied.
That ranking does not reliably carry through to the policies they train.

In the shared global Gold arena, Answer-Only rewarders produce higher peak
policy Elo in **seven of eight matched configurations**. The same seven-of-eight
pattern holds when averaging each run's five highest-rated snapshots. The
smallest-policy configuration is the exception; some other gaps are small.

<figure>
  <a href="/assets/genrm/static-accuracy.png"><img src="/assets/genrm/static-accuracy.png" alt="Original paper figure comparing static preference accuracy of baseline and trained Answer-Only and Thinking generative reward models across parameter sizes." loading="lazy"></a>
  <figcaption>Static evaluator accuracy. Trained Thinking models have an advantage here. The downstream experiments test whether that advantage makes them better online rewarders.</figcaption>
</figure>

<figure>
  <a href="/assets/genrm/online-rewarder-comparison.png"><img src="/assets/genrm/online-rewarder-comparison.png" alt="Original online-training trajectory comparing Answer-Only and Thinking rewarders for a four-billion-parameter policy and fourteen-billion-parameter judge, with proxy Elo on the horizontal axis and Gold Elo on the vertical axis." loading="lazy"></a>
  <figcaption>One matched online comparison: a 4B policy trained with 14B rewarders. Points are evaluation snapshots; curves summarize the rating relationship rather than connect snapshots in time order. The axes use separately fitted proxy and Gold ratings; their diagonal is a visual reference, not a direct measure of verdict agreement.</figcaption>
</figure>

Intermediate reward-model checkpoints supply another view of the same problem.
A checkpoint that improves static judging accuracy need not be the checkpoint
that produces the best downstream policy. Selecting the rewarder is therefore
part of the policy-optimization problem, rather than a preprocessing decision
settled by validation accuracy alone.

## Capacity on both sides of the loop

Increasing reward-model size substantially improves Gold-evaluated policy
quality in the measured sweeps. For a fixed 4B policy, the Answer-Only 14B judge
outperforms its smaller counterparts—even though the reward model is much
larger than the model being trained. Thinking rewarders also benefit from scale,
but not monotonically: the 8B Thinking judge slightly exceeds the 14B Thinking
judge in the global arena.

Scaling the policy matters too. The paper studies the interaction between
the capacity that generates responses and the capacity that evaluates them,
rather than treating reward-model size as an incidental implementation setting.
Post-hoc fits summarize the two size axes and local optimization trajectories.
They describe this sweep; they are not independently validated predictions for
unmeasured model sizes.

## The training system behind the study

I implemented the custom online-DPO trainer and actor/loss path in a fork of
[verl](https://github.com/volcengine/verl), and carried out the distributed
training and evaluation program with my coauthors. The system coordinates
three distinct model roles: a trainable current policy, a frozen reference
policy for DPO likelihood ratios, and a generative pairwise judge.

Each update performs a complete online preference-learning cycle:

1. **Sample current-policy behavior.** Generate two fresh responses for each
   prompt, retaining the response tokens and prompt identity through distributed
   batching.
2. **Construct preferences.** Ask the generative judge about both response
   orderings, normalize and aggregate its verdicts, and filter zero-sum results.
   The judge has its own tokenizer, chat template and generation settings.
3. **Train on the resulting pairs.** Score chosen and rejected responses under
   the current and frozen-reference policies. Apply the sequence-level DPO
   objective with response masking, dynamic microbatching and distributed
   gradient updates.
4. **Follow the evolving policy.** Preserve evaluation generations and model
   state, then measure the resulting trajectories under both the training judge
   and the separate Gold evaluator.

Ray coordinates distributed workers, FSDP supplies sharded training and vLLM
supports generation. Independent multi-GPU training jobs made it possible to
compare judge sizes, policy sizes, training recipes and regularization settings
in parallel. The engineering work included preference-pair identity, reward
construction, distributed actor updates, evaluation, checkpointing and recovery.

For Thinking rewarders, I also implemented the response-order consistency
reward: correct judgments receive an additional signal when the two response
orderings yield correct majority decisions. This addresses a concrete failure
mode of using a language model as a pairwise preference provider.

This research predates the managed agent-learning platform described in
[my systems article](/distributed-agent-training-and-evaluation/). Both involve
the same broader concern: connecting real model behavior, trustworthy feedback
and distributed model updates. They are separate systems and research efforts.

## Interpreting the result

The strongest conclusion is operational: **evaluate a reward model through the
optimization it induces, not only through its static preference accuracy.** In
this study, more accurate fixed-distribution judges can be worse rewarders
under a specified learned reference evaluator.

That reference is not a human oracle. The result does not establish universal
Answer-Only superiority, a cross-domain law, or a causal disadvantage of
reasoning. A retained diagnostic using a different, larger learned judge is
inconclusive overall, and preference gains do not establish better stylistic
diversity. The paper reports these boundaries, the matched-setting exceptions,
and uncertainty conditional on the stored comparison data.

The broader question connects to earlier work on
[reward-model evaluation and downstream performance](https://proceedings.iclr.cc/paper_files/paper/2025/hash/93f250215e4889119807b6fac3a57aec-Abstract-Conference.html)
and [evaluation through reward overoptimization](https://aclanthology.org/2025.acl-long.649/).
Our focus is the generative-rewarder loop: practical judge-training pipelines,
rewarder/policy capacity, checkpoint selection and online-DPO dynamics.

## Paper and citation

[Download Scaling Laws for Generative Reward Models (PDF)](/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=903cc32194cb).
The manuscript contains the experimental setup, matched-condition comparisons,
readable chronological training trajectories, and an expanded empirical appendix.
It documents the Elo estimator and uncertainty procedure, and distinguishes
descriptive scaling fits from independently validated laws.
The [version record](/research/generative-reward-models/release.json) identifies
the downloadable PDF.

<iframe class="grm-pdf" src="/research/generative-reward-models/reader.html?v=903cc32194cb" title="Scaling Laws for Generative Reward Models — full manuscript" loading="lazy"><a href="/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=903cc32194cb">Open the manuscript PDF</a>.</iframe>

<p class="note">If your browser does not display the reader, <a href="/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=903cc32194cb">open or download the PDF directly</a>.</p>

<div id="citation"></div>

```bibtex
@misc{raychev2026scaling,
  title  = {Scaling Laws for Generative Reward Models},
  author = {Angel Raychev and Nathan Lile and Rafael Rafailov},
  year   = {2026},
  note   = {Research manuscript},
  url    = {https://angelraychev.com/scaling-laws-for-generative-reward-models/}
}
```

<style>
.grm-diagram { border: 1px solid var(--rule); padding: 20px; }
.grm-diagram strong, .grm-diagram span, .grm-diagram small { display: block; }
.grm-diagram strong { line-height: 1.6; }
.grm-diagram span { font-size: 13px; margin-top: 5px; }
.grm-diagram small { font-size: 12px; color: var(--dim); margin-top: 5px; }
.grm-foundation, .grm-loop, .grm-measure { border: 1px solid var(--rule); padding: 14px; }
.grm-branches { display: grid; grid-template-columns: 1fr 1fr; gap: 12px; margin: 20px 0; }
.grm-branches > div { border-left: 2px solid var(--fg); padding: 5px 12px; }
.grm-loop { background: var(--surface); }
.grm-measure { margin-top: 20px; }
.grm-pdf { width: 100%; height: 820px; border: 1px solid var(--rule); background: white; margin: 12px 0 20px; }
@media (max-width: 520px) { .grm-branches { grid-template-columns: 1fr; } .grm-diagram { padding: 12px; } }
</style>

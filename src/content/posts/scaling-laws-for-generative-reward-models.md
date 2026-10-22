---
title: "Scaling Laws for Generative Reward Models"
description: "A study of generative judges as online training signals: reward-model and policy scaling, reasoning versus answer-only pipelines, and the gap between static judging accuracy and downstream policy optimization."
image: "/assets/genrm/research-preview.png"
imageAlt: "Scaling Laws for Generative Reward Models by Angel Raychev, Nathan Lile and Rafael Rafailov. Custom distributed online DPO with generative judges."
updated: 2026-10-21
---

**Angel Raychev · Nathan Lile · Rafael Rafailov**

[Paper (PDF)](/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=8ceca55b6af6) · [Code and results](https://github.com/RaychevAngel/generative-reward-models) · [Implementation](#the-training-system-behind-the-study) · [Citation](#citation)

<p class="note">Research preprint</p>

**Static judge accuracy and downstream training quality can disagree.** In our
matched online-DPO study, Answer-Only rewarders produce higher peak and top-five
policy ratings than Thinking rewarders in seven of eight settings under the
learned reference evaluator, despite the Thinking judges' higher static accuracy.

I led the implementation of the distributed online-DPO training system and the
experimental program behind this first-author work. The release includes the
custom trainer, judge-training components, version-pinned experiment recipes
and reproducible analysis of the recorded results.

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
The central measurement is the behavior of the complete training loop.

<figure class="grm-diagram">
  <div class="grm-foundation"><strong>Reddit vote-derived labels → learned reference evaluator</strong><span>Gold is an Answer-Only 32B model trained on LitBench pairs of human-written stories. It supplies reference judgments and labels data for smaller judges.</span></div>
  <div class="grm-branches">
    <div><strong>Answer-Only rewarders</strong><span>Supervised fine-tuning</span><small>Generate a preference verdict directly.</small></div>
    <div><strong>Thinking rewarders</strong><span>GRPO training</span><small>Generate reasoning before the verdict.</small></div>
  </div>
  <div class="grm-loop"><strong>Current policy → fresh response pairs → proxy judge → online DPO → updated policy</strong><span>Repeat as the policy's responses and the judge's effective input distribution change.</span></div>
  <div class="grm-measure"><strong>Evaluate the resulting policies</strong><span>Compare proxy-judged and Gold-judged trajectories in separately fitted Elo arenas.</span></div>
  <figcaption>The study separates the judge supplying online training preferences from the learned Gold reference used to measure the resulting policies. Reddit votes provide implicit source labels, not explicit pairwise human annotations.</figcaption>
</figure>

## What we varied

The study uses Qwen3 models, LitBench's curated, vote-derived preferences over
human-written Reddit stories, and policy-training prompts derived from
WritingPrompts. A fine-tuned 32B evaluator supplies reference judgments. Smaller
generative reward models learn from its labels and then supervise online policy
optimization. Gold, proxy and policy validation reuse the same 1,000 source
pair records and their prompts; the paper spells out the distinct labels and
response references.

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
  <a href="/assets/genrm/matched-trajectories.png"><img src="/assets/genrm/matched-trajectories.png" alt="Four chronological policy-training comparisons, including the smallest-policy exception, in a shared Gold evaluator arena. Answer-Only and Thinking rewarders are compared at matched model sizes." loading="lazy"></a>
  <figcaption>Recorded policy-training trajectories in one shared Gold arena. The selection includes the smallest-policy exception as well as larger-policy and larger-rewarder settings. Lines connect observed snapshots; they are not fitted curves or averages across independent training seeds. The paper contains all eight matched conditions.</figcaption>
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
Post-hoc fits summarize associations with policy and reward-model size. They
describe the measured grid; they are not independently validated predictions
for unmeasured model sizes.

<figure>
  <a href="/assets/genrm/capacity-allocation.png"><img src="/assets/genrm/capacity-allocation.png" alt="Rewarder-size and policy-size sweeps plotted separately, with Answer-Only and Thinking conditions in the same Gold arena." loading="lazy"></a>
  <figcaption>Capacity on both sides of the loop. Left: vary the judge while holding the policy at 4B. Right: vary the policy while holding the judge at 4B. Each point averages that run's five highest Gold-rated snapshots. These are observed parameter-size sweeps, not compute-normalized optima or predictions for unmeasured sizes.</figcaption>
</figure>

## The training system behind the study

I implemented the [custom online-DPO trainer and actor/loss path](https://github.com/RaychevAngel/generative-reward-models/blob/main/docs/implementation.md) in a fork of
[verl](https://github.com/volcengine/verl), and carried out the distributed
training and evaluation program with my coauthors. The system coordinates
three distinct model roles: a trainable current policy, a frozen reference
policy for DPO likelihood ratios, and a generative pairwise judge.

verl provided the distributed foundation. The custom work connected fresh
policy generations to pairwise judge preferences and online DPO updates,
without requiring a precomputed preference dataset between training rounds.
That made the judge itself an experimental component of the learning loop.

<figure>
  <a href="/assets/genrm/online-dpo-system.svg"><img src="/assets/genrm/online-dpo-system.svg" alt="A prompt feeds current-policy generation; a generative judge orders fresh responses; current and frozen reference policy log probabilities feed a masked DPO loss; distributed updates refresh the current policy. A separate Gold evaluator measures saved policy outputs." loading="lazy"></a>
  <figcaption>The custom online-DPO loop. The frozen DPO reference policy supplies likelihoods, the rewarder supplies preferences, and Gold supplies a separate evaluation signal. These are different model roles even when some use related backbones.</figcaption>
</figure>

Each update performs an online preference-learning cycle:

1. **Sample current-policy behavior.** Generate two fresh responses for each
   prompt, retaining the response tokens and prompt identity through distributed
   batching.
2. **Construct preferences.** Ask the generative judge about both response
   orderings, normalize and aggregate its verdicts, and filter zero-sum results.
   A verdict parsed as invalid contributes zero, so a surviving pair need not have two
   valid votes. The judge has its own tokenizer, chat template and generation settings.
3. **Train on the resulting pairs.** Score chosen and rejected responses under
   the current and frozen-reference policies. Apply the sequence-level DPO
   objective with response masking, dynamic microbatching and distributed
   gradient updates.

Periodic validation and checkpointing track the evolving policy. In-loop
validation uses the configured proxy judge; a separate evaluation and analysis
path measures saved policy outputs under Gold. This keeps the training signal
distinct from the reference used to compare the resulting policies.

Ray coordinates distributed workers, FSDP supplies sharded training and vLLM
supports generation. Independent multi-GPU training jobs made it possible to
compare judge sizes, policy sizes, training recipes and regularization settings
in parallel. The engineering work included preference-pair identity, reward
construction, distributed actor updates, evaluation and sharded checkpointing.

This research predates the managed agent-learning platform described in
[my systems article](/distributed-agent-training-and-evaluation/). Both involve
the same broader concern: connecting real model behavior, trustworthy feedback
and distributed model updates. They are separate systems and research efforts.

## Code and reproducibility

The [public research repository](https://github.com/RaychevAngel/generative-reward-models)
connects the paper to the implementation and numerical evidence:

- **Training implementation:** the historical verl-based online-DPO trainer,
  distributed actor/loss code, judge integration and the source map explaining
  the custom components.
- **Experiment recipes:** Gold SFT, proxy SFT/GRPO and online-DPO configurations,
  with model/data requirements and the distinction between historical settings
  and a newly validated training environment.
- **Results and analysis:** retained numerical tables, figure generators and
  provenance linking the plots to their inputs.
- **Paper:** the matching manuscript sources and build instructions.

An [earlier exploratory archive](https://github.com/RaychevAngel/generative-reward-models/tree/main/results/historical-explorations)
preserves original data-recipe and distillation comparisons, separately from
the paper's matched study.

The release makes [CPU analysis reproducible without model calls](https://github.com/RaychevAngel/generative-reward-models/blob/main/docs/reproduction.md). Repeating the
original training additionally requires suitable GPUs and access to the model
and data artifacts; it is not presented as a freshly verified one-command GPU
reproduction. The repository documents those requirements separately and exposes
the [conditional Elo uncertainty method](https://github.com/RaychevAngel/generative-reward-models/blob/main/results/receipts/README.md#inspectable-method-source)
alongside the retained comparison results.

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

[Download Scaling Laws for Generative Reward Models (PDF)](/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=8ceca55b6af6).
The [versioned research release](https://github.com/RaychevAngel/generative-reward-models/releases/tag/v2026.10.21)
also provides the matching TeX source package.
The manuscript contains the experimental setup, matched-condition comparisons,
readable chronological training trajectories, and an expanded empirical appendix.
It documents the Elo estimator and uncertainty procedure, and distinguishes
descriptive scaling fits from independently validated laws.
The [version record](/research/generative-reward-models/release.json) identifies
the downloadable PDF.
The [paper landing page](/research/generative-reward-models/) provides the exact
abstract and machine-readable citation metadata.

<iframe class="grm-pdf" src="/research/generative-reward-models/reader.html?v=8ceca55b6af6" title="Scaling Laws for Generative Reward Models — full manuscript" loading="lazy"><a href="/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=8ceca55b6af6">Open the manuscript PDF</a>.</iframe>

<p class="note">If your browser does not display the reader, <a href="/research/generative-reward-models/scaling-laws-for-generative-reward-models.pdf?v=8ceca55b6af6">open or download the PDF directly</a>.</p>

<div id="citation"></div>

```bibtex
@misc{raychev2026scaling,
  title  = {Scaling Laws for Generative Reward Models},
  author = {Angel Raychev and Nathan Lile and Rafael Rafailov},
  year   = {2026},
  note   = {Preprint},
  url    = {https://angelraychev.com/research/generative-reward-models/}
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

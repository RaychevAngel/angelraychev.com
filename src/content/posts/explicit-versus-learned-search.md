---
title: "Explicit versus learned search"
description: "Neural-guided tree search, iterative policy and value training, and learning to search from complete traversals. A technical retrospective of my 2025 Stanford research projects."
updated: 2026-10-23
---

*Neural-guided tree search and search-trace learning.*

[Technical report (PDF)](/research/explicit-learned-search/explicit-versus-learned-search.pdf) · [Code](https://github.com/RaychevAngel/classical_vs_contextual_search) · [Original Stanford report](https://cs224r.stanford.edu/spring_2025/projects/pdfs/CS_224R_Final_Report__3_%20%281%29.pdf)

Giving a language model more computation does not specify how it should use it. An external controller can maintain a tree, revisit alternatives and ask learned models where to search next. Alternatively, the model can learn to perform the search in its own generated sequence: proposing branches, evaluating their consequences and returning to earlier decisions.

In 2025, I built research systems for both approaches. The work began as a joint Stanford CS224N project with Yalcin Tur and Mihajlo Stojkovic and developed into my CS224R implementation of batched neural-guided Monte Carlo Tree Search, iterative policy/value training, and Stream-of-Search learning. I was the lead developer of the later system and conducted its experiments.

The central connection was not just a comparison between two inference algorithms. **The external search system also became a teacher.** A single tree supplied successful paths for the policy, intermediate return targets for the value model, and whole traversals for a model learning to search in language.

This article and its companion report explain that system and the choices behind it. They are a technical retrospective of the existing work, not a new experimental study.

Explore: [search architecture](#where-the-search-lives) · [batched execution](#making-search-a-batched-workload) · [learning signals](#one-tree-three-learning-products) · [artifacts](#code-report-and-released-models).

## Where the search lives

“Explicit versus learned” is useful shorthand, but both systems contain learned components. The external controller uses a neural policy and a separately trained value model. The internalized version learns a distribution over textual search procedures.

The operational distinction is **who manages the branches and where the state is stored**.

<figure class="search-figure" aria-labelledby="control-caption">
  <div class="control-comparison">
    <section><span class="diagram-label">Externally managed</span><strong>Tree in program memory</strong><p>Controller selects a node → policy proposes children → value model scores them → controller updates the tree.</p><span class="diagram-foot">Branch identity, visits and returns are explicit data structures.</span></section>
    <section><span class="diagram-label">Internalized</span><strong>Traversal in model context</strong><p>Model generates a search stream containing branches, parent references and a selected final expression.</p><span class="diagram-foot">Search behavior is learned; the generated context carries the traversal.</span></section>
  </div>
  <figcaption id="control-caption">Two locations for search control. The external system still relies on learned proposals and values; the search-in-language system still needs a representation of branch structure.</figcaption>
</figure>

The external controller can return to a stored node without regenerating the entire route to it. A search-in-language model can condition its next decision on the preceding traversal, including alternatives that did not become the final answer. These are different computational interfaces, not a division between brute force and intelligence.

The work follows two complementary lines: [TS-LLM](https://arxiv.org/abs/2309.17179), which couples learned policies and values to tree search, and [Stream of Search](https://arxiv.org/abs/2404.03683), which represents exploration as a sequence that a language model can learn.

## A task with an inspectable search structure

The later system used a generalized arithmetic game. Given input integers and a target, construct an expression using every input occurrence exactly once, the four basic arithmetic operations and parentheses. A repeated number is a repeated resource: two threes may be used twice, but one three may not.

The task gives the system three useful objects: a language representation of a partial state, multiple alternative next steps, and an independently checkable final expression. The policy emits arithmetic steps and the remaining numbers. These intermediate descriptions are model-generated text; the final-expression checker, rather than a symbolic transition engine validating every intermediate sentence, supplies the terminal training labels.

One question in the original report asks the model to use $3,3,5,12$ to make $51$. There are distinct routes:

<figure class="search-figure" aria-labelledby="branch-caption">
  <div class="branch-question">Use 3, 3, 5, 12 to make 51</div>
  <div class="branch-paths">
    <div><span class="diagram-label">Branch A</span><code>3 × 12 = 36</code><code>3 × 5 = 15</code><code>36 + 15 = 51</code></div>
    <div><span class="diagram-label">Branch B</span><code>12 × 5 = 60</code><code>3 × 3 = 9</code><code>60 − 9 = 51</code></div>
  </div>
  <figcaption id="branch-caption">An explanatory reconstruction of two branches from the report's worked example, not a new model run. The final expressions use the same four input occurrences through different intermediate states.</figcaption>
</figure>

Final-answer-only supervision does not explicitly show the explored alternatives or how the search returned to earlier states. That distinction motivated exporting more than accepted solutions.

## A custom neural-guided search engine

For each question, the implementation builds a tree of partial textual trajectories. A node stores its parent and children, visit count $N$, running backed-up value $Q$, an initial learned value estimate and observed terminal labels.

Selection trades off the current value estimate against exploration. The implemented score for a child $u$ of node $s$ is

$$
U(s,u)=Q(u)+c\,\frac{\sqrt{N(s)}}{N(u)+1}.
$$

At a leaf, the policy samples candidate next steps. Duplicate candidates are removed, and the value model scores the resulting partial trajectories. Their estimates initialize the new nodes. Later visits back up values through the ancestors, updating running means and visit counts.

The training and evaluation paths share this search machinery but use different terminal feedback. During data generation, the expression checker provides a terminal success label. During evaluation, learned values guide search and final selection; the checker scores the selected final expression afterward. Finding a correct expression somewhere in a tree and successfully selecting it are different outcomes.

The repository's final-path selection follows the child with greatest backed-up $Q$ at each step. That is separate from the exploration score above. Keeping the exploration rule, the final-selection rule and the training labels explicit is essential to understanding what the system does.

## Making search a batched workload

A single search tree alternates between dependent decisions. Serving one request at a time would turn that dependence into GPU idle time. I reworked the engine around a **forest of independently advancing trees**.

Each tree submits a request containing its question and partial trajectory, then awaits a future. A shared queue collects requests across trees. The serving layer batches policy generation, gathers the resulting child states, batches their value evaluations and resolves the waiting trees' requests. A tree can continue as soon as its own expansion returns.

<figure class="search-figure" aria-labelledby="forest-caption">
  <div class="forest-sources"><span>Tree A</span><span>Tree B</span><span>Tree C</span><span>…</span></div>
  <div class="forest-step"><span class="diagram-label">Shared queue</span><strong>Questions + partial trajectories + waiting futures</strong></div>
  <div class="forest-services"><div><span class="diagram-label">Policy service</span><strong>Batched next-step proposals</strong></div><span class="flow-connector" aria-hidden="true">→</span><div><span class="diagram-label">Value service</span><strong>Batched child-state scores</strong></div></div>
  <div class="forest-step"><span class="diagram-label">Route results</span><strong>Resolve each future → resume its tree</strong></div>
  <figcaption id="forest-caption">Batch across independent problems while preserving each tree's sequential dependencies. This is the architecture implemented in the asynchronous forest, not a claim that branches within one tree are independent.</figcaption>
</figure>

This separates three concerns: the search controller manages state, the serving layer performs neural inference, and the generator or evaluator decides how to consume the completed tree. It also makes policy and value models independently configurable rather than treating them as one inseparable model.

## One tree, three learning products

The tree is useful beyond the answer it returns. The generator extracts three distinct forms of supervision, each with a different purpose.

<figure class="search-figure" aria-labelledby="products-caption">
  <div class="tree-source"><span class="diagram-label">Shared source</span><strong>Search tree + terminal checks + backed-up returns</strong></div>
  <div class="learning-products">
    <section><span class="diagram-label">Policy</span><strong>Accepted trajectories</strong><p>Learn to produce successful solution paths.</p></section>
    <section><span class="diagram-label">Value</span><strong>Partial-state targets</strong><p>Learn which prefixes lead toward successful continuations.</p></section>
    <section><span class="diagram-label">Search in language</span><strong>Whole traversals</strong><p>Learn exploration, branch references and answer selection.</p></section>
  </div>
  <figcaption id="products-caption">The distinction between teaching an answer, teaching a state evaluator and teaching the search procedure. These products come from the same search process but are not interchangeable datasets.</figcaption>
</figure>

### Policy improvement

An initial synthetic successful-solution dataset first taught the policy the arithmetic response format. Subsequent iterations used newly generated search trajectories: accepted terminal paths become prompt/completion examples for supervised fine-tuning. In conceptual form, the policy objective is

$$
\mathcal{L}_{\mathrm{policy}}
=-\mathbb{E}_{(q,\tau)\sim\mathcal{D}^{+}}
\log\pi_\theta(\tau\mid q).
$$

After training, the updated policy generates the next round of search data. The loop is search → extract successful trajectories → train → search again. The dataset therefore evolves with the policy rather than remaining a fixed set of demonstrations.

### A learned value at intermediate steps

The value model is trained from both successful and unsuccessful terminal trajectories. Its targets include the intermediate states along those trajectories. Where terminal outcomes have been backed up through a state, their mean supplies a soft target; the generator has a terminal-label fallback where such observations are absent. These are empirical targets under the sampled search, not exact optimal values of the arithmetic state.

In the later implementation, a causal language model supplies the value through one designated vocabulary logit. Its sigmoid is the scalar estimate. Training aligns value labels to newline-token positions marking the question and successive steps, masks every other position and padding, and applies binary cross-entropy at the labelled positions:

$$
\mathcal{L}_{\mathrm{value}}
=\frac{1}{|J|}\sum_{j\in J}
\operatorname{BCEWithLogits}(\ell_\phi(s_j),\widehat y_j).
$$

Here $J$ denotes the labelled step positions. The [custom trainer](https://github.com/RaychevAngel/classical_vs_contextual_search/blob/1a7fda10617d34ccd3a87c825cba71e4429de91a/train/value_trainer.py) checks the alignment between newline positions and supplied labels before computing the loss. This gives the controller a trainable evaluator for partial progress, not just a reward attached to the final answer.

## Teaching the traversal, not only the winning path

For search-in-language training, the generator records nodes in first-visit order and serializes their relationships. A nonterminal entry names its node and parent. A terminal entry can include its ancestor chain. The sequence is wrapped in thought markers and followed by a separately marked selected accepted expression.

The representation makes a crucial distinction: **two consecutive lines in the stream need not be consecutive steps on one solution path**. Parent references tell the model where each explored state belongs.

An abbreviated illustration of the format is:

```text
Q | Use 3, 3, 5, 12 to make 51.
<START_THOUGHT>
N1->Q | 3*12=36 Left: 3, 5, 36
N2->Q | 12*5=60 Left: 3, 3, 60
N3->N1 | 3*5=15 Left: 15, 36
N4->N2 | 3*3=9 Left: 9, 60
N5->N2 | 60-3=57 Left: 3, 57
N6->N5 | 57-3=54 Left: 54
N7->N6->N5->N2->Q | 12*5-3-3=54
...
<END_THOUGHT>
<START_ANSWER>
3*12+3*5=51
<END_ANSWER>
```

This is an explanatory excerpt, not a complete training record. The route ending at $54$ is unsuccessful, yet belongs in the traversal that teaches the search process. The full records include the remaining visited states and terminal references.

The model is initialized from a pretrained checkpoint and fine-tuned on these traversals. “Learning search” here does not mean pretraining a new foundation model from nothing. It means teaching a model to reproduce a search process and emit a final answer within one generated sequence.

The project also implements a STaR-style rejection/self-training path: generate attempts, keep successful completions and use them for further fine-tuning. This follows the broader [STaR](https://arxiv.org/abs/2203.14465) idea of learning from successful reasoning, without identifying every detail of this implementation with the original paper's procedure.

## Two stages of the project

The original reports describe related but distinct systems.

| Stage | Main question | Implementation emphasis |
| --- | --- | --- |
| CS224N | How do policy capacity, value capacity and inference-time search interact? | SmolLM2 policy/value combinations, a custom value head, iterative search-generated training and search-budget sweeps. |
| CS224R | What changes when the search procedure is learned in language? | Reworked asynchronous MCTS, Qwen-based policy/value training, step-aligned value supervision and traversal-trained search models. |

The early project was a team effort. My contributions included MCTS implementation, evaluation and writing; Yalcin and Mihajlo contributed policy/value training, data generation and infrastructure. I subsequently led the later implementation, repeatedly reworked the search engine, added the search-in-language pipeline and ran its experiments. The [CS224R contribution statement](https://cs224r.stanford.edu/spring_2025/projects/pdfs/CS_224R_Final_Report__3_%20%281%29.pdf) records these roles.

The original studies investigated changes in policy/value capacity, repeated training rounds, branching and expansion budgets, traversal size and rejection-based refinement. They provide the experimental context for the system. This retrospective does not turn their exploratory comparisons into a new compute-matched benchmark or an asymptotic separation between reasoning methods.

## What a meaningful comparison has to measure

The choice is not determined by adding up model parameters. An external system pays for policy calls, value calls, repeated prefix processing and controller overhead. A search-in-language model pays for generating and processing its traversal context. The lengths and shapes of those workloads differ.

There is also a training-time investment: an internalized search model inherits computation already spent producing its teacher's traversals. The cost can be worthwhile when amortized over subsequent use. A useful accounting therefore separates the one-time construction cost from the recurring solve cost, rather than counting only the final model invocation.

Three distinctions are particularly important:

- **Discovery versus selection.** Did any explored branch contain a correct answer, and did the system actually return it?
- **A fixed method's budget curve versus different trained methods.** More inference for one frozen model is a different comparison from training separate models on differently sized traversals.
- **Efficiency versus generalization.** Better use of a finite budget does not by itself show transfer to longer problems, different branching structures or new task families.

These are research questions, not reasons to prefer one architecture universally. An external tree offers explicit state management and replaceable control rules. A traversal-trained model offers learned control conditioned on its preceding search. Hybrids can combine learned decisions with external state. [External and internal planning research](https://arxiv.org/abs/2412.12119) provides a broader setting for this distinction.

## Code, report and released models

The [companion repository](https://github.com/RaychevAngel/classical_vs_contextual_search) contains the search engine, policy/value serving, generators, trainers and evaluation paths. Its documentation separates the historical implementation from the maintenance corrections accompanying this retrospective. CPU regression checks exercise arithmetic verification and evaluation accounting without downloading models or running training. GPU training and generation remain separate workflows with explicit environment, data and model prerequisites.

Selected released artifacts include a [policy checkpoint](https://huggingface.co/AngelRaychev/0.5B-policy-iteration_6), a [step-value checkpoint](https://huggingface.co/AngelRaychev/1.5B-value-iteration_2) and a [traversal-trained checkpoint](https://huggingface.co/AngelRaychev/0.5B-sos-iteration_1_b21_e42_epochs16). These are examples of the project's different learning products, not a prescribed matched comparison set.

The [new technical report](/research/explicit-learned-search/explicit-versus-learned-search.pdf) provides a self-contained description of the architecture, learning objectives and artifact boundaries. Its [typesetting source](/research/explicit-learned-search/report-source.zip) and [version record](/research/explicit-learned-search/release.json) accompany the PDF. The untouched original CS224R report remains available through Stanford.

This work connects to the systems I later built for [distributed agent training and evaluation](/distributed-agent-training-and-evaluation/) and to [learning from hindsight](/scalable-meta-learning-from-hindsight/). In each case, the question is not just how to obtain a useful outcome once, but how to convert the computation behind it into a reusable improvement process.

## References

- Feng et al. [AlphaZero-like Tree-Search Can Guide Large Language Model Decoding and Training](https://arxiv.org/abs/2309.17179), 2023/2024.
- Gandhi et al. [Stream of Search: Learning to Search in Language](https://arxiv.org/abs/2404.03683), 2024.
- Zelikman et al. [STaR: Bootstrapping Reasoning With Reasoning](https://arxiv.org/abs/2203.14465), 2022.
- Schultz et al. [Mastering Board Games by External and Internal Planning with Language Models](https://arxiv.org/abs/2412.12119), 2024/2025.
- Raychev, Tur and Stojkovic. [In-context Search: Efficiency Boost or Fundamentally New Capability?](https://cs224r.stanford.edu/spring_2025/projects/pdfs/CS_224R_Final_Report__3_%20%281%29.pdf), Stanford CS224R, 2025. Historical project report.

<style>
.search-figure{border-top:1px solid var(--rule);border-bottom:1px solid var(--rule);padding:22px 0}
.search-figure p{font-size:13px;line-height:1.7;margin:10px 0 12px}
.search-figure strong{display:block;font-size:13px;line-height:1.6}
.diagram-label{display:block;color:var(--dim);font-size:11px;line-height:1.5;margin-bottom:7px;text-transform:uppercase;letter-spacing:.035em}
.diagram-foot{display:block;font-size:12px;line-height:1.65;color:var(--dim)}
.control-comparison,.branch-paths{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:24px}
.control-comparison section+section,.branch-paths>div+div{border-left:1px solid var(--rule);padding-left:24px}
.branch-question,.tree-source{border:1px solid var(--rule);padding:14px;text-align:center;margin-bottom:18px;font-size:13px}
.branch-paths code{display:block;font-size:13px;line-height:1.85;white-space:nowrap}
.forest-sources{display:flex;justify-content:space-between;gap:12px;margin-bottom:14px;font-size:12px}
.forest-sources span{border:1px solid var(--rule);padding:7px 12px;flex:1;text-align:center}
.forest-step{padding:14px;border:1px solid var(--rule);text-align:center}
.forest-services{display:grid;grid-template-columns:1fr auto 1fr;gap:14px;align-items:center;padding:18px 0}
.forest-services>div{padding:12px;border:1px solid var(--rule)}
.flow-connector{font-size:18px}
.learning-products{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:14px}
.learning-products section{border:1px solid var(--rule);padding:12px}
.learning-products p{margin-bottom:0;font-size:12px}
@media(max-width:540px){.control-comparison,.branch-paths,.learning-products{grid-template-columns:1fr;gap:18px}.control-comparison section+section,.branch-paths>div+div{border-left:0;border-top:1px solid var(--rule);padding-left:0;padding-top:18px}.forest-sources{gap:6px}.forest-sources span{padding:6px 3px}.forest-services{grid-template-columns:1fr;gap:10px}.flow-connector{transform:rotate(90deg);text-align:center}}
</style>

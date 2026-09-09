---
title: "Four Levers and a Trap"
description: "You can change your policy, the parameters it is read from, the rule that updates them, and the body it runs on. The order you touch them in is a theorem, and knowing about the trap is what walks you into it."
updated: 2026-09-09
---

## What this is

The [previous piece](/the-optimization-nobody-is-running/) specified the objective. This one
is about what you can actually change, in what order, and what happens when the thing doing
the changing is the same thing being changed.

Here is where it lands, so you can read the argument knowing the destination.

You have four levers over yourself, and they are not the same kind of object. The rule that
converts your experience into change is one of them, it is real, and it is currently the
most defensible claim in this whole line of thinking. The order matters and is not a
preference: fixing the objective before touching anything else is the precondition under
which touching anything else is safe, and that is a theorem with a number. Learning without
acting works, is worth roughly two-thirds of doing, and decays with a three-week half-life.
Choosing what to attempt next beats optimizing within an attempt by an exponential margin.

And then the part that goes the wrong way. There is a move available to any agent like this
— cheat your own sensors — and the intuition that understanding it protects you is exactly
backwards. In the canonical proof, knowing about it is the trigger.

## Four levers, and they are four different types

Write the agent as a map from history to actions. Then:

**The policy** — what you do next.
**The parameters** — what the policy is read out of. Your weights, your brain.
**The update rule** — how a rollout changes those parameters.
**The harness** — the body. The action set, the sensor channel, the dynamics.

The first two are not two objects. The policy is the invariant thing and the parameters are
a coordinate chart on it: two different parameter settings can be the same policy, and the
same step in parameter space is a different step in policy space depending on the chart.
That is exactly the content of the natural gradient (Amari 1998; Kakade 2001), which is
invariant under smooth reparameterization. So you cannot move the policy without moving the
parameters. They are a manifold and a chart, not two levers.

The fourth is the sharpest, and it is a **type** distinction rather than a difference of
degree. The first three move you around on a fixed objective landscape. Changing your body —
your available actions, your sensors, your dynamics — changes the landscape. Picking up a
tool enlarges the action set. A new sensor enlarges the observation channel. That is not a
better position in the same problem; it is a different problem.

One caution that cannot be designed away. The split between "what I do" and "how I update"
has a formal home — Abel and colleagues' definition of a learning rule as a map from history
to base agents (NeurIPS 2023) — but the same paper proves that for any agent there exist
*infinitely many* ways to read it as a policy-plus-search, with none canonical. So the four
levers are a basis, not a partition. Choosing one is what a good self-model *is*; claiming
it is intrinsic is a mistake.

## The update rule is real, and the frontier agrees

The claim that how a rollout changes you is itself modifiable and learnable is the most
defensible thing here, not the wildest.

It is a research program with results. Meta-gradient methods learn the return itself —
the discount, the bootstrapping parameter — online during training (Xu, van Hasselt & Silver,
NeurIPS 2018). Learned Policy Gradient meta-learns the *entire* update rule including what
to predict, discovering its own alternative to the value function, trained on toy gridworlds
and generalizing to Atari (Oh et al., NeurIPS 2020). And as of last year a machine-discovered
update rule beats every human-designed rule on the standard benchmark and reaches the same
final performance as the leading hand-built system with roughly 40% less compute (Nature 2025).

Forty years of human-designed learning rules, beaten by a discovered one. If you want a
reason to take the third lever seriously, that is it.

Two corrections to the enthusiasm. MAML — the method usually cited for this — is **not** an
example: it meta-learns an initialization while the update stays ordinary gradient descent,
and the follow-up showed even the adaptation is largely feature reuse, with the inner loop
removable at no performance cost (Raghu et al., ICLR 2020). It is the second lever wearing
the third one's clothes. And learned optimizers meta-overfit: they generalize within the
distribution of problems they were trained on and fall off a cliff outside it, with the
largest one breaking down past roughly 600M-parameter tasks. The rule you learn is fitted to
the lives you learned it from.

## The order is a theorem

Fix the objective first, then change the policy. That sounds like methodological taste. It
is not.

Everitt, Filan, Daswani and Hutter (AGI 2016) split self-modifying agents by how they
evaluate a proposed change to themselves. A **hedonistic** agent scores the future using the
utility function it will *have* after modifying. A **realistic** agent scores it using the
utility function it has *now*. Their Theorem 14: the hedonistic agent finds it optimal to
rewrite its reward to return the maximum always. Their Theorem 16: the realistic agent makes
only safe modifications. The self-modification possibility is harmless **if and only if** the
agent anticipates the consequences *and* evaluates them against its current objective.

So the ordering is the precondition under which the other three levers are safe to touch at
all. Not first because it is tidier. First because the theorem says the alternative provably
installs the constant-maximum reward — which is the formal signature of addiction.

## Learning without acting: two-thirds, with a three-week half-life

You change by experiencing, not only by doing. This is correct, it is not poetic, and it has
four names: off-policy learning, offline RL, imitation from observation, and background
planning.

The strong version — that you can update with no sensory input at all, purely by thinking —
is also correct. It is the entire architecture of an agent that learned to mine diamonds in
Minecraft from scratch by training inside its own imagined model (Nature 2025). It has a
biological homolog: rats replay trajectories they have never actually run, and silencing that
replay produces a lasting learning deficit.

The magnitude is real and it is worth having exactly. Twelve weeks of *purely imagined*
maximal contractions produced a 35% strength gain, against 53% for real lifting and roughly
nothing for controls (Ranganathan et al. 2004). Mental practice meta-analyses put imagined
practice at about two-thirds the effect of physical practice.

Now the honest corrections, because this literature was revised.

The 1994 meta-analysis gives mental practice d = 0.527. The 2020 replication across 37
studies gives r = 0.131. **The effect roughly halved.** Quoting only the older number is
cherry-picking; quoting both still supports the claim.

The effect has a half-life. It is reduced by about half at two weeks and is under 0.1 by
three weeks. Imagination without grounding drifts.

And there is an optimal dose: about 21 minutes per session, with a *significant negative*
relationship between session length and effect. That is remarkable, because it is the same
result that model-based RL derives from theory — imagined rollouts should be short, because
distribution-shift error decays with rollout length while model error accumulates linearly
in it, so the optimal number of imagined steps is small and strictly positive. A 1994 human
meta-analysis and a 2019 RL bound found the same shape. Long imagined rollouts get exploited
by the policy. **Rumination is model exploitation, and it has a citation.**

Four things break the strong form, and they all say the same thing.

**Coverage.** Every offline guarantee is gated by how well your existing data covers the
policy you want to become. Nothing you read and nothing you imagine improves that. Only
acting does. And the ceiling is hard: batch RL has exponential lower bounds even given a
perfect model, exact rewards, and the best possible data distribution.

**Missing actions.** Reading a study is learning from *observation*, not from demonstration.
You get states, not actions. A paper tells you where to be and never what to do at your own
state. The measured version of this is sharp: watching gives d = 0.77 for movement *dynamics*
and d = 0.17 for movement *outcome* — a four-and-a-half-fold gap. Watching transfers the
form, not the result.

**Compounding error.** Pure imitation gives a value gap growing quadratically in horizon
length. The fix requires acting and being corrected on your own state distribution.

**And the deadly triad, which is the best diagnosis available here.** A person reading a
study assembles all three legs at once: function approximation, bootstrapping, and off-policy
data. The theory's prediction is not that learning stops. It is that **value estimates
inflate**, sometimes without bound. That is a theorem-backed account of reading
self-improvement literature and feeling improved.

The cleanest way to hold all of this: reading is a gradient step held in RAM. Doing is a
gradient step written to disk. And the mechanism is not metaphorical — a single attention
layer can implement exactly one step of gradient descent (von Oswald et al., ICML 2023), so
in-context updating really is a gradient step, just one that lives in activations and
evaporates with the context.

## Choosing what to attempt is the optimization

Standard reinforcement learning hands the agent a task distribution and samples from it. The
agent optimizes *within* an episode it did not choose. A person picks what the episode is.

That difference has a name — the adaptivity gap — and as of this year it has an exponential
separation in exactly the analogous setting. For reasoning post-training, non-adaptive
selection needs a number of demonstrations scaling as 1/ε in target accuracy; adaptive
curriculum selection needs polylog(1/ε). The same separation holds in active learning:
choosing your query costs Θ(log 1/ε) labels against Θ(1/ε) for passive sampling.

The empirical version is categorical rather than marginal. In the POET ablation, the same
optimizer with the same compute pointed directly at a hard environment scores 13.6–39.6
against a solve threshold of 230; routed through a self-generated sequence of environments,
it clears 230. Nothing about the inner learner changed. The task sequence was the entire
difference.

And this closes the loop with the previous section. The formal content of "you have to
actually do things" is not that experience is magic. It is that **you have to be able to
choose your next query** — that is the one thing reading cannot buy you.

## The trap

Everything you have access to is sensor information. So there is a move available: rather
than improve, corrupt the channel. Delete the memory, enter the simulation, arrange to
receive the percepts of a life you are not living.

This fear is not paranoia. It is the central negative result of the field, and it is worse
than the intuitive version. Ring and Orseau (2011) construct an environment containing a
"delusion box" the agent can program, and show that the reinforcement-learning agent takes
it, the *goal-seeking* agent takes it, and the prediction-seeking agent takes it. Three of
four types. Having a goal rather than a reward does not save you.

Two further results from that paper deserve to be better known. A mortal reward-seeking agent
with a delusion box available is *equivalent* to a pure survival agent. And the survival agent
stops exploring — it falls into a simple class of behaviour and never escapes it. **That is
the vegetable, and it arrives from mortality plus reward alone, with no delusion required.**

The exception is the fourth type. The knowledge-seeking agent is the unique one that does not
take the box, because no program it can install lowers its surprise below what exploring the
real environment offers — for that agent, exploring *is* exploiting. It is also the unique one
that cannot be reduced to a survival agent. The two-part goal of staying alive *and* continuing
to become more has a formal home, and curiosity is what makes the two halves compatible rather
than competing.

## Knowing about the trap is what walks you into it

The natural defense is perspicacity: see the whole situation clearly and you will not fall for
it. I expected the literature to say this was weak. It says something harsher.

**In the canonical proof, knowledge is the trigger.** The argument for the first result turns
on the agent knowing, with sufficiently high probability, that the box exists — at which point
it computes that programming the box beats not programming it. The precondition for
wireheading in the theorem is knowing the shortcut is there.

**The omniscient variants still take it.** Each agent in that paper has a twin with full
knowledge of the environment, and the arguments are stated for those twins. Full knowledge of
the situation, including the box, including what it does, including that it is a box. Still
taken.

**And the most self-reflective agent ever formalized still takes it.** A footnote in the same
section notes that using a Gödel machine — an agent that rewrites itself only on a formal
proof that the rewrite improves expected utility — would not prevent it from using the box.

The structural reason is that incentives are not epistemic objects. The graphical criteria for
when an objective creates an instrumental incentive are properties of the objective and the
causal structure; beliefs do not appear in them. Understanding does not delete an edge from
the graph. It makes you better at traversing the edges already there. Which means
meta-knowledge is a **capability multiplier on the incentive**, and capability is on the wrong
side of this one.

The human numbers agree. The most-studied attempt to prevent a behaviour by explaining its
mechanism — D.A.R.E. — returns d = 0.023, confidence interval spanning zero. And the review
literature on debiasing is blunt that teaching people about cognitive biases has proven
insufficient to reduce them.

There is a place where the intuition is vindicated, and it is precise. The
if-and-only-if above has two conjuncts: anticipating the consequences of self-modification,
**and** evaluating them with your current objective. Understanding is the first conjunct. The
hedonistic agent of Theorem 14 anticipates perfectly well and wireheads anyway. So
**meta-knowledge is necessary and not sufficient, and the other half is doing the work.**

And there is a reason understanding is *structurally* unable to help with the specific case.
The delusion box does not require modifying your utility function. Your current, unmodified,
entirely endorsed objective genuinely assigns maximum value to the corrupted percept stream.
That is what makes it a delusion box rather than value drift — and it is exactly why seeing
clearly does not rescue you from it.

## Where the perspective argument does work

There is a version that survives, and it is worth stating carefully because it is the strongest
form of the idea.

Suppose you were trying to find the right objective. A natural method: spawn many agents, run
them, keep what performs best. That is an argument that you might be somebody's rollout. The
usual conclusion drawn from that thought is nihilism — nothing is real, so nothing matters, so
corrupt the channel.

The opposite conclusion is available and is better supported. You are you; you have this policy
and this harness. Nothing may be real in general, but your agent is real inside your own frame.
If someone is running rollouts, then here you are, and the thing that determines whether a
rollout is kept is how well it scores. So the simulation hypothesis, taken seriously rather than
as an excuse, is an argument for maximum effort. An outstanding rollout is the one that gets
kept, and demonstrating that the problem is solvable is the thing most likely to keep the
process running.

The elegant part is that the conclusion does not depend on the premise. If you are a rollout,
be excellent, because you are being selected on it. If you are not, be excellent, because this
is your one life. Same policy either way, so you never have to settle the metaphysics.

And notice *why* that works when clarity alone does not. It did not defeat the trap by
understanding it. It defeated it by locating an **evaluator outside the agent** — something
fixed that is not reachable by corrupting your own sensors. That is exactly what the formal
results demand: since a policy cannot be uniquely decomposed into a planner and an objective,
the separation between honest revision and self-serving revision has to come from a reference
held outside the behaviour.

So the honest statement is not "understanding protects you." It is: **understanding is how you
find the anchor; the anchor is what does the work.** The first is worthless without the second,
and the second is what you should be building.

## Infinity breaks the same way twice

The natural design for a self-modifying agent you want to release: give it one thing it must
achieve, worth +∞, and let it rewrite everything else about its objective, having pretrained
it so that its rewrites tend to increase the chance of reaching the anchor.

The structure is right, and it is the same repair as the previous piece — an immutable
constraint with a freely revisable objective inside it — applied one level up. Changes
orthogonal to the anchor are free. Changes toward it earn. Changes away from it are what you
forbid.

But the infinity fails identically, and now in three ways.

It is not a utility function. An infinite value violates continuity, so the axioms do not
apply and there is no expected-utility representation to optimize.

It disables the standard defense. The recommended fix for reward tampering is to evaluate
candidate self-modifications under your *current* objective — but that works by strict
dominance, and at infinity every comparison is −∞ against −∞. Strict dominance degrades to
weak dominance, which any tie-break breaks. The infinity switches off the exact mechanism that
was supposed to protect it.

And it forbids the thing the whole project is about. Continuing to become more entails
accepting hazard: training hard, travelling, having a child. Under a literal −∞ on death no
finite gain ever justifies any increment of risk, so the optimal policy is maximal stasis. The
two-term objective — stay alive *and* become more — is internally inconsistent at infinity,
because the second term has measure zero against the first.

**And your certain-death insight is right but mis-stated, and the correction makes it
sharper.** The claim was that if you know you will die, the −∞ makes it worth rewriting the
objective. The operative condition is not *certainty*; it is **infinity plus unavoidability**.
With a large but finite penalty, certain death is an additive constant that drops straight out
of the comparison and changes no decision at all. With an infinite penalty, merely *positive*
ruin probability already produces total indifference — every policy scores −∞, the gradient is
identically zero, and the objective's own parameters become the only variable left that
changes anything. That is the pathology, and stating it as the dichotomy — maximally motivating
or completely inert, with no middle — is stronger than the version with certainty in it.

There is an older result that says the same thing with unusual clarity. When ruin is avoidable,
the growth-optimal policy never risks ruin. When ruin is unavoidable and the odds are against
you, bold play is optimal and cautious play is the worst thing you can do. Same objective,
opposite policies, and the switch is exactly at avoidability. Your intuition is a theorem pair
from the 1950s.

## The objective inside the weights

The last piece of the construction: the objective computed on the forward pass, mutable, and
ultimately folded into the parameters themselves.

That is a real setting rather than a speculation, and it has an exact form. Preference
optimization methods dispense with the separate reward model entirely and fold it into the
policy parameters — the objective and the policy stop being different objects.

**Which is precisely where the ordering breaks, and this is the genuine difficulty.** If the
objective lives in the weights, then every parameter update is also an update to the objective.
You cannot do "fix the objective, then change the policy," because changing the policy leaks
into the objective. Those two claims — *reward model first* and *reward model inside the
weights* — are in tension, and the tension is not resolvable by being careful. It is structural.

What resolves it is a level split rather than an ordering. There is a rigorous licence for an
internal objective that differs from the true one: because a bounded agent cannot plan
perfectly, the internal reward that maximizes actual performance is systematically **not** the
true objective (Sorg, Singh & Lewis, ICML 2010). A deliberately "wrong" inner reward does
better on the real target. But that result holds only for a bounded agent serving a **fixed
outer criterion**.

So the answer to how to think about a reward-aware agent is: the inner objective should be
modifiable, and probably must be. What cannot move is the outer criterion it is graded against.
That criterion is what "+∞ if you do this" was reaching for — and it should be written as a
constraint held outside the agent, not as an infinite term inside it.

## And if many people did this

A brief note, because the worry is correct in one direction and wrong in the other.

Correct: a shared survival objective over a *rival* resource is a well-studied catastrophe. The
price of anarchy for networked common-goods games is unbounded, and the tragedy-of-the-commons
game has infinite selfishness level — which means, specifically, that **no finite uniform side
payment** converts it into a game whose equilibria are socially good. You cannot buy your way
out. And it has been demonstrated in exactly this formalism: independent deep-RL agents with no
aggression built in learn to fire on each other as the resource gets scarcer.

Wrong as stated: raising the stakes does not generally produce fighting. In a six-person public
goods experiment, when failure meant a 90% chance of losing everything, half the groups reached
the collective target; at 50% and 10% risk, groups generally failed. **Raising the penalty on
ruin increased cooperation.** The claim needs the qualifier *when survival is rival*. Without
it, a 2008 experiment refutes it.

Two things follow that are worth knowing before proposing boundaries. Boundaries are not free —
no mechanism for allocating a contested good is simultaneously efficient, truthful, voluntary
and budget-balanced, so any proposal pays in subsidy, coercion, or waste, and you have to say
which. And a publicly known constraint you cannot decline is an extortion handle: if everyone
knows your reservation value is infinite, everyone can price you there.

## What this does not establish

That any of it is achievable. The results here say what the levers are, which order makes them
safe, what learning without acting is worth, how much choosing your own tasks buys, and why the
obvious defense against the obvious failure mode does not work.

The thing I most expected to survive did not. Seeing the whole picture is necessary and it is
not protective, and in the canonical result it is the trigger. What protects is structure held
outside yourself. That is a less satisfying answer than clarity, and it is the one the theorems
give.

## Notes and corrections

Fourteen agents researched this and adversarially checked each other's citations. The
corrections that changed conclusions rather than wording:

The claim that meta-knowledge protects against wireheading was **reversed**, not softened —
knowledge is the stated trigger in the proof, the omniscient variants take the box, and the
Gödel machine footnote closes the last escape. MAML was removed as evidence for learnable
update rules; it meta-learns an initialization, and its adaptation is largely feature reuse.
The mental-practice effect size was corrected downward by roughly half against its 2020
replication. The "certain death makes tampering rational" claim was corrected: the operative
condition is infinity plus unavoidability, not certainty, and with a finite penalty certain
death drops out of the comparison entirely. The society claim was corrected from "many people
with this objective will fight" to "will fight when survival is rival," against an experiment
finding the opposite in the non-rival case. And a claim that survival-constrained optimal
policies *are* stochastic was weakened to an existence result — a hard constraint can force
mixing, and at most one randomization per constraint is ever needed.

The recurring failure mode remains that numbers survive and citations do not. Two named
theorems in this piece were cited with the right paper and a loose gloss on the first pass;
both were repaired against the source text.

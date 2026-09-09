---
title: "The Optimization Nobody Is Running"
description: "A person trying not to die is an agent running a reinforcement learning problem. Write the reward down properly and most of what follows is forced."
updated: 2026-09-08
---

## What we are actually after

Solving death is not the same problem as extending survival. A body preserved for a
thousand years and returned intact has not lived those years. Preservation and life are
different targets.

The target is being more alive than ever, and the object to build is not a routine. It is
a process that maintains you, notices when maintenance is failing, and improves how it
works.

Which means the first question is not *what should I do*. It is *what is the objective*.
Almost everything else is downstream of that answer, and the answer is usually not written
down at all.

## You are an agent running an optimization

A person trying to remain alive and functional over decades is performing sequential
decision-making under uncertainty, with noisy feedback, toward an objective. That is not a
metaphor for reinforcement learning. It is the definition of the setting reinforcement
learning studies.

This matters because it makes a vague complaint precise. "People are bad at looking after
themselves" is not a claim you can work with. "This is a single-episode partially observed
control problem with an unwritten objective" tells you which part is hard.

So write the objective.

## Writing the reward down

Here is the specification.

There is no discount factor. Reward accrues continuously for as long as you are alive. At
each instant there is a vector — call it Φ — of who you are at that moment: memories,
skills, language, muscle, aerobic capacity, everything mental and physical. Being alive
pays. Losing part of Φ while alive costs. Death ends the stream.

That is four choices, and three of them are provably the right ones. It is worth being
precise about which, because the reasons are stronger than the intuitions that produced
them.

And here is where the derivation lands, stated plainly, so you can read the machinery
knowing what it is for.

Reward is a rate rather than a number per step. It accrues for as long as you are alive,
and what it pays for is the *level* of Φ — being capable, not becoming capable. No discount
factor is written down, but there is one anyway, because the mortality hazard supplies it:
the rate at which the future matters is state-dependent and therefore partly under your
control. Losing capability costs strictly more than regaining it pays, and that asymmetry
is not a psychological quirk but the condition that stops the objective being farmable.
Survival is not a term in this sum at all — it is a constraint on which policies are
allowed. Φ is a vector and cannot be collapsed into a score. And two things need separate
terms because a rate cannot express them: a floor on the level, and whether you can still
learn.

Every section below is the argument that one of those is forced.

## Reward is a rate, not a number

The reward is a **density** — something per unit time — rather than a number attached to
each step. This is not a stylistic preference. A per-step reward silently encodes the
modeller's choice of time step, and the time step is made up. Doya's continuous-time
formulation makes the dependence explicit: the ordinary discrete Bellman equation is the
backward-Euler discretisation of the continuous problem, and the translation only works
after rescaling values by 1/Δt, with the discount factor appearing as γ = 1 − Δt/τ. A
per-step reward is not a statement about what is good. It is a statement about what is
good *per tick*.

The sharper result is that the per-step object degenerates entirely. Tallec, Blier and
Ollivier proved in 2019 that as the time step shrinks, Q^π(s,a) = V^π(s) + O(δt) — the
action-dependent part of the Q-function vanishes at rate δt and falls below function
approximation error. In the continuous limit **the Q-function contains no information
about which action to take at all.** What survives is the *advantage rate*. Their
empirical demonstration is that standard deep RL algorithms collapse as the time step is
made finer.

So the right object for ranking actions in a continuous-time problem is a rate. The
density formulation is not a modelling convenience; the alternative does not exist in the
limit.

## You never wrote a discount, and you got one anyway

Refusing a discount factor looks like the hard part of the specification to defend. It is
not, because you do not actually get to refuse it.

Write death as a hazard: at any moment, in state x under action u, the process terminates
at rate λ(x,u). Then the expectation of anything over the surviving trajectories equals the
expectation weighted by exp(−∫λ). **A state-dependent mortality hazard is exactly a
state-dependent discount rate.** In the Hamilton–Jacobi–Bellman equation the hazard enters
as −λ(x,u)·(V(x) − V_death), which with V_death set to zero is literally a discount term.

This is not new mathematics; it is the standard move in three separate literatures.
Boukas, Haurie and Michel reduced random-stopping-time control to an infinite-horizon
problem in 1990. Blanchard's perpetual-youth model, building on Yaari, runs the whole of
macroeconomics on a discount rate of ρ + p where p is the death rate. Martha White's
transition-dependent discount γ(s,a,s′) is the reinforcement-learning version.

The consequence is good news, and it is the most useful technical fact available here.
You never have to defend a rate of time preference — the usual embarrassment of anyone
writing a long-horizon objective — because you never asserted one. The discount is
*derived* from mortality. And because it is state-dependent, it says something an
exogenous constant never could: **the rate at which you should discount the future is
something you partly control.** Improve your state, lower your hazard, and the horizon
over which investment pays gets longer. That is the formal version of the observation that
getting healthier makes it rational to invest more in getting healthier, and it is a
genuine feedback loop rather than a slogan.

It also settles a question about how to choose a discount. Lattimore and Hutter showed
that a time-consistent sliding discount must be geometric — their recovery of Strotz's
1955 result — so an agent that picks a non-geometric discount is not one optimizer over
time but a sequence of optimizers that disagree with each other. Reading the discount off
the state rather than choosing it avoids having to make that choice at all.

## Four things that break

The specification as stated has four failures. Each repair is forced, and each one turns
out to buy something.

**Minus infinity on death does not do what it looks like it does.** The intent is clear:
survival is not tradeable. But every mortal agent dies with probability one, so every
policy scores minus infinity and the ordering over policies is empty — the objective
cannot rank anything. It is also not a utility function at all: an infinite value violates
continuity, so the von Neumann–Morgenstern axioms do not apply, and Skalse and Abate showed
that lexicographic and constraint-satisfaction objectives cannot be scalarised except
degenerately. The repair keeps the intent exactly: **survival is a constraint, not a term.**
Maximise Φ inside the feasible set — a constrained Markov decision process, or a
thresholded lexicographic order. Equivalently, use a large finite death value −M, which
enters the HJB as a running penalty λ(x,u)·M and recovers the lexicographic solution as M
grows. Survival sitting *above* the objective rather than inside it is what was meant in
the first place; this is how it is written so that it computes.

The related error is worth naming because it is easy to make. A reward of minus infinity
on death does not produce an agent that never gets out of bed. It produces indifference —
if all policies tie, nothing is preferred to anything. And the caution would be wrong on
the physiology too. Three weeks of strict bed rest in the Dallas study produced a decline
in aerobic capacity comparable to decades of aging. Immobility is not the safe action.

**Rewarding the change in Φ rewards nothing.** This is the deep one. If reward is the rate
of change of Φ, then the undiscounted integral of that rate is Φ(end) − Φ(start). It
telescopes. By Ng, Harada and Russell's theorem, it is exactly potential-based shaping of
the zero reward function — which is to say it is *policy-invariant*, and ranks lives only
by the condition they end in. Seventy-nine years as a vegetable followed by one spectacular
year scores identically to eighty years of steady accumulation. That contradicts the intent
completely.

**And the repair is the same fact as the hazard.** Integrating by parts, the discounted
integral of the rate of change of Φ equals −Φ(0) plus ρ times the discounted integral of
the *level* of Φ. So with any strictly positive rate, "reward = the change in who you are"
and "reward = ρ × who you are" are the same objective. With the mortality hazard supplying
ρ, rewarding *becoming* and rewarding *being* coincide. Without it, only the level works.
The hazard is not an inconvenience bolted onto the objective — it is the thing that makes
the level, and therefore time spent capable, matter at all.

**A risk-neutral version is blind to variance.** If Φ moves with a diffusion component, its
time derivative does not exist pathwise and the reward has to be written as the
differential dΦ, whose martingale part contributes zero in expectation. Under that
objective an injury and a coin flip between two injuries score the same. For a repeated
process that is fine. For one life it is wrong.

**Symmetric gains and losses make the objective farmable.** If losing a capability costs
exactly what regaining it pays, detrain-and-retrain cycling is free reward. This is the
general form of a known failure — an agent that is itself the source of the variation can
reward itself without making progress. The fix is an asymmetry: count losses more steeply
than gains, κ > 1. That single change also breaks the telescoping, so the path matters
even before the discount is introduced.

Which produces the sentence worth keeping: **loss aversion is the safety condition.** The
thing behavioural economics files under bias is, in this objective, precisely the term that
stops it being hackable. Reverse the weights and the increment term becomes a farm.

Two more terms are needed and neither is optional. A rate of zero cannot distinguish a
vegetable from a healthy adult on a plateau, so there has to be a **floor on the level**,
not only a term on the rate. And "can no longer improve" is a different failure from "is
not improving" — it is loss of plasticity, and it is measured: networks under sustained
continual training degrade until they learn worse than a linear model, with large fractions
of units effectively dead and the effective rank of their representations collapsing. It is
fixable by continually reinitializing the least useful units. **The known repair for losing
the ability to learn is targeted destruction**, which is the formal shadow of every
biological process that works by turnover.

## Who you are is not a number

Φ has to be a vector, and this is also a theorem rather than a preference.

Skalse and Abate proved that a multi-objective criterion collapses to a scalar reward
preserving the ordering over policies **if and only if** the collapse is a fixed linear
weighting. Miura showed multi-dimensional reward is strictly more expressive than scalar
reward. So unless your trade-offs between memory, skill, muscle and aerobic capacity are a
single fixed blend that never depends on context — and they are not — **no scalar reward
implements them.** The vector is a necessity.

Two obstacles come with it that cannot be designed around.

Debreu's representation theorem says an additive Φ requires every subset of attributes to
be preferentially independent of the rest. The obvious examples violate it: what a gain in
aerobic capacity is worth depends on musculoskeletal state. Additivity is a convenience
being assumed, not a property being used.

Worse, the components have wildly different time constants — muscle in weeks, semantic
memory over decades. Pitis proved that no aggregation of objectives with different
discount rates satisfies the von Neumann–Morgenstern axioms, dynamic consistency and Pareto
indifference together. The failure has a name and a mechanism: re-deriving the aggregate
each day can land the agent on the trajectory it least prefers. The known fix is one extra
non-Markovian parameter per objective, which is to say the aggregate has to carry state.

And a single life is the hard case. The criterion for one execution is the expectation of
the scalarised return, not the scalarisation of the expected return, and those differ
whenever the collapse is nonlinear. As of the field's own 2022 survey the single-execution
criterion had no defined coverage set and was described as badly understudied; it acquired
a general algorithm only in 2023.

## What follows from it

Here is what the objective produces once it is written correctly. These are consequences,
not advice.

**Blocking is a theorem.** In infinite-horizon multi-objective problems, deterministic
*non-stationary* policies can Pareto-dominate deterministic stationary policies that no
other deterministic stationary policy dominates. The worked example is one state and three
actions paying (3,0), (0,3) and (1,1); alternating the first two dominates the constant
policy whenever the discount exceeds 0.5 — at γ = 0.9, (15.79, 14.21) against (10, 10).
The usual escape is that stochastic stationary policies make mixtures available, and
mixtures substitute for non-stationary ones. **But a mixture's value is an average across
executions, and you get one.** In a single life the substitution is void and the
alternating construction is not replaceable. Periodising — training one quality hard, then
another — falls out of the objective rather than out of coaching folklore.

To be exact about the theorem: it says such a policy *can* dominate, and the stationary
policies it dominates are deterministic ones. It does not say alternation beats everything.
The single-execution part is the addition that makes it bite here.

**You do not need a correct list of your own capabilities.** The loss term already exists
in the literature: attainable utility preservation measures the sum over auxiliary
objectives of how much an action changes what you could still achieve, compared to doing
nothing. Its striking result is that it works with *randomly generated* auxiliary rewards.
You need a diverse basis of measurements, not a correct enumeration. For anyone assembling
a panel of tests, that is a large practical relief: the panel does not have to be right, it
has to be varied.

**Some of the objective is genuinely not editable, and there is evidence.** The popular
version of hedonic adaptation — that people return to baseline after anything — is wrong in
a checkable way. In the 1978 lottery-and-accident study the accident victims *were*
significantly less happy in the present (p < .01), the study had no baseline measurement,
and it sampled between one month and eighteen months after the event. The panel data that
followed says adaptation is systematically incomplete exactly where capability was
destroyed: disability effects of 0.40 to 1.27 standard deviations with little recovery
across nearly 40,000 respondents; unemployment not fully recovered even after
re-employment. If the objective were freely rewritable those deficits should have been
edited away. **The persistence is evidence that the capability terms are real and not under
the policy's control** — which is the strongest empirical support the specification has.

**The reference is not neutral and not shared.** The set-point literature's own revision
says set points are not hedonically neutral, differ between people, can be multiple within
one person, and can move. Roughly a fifth of a nationally representative sample recorded
substantial and apparently permanent change in life satisfaction over twenty years. So the
level term in the objective is not a constant to be discovered once.

**And the build order is implied.** Sustained income first, because every term in the
objective is integrated over decades and an optimization that stops when money runs out was
never going to reach its horizon — and because income is one of the few dimensions where
adaptation demonstrably does not finish: large lottery winners in a pre-registered Swedish
study showed life-satisfaction gains persisting more than a decade with no sign of
dissipating. Then measurement — cheaper, wider, more frequent, and validated against
outcomes rather than against other markers, since that is the binding constraint and every
other improvement is multiplied or nullified by it. Then procedure: designs that estimate
interactions rather than one factor at a time. Then environment, treated as a first-class
intervention rather than background, which is the strangest lever of the four — an agent
that shapes its own environment changes its own future observation and reward
distributions, making the problem non-stationary because of itself.

## The measurement is still broken, and that is separate

Getting the objective right does not give you access to it. This is the distinction that
matters most and is the one most often collapsed.

The reward is *dense*. It accrues every moment you are alive. What is sparse, delayed and
biased is your **measurement** of it. Those are different problems and only the second one
is about credit assignment.

And the measurement cannot be repaired by finding a better proxy. Skalse and colleagues
proved in 2022 that a proxy is unhackable — increasing it never decreases the true
objective — only if one of the two is constant. **There is no non-trivial safe proxy.** Not
hard to find. Does not exist.

The canonical demonstration should be better known. The Cardiac Arrhythmia Suppression
Trial tested drugs that successfully suppressed the marker they targeted, ventricular
ectopy after heart attack. The drugs worked on the marker. There were **63 deaths in 755
patients treated, against 26 in 743 on placebo** — more than double the mortality. The
optimization succeeded and the patients died. The statistics literature calls the general
case the surrogate paradox: a treatment can improve a surrogate, the surrogate can
genuinely predict the outcome, and the treatment can still make the outcome worse, with the
sign not deducible from the two component effects.

There is one constructive result here and it changes what to do. Work on the geometry of
Goodhart's law in Markov decision processes shows that optimizing an imperfect proxy is
beneficial up to a point and harmful past it, and derives an **early-stopping rule with
regret bounds** that provably avoids the harmful regime. The correction to "optimize the
biomarker" is therefore not "find a better biomarker." It is "stop at the right point,"
and that point is computable from how good the proxy is.

## Why nobody has run it

The rest of the difficulty is real but downstream. It is worth naming the whole setting
once, in the field's own vocabulary, because every clause is a live research area with its
own results: a **single-trajectory, reset-free, extreme-horizon, non-stationary partially
observed control problem with a vector-valued objective, measurement-as-action, shrinking
action sets, absorbing failure states, and an embedded self-modifying agent.** The
individual pieces are each hard. Their conjunction is not a research area — there is no
algorithm, no regret bound and no benchmark for it.

**Partial observability is where the complexity jumps.** Finite-horizon planning in a fully
observed problem is P-complete; make it partially observed and it is PSPACE-complete
(Papadimitriou & Tsitsiklis 1987), with no constant-factor approximation unless complexity
classes collapse. Optimizing a memoryless reactive controller — formally what a habit is —
is NP-hard. And the indefinite-horizon version is undecidable: Madani, Hanks and Condon
proved in 2003 that policy existence for infinite-horizon partially observed problems is
undecidable under discounted reward, undiscounted reward, average reward, and **state
avoidance** — which is exactly the survival objective.

**The horizon is nearly free; the delay is not.** It is natural to say fifty years is what
makes this hard. The field answered that: with normalized return, sample complexity scales
*logarithmically* in horizon length. What is expensive is delay between action and
feedback, where temporal-difference methods need updates growing exponentially in the
number of delay steps, and where even a perfect representation of the optimal value
function does not rescue you.

**You cannot explore.** Nearly every result in exploration theory assumes episodes: try,
observe, reset, repeat. You get one episode, no reset, and some actions are absorbing. And
"stuck in a local optimum" is the right complaint under the wrong name. The two accurate
names are **one-factor-at-a-time experimentation**, which provably cannot estimate
interactions and converges to points optimal along every axis and far from the joint
optimum, and **coverage failure** — in reinforcement learning, converging to a bad policy is
usually not a landscape problem but a data problem. You cannot learn what you never
sampled.

**Nobody has run the outer loop.** Taken literally, the claim that almost nobody attempts
this is false: there are 124 published mindfulness trials by 2016 alone, and a
cognitive-training literature large enough for meta-analyses of meta-analyses. Under the
reading that matters it is strongly supported — almost nobody has run a design capable of
telling whether their own update rule caused the change. The cleanest demonstration is a
sham-controlled neurofeedback trial where the control group received another child's
pre-recorded brain activity: read as a single-arm study the data reports an effect size of
**1.63**; read against its own control the specific effect is **p = 0.47**. Same numbers,
two designs, opposite conclusions. And when far-transfer claims from cognitive training are
pooled across meta-analyses, corrected for publication bias and restricted to active
controls, the effect is **exactly zero**, with zero true variance between studies.

**And coordination beats headcount.** Across 55 large trials of drugs and supplements with
cardiovascular outcomes, 57% of those published before 2000 reported a benefit; after
prospective registration became mandatory, 8% did. Same field, same funder, same kinds of
question. One coordination device removed seven-eighths of the apparent positive findings.
That is the reward-assignment problem again, one level up: the collective learns faster not
by adding minds but by fixing what its minds are rewarded for reporting.

## The reward model has an editor, and it is paid

There is already a mechanism inside the objective that alters the objective — and it pays
you for the alteration. It is happiness.

This is not a figure of speech. Lowering a target produces the relief of no longer falling
short of it, which means the edit is *self-rewarding*. Philosophy calls the general case
adaptive preference formation, and the reason it is hard to legislate against is that it
is indistinguishable from its virtuous twin: honest revision in light of evidence produces
the same behaviour from the outside.

Three properties make this worse than a bug you could patch.

**The regulator is partly differential, which is the failure this piece already
diagnosed.** The best-fitting computational model of momentary well-being — fitted on 26
subjects in the scanner and replicated on over eighteen thousand people online, explaining
around half the variance — is a leaky sum of three terms: rewards actually received,
expected value, and reward prediction error. Two of those are level-valued. But the paper's
headline finding is that positive expectations *reduce* the emotional impact of positive
outcomes. The regulator subtracts your own expectations from your own progress. To the
extent it tracks change rather than level, it is running exactly the objective shown above
to telescope into nothing — which means part of your built-in reward signal implements the
degenerate criterion by construction. It cannot rank a life; it can only rank a surprise.

**It is biochemical, and the strongest part of it does not report what you would want it
to.** Berridge and Robinson's dissociation is the relevant fact: *wanting* is generated by
large and robust mesolimbic dopamine systems, while *liking* is mediated by small, fragile
hedonic hotspots that are not dopamine-dependent. Sensitization amplifies wanting without
amplifying liking. So the machinery that most powerfully moves you is not the machinery
that reports whether anything is good, and the two can be driven apart. Any attempt to
overwrite the objective is competing against the larger and more robust of the two systems
using the smaller and more fragile one.

**And it runs unobserved.** Across six studies — romantic dissolution, tenure denial,
electoral defeat, negative feedback, employer rejection — people systematically
overestimated how long their affective reactions would last, and the authors' explanation is
that people are unaware of the mechanisms that reduce negative affect. You do not get to
watch the editor work. You only see the output and mistake it for the input.

So the objective is not merely rewritable in principle. It is being rewritten continuously,
by a process that is fast, chemical, self-rewarding and invisible. "Just decide what you
want" is not available.

There is one piece of leverage, and it is the same evidence as above. The editor is
powerful but it is not omnipotent, and where it fails is not random: adaptation is
systematically *incomplete* precisely where capability was destroyed. The editor can talk
you out of a disappointment. It has not managed to talk anyone out of a disability. That
bounds its reach, and the region it cannot reach is exactly the capability terms — which is
the second reason to build the objective out of Φ rather than out of how you feel.

## What this leaves open

The objective above is written as though it sits outside you. It does not. The weights on
Φ, the value assigned to death, the reference the whole thing is measured against — all of
them are inside the policy's reach. You can change what you want.

That is a harder problem than this one and it deserves its own treatment, but the shape of
it is worth stating. It is not uniformly bad to move the reward model. A change orthogonal
to the reference costs nothing. A change *toward* the reference should earn. What has to be
prohibited is the specific move of editing the target to match whatever you happen to have
achieved — and the difficulty is that from behaviour alone, that move and honest revision
are not distinguishable. Armstrong and Mindermann proved a policy cannot be uniquely
decomposed into a planning algorithm and a reward function, and that a simplicity prior
does not break the tie. "She wisely reweighted" and "she lowered the bar" are not separable
hypotheses from the outside. The separation has to come from something held fixed outside
the behaviour.

Which is the real reason to write the objective down first: **you cannot even pose the
question of what a legitimate change to it would be until there is an it.** And the
reference itself is only partly known — which is a third open problem, not a detail.

Rewriting your own reward model is plausibly the most significant thing a person can do,
it is exceptionally hard, and it is unproven. That is a separate piece.

## What this does not establish

None of this shows the problem is solvable. The formal results point the other way: the
setting is, in its general form, undecidable, and its components are individually hard.

What the specification buys is different. It says the objective is a density not a sum,
that the discount is derived not chosen, that survival is a constraint not a term, that
losses must count more than gains or the whole thing is farmable, that the state has to be
a vector and cannot be added up, and that blocking is implied rather than optional. A
person optimizing a biomarker with no validated link to an outcome, one factor at a time,
without a control, in a single life, is not doing a rough version of the right thing. They
are making a specific and nameable set of errors, and every one of them has a literature.

## Notes and corrections

The research behind this was re-checked against primary sources by a process instructed to
refute it. Roughly half the headline claims came back needing correction — almost always in
the attribution rather than the number.

Corrections made in this version. An earlier draft filed the reward under the wrong
heading, treating it as delayed and observed once at the end; the reward is dense and it is
the *measurement* that is delayed, which is a different problem with a different literature.
An earlier draft also claimed minus infinity on death produces an agent that never moves;
it produces indifference, and the physiology runs the other way — bed rest is among the
most damaging available interventions. The blocking theorem was initially stated as a
universal and is existential, and its hypothesis of *deterministic* stationary policies is
load-bearing; the single-execution argument is what makes it apply here. A claim that momentary
happiness is formally an integral of prediction errors was corrected rather than cut: the
underlying model is a leaky weighted sum of three terms, two of which are level-valued with
positive weights, so the regulator is only *partly* differential and the stronger version of
the inference does not follow.

The recurring failure mode is that numbers survive and citations do not. It is the reason
this section exists.

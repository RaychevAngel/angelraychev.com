---
title: "The Optimization Nobody Is Running"
description: "A person trying not to die is an agent running a reinforcement learning problem. It is being run extremely badly, and the reasons are specifiable."
updated: 2026-09-08
---

## What we are actually after

Solving death is not the same problem as extending survival. A body preserved for a
thousand years and returned intact has not lived those years. Preservation and life are
different targets.

The target is being more alive than ever, and the object to build is not a routine. It is
a process that maintains you, notices when maintenance is failing, and improves how it
works.

Which means the interesting question is not *what should I do*. It is *what kind of
problem is this, and why is nobody solving it well*.

## You are an agent running an optimization

A person trying to remain alive and functional over decades is performing sequential
decision-making under uncertainty, with delayed and noisy feedback, toward an objective.
That is not a metaphor for reinforcement learning. It is the definition of the setting
reinforcement learning studies.

This matters because it makes the vague complaint precise. "People are bad at looking
after themselves" is not a claim you can work with. "This is a single-episode partially
observed control problem with an unidentified reward and irreversible actions" tells you
exactly which part is hard and what has been tried.

So: specify it.

## The setting, named

The state has three parts. There is your actual physiological and functional condition,
which you never observe directly. There is your own decision apparatus — beliefs, habits,
capabilities, the set of actions available to you. And there is context: money, environment,
and the state of medical knowledge, which moves on its own.

You observe none of it directly. You observe a few noisy, biased, irregularly sampled
proxies — and *taking a measurement is itself an action*, with a cost, that has to be
planned. Some states are absorbing: reachable from almost anywhere, with no transition
out. Your action set shrinks with time. Your transition dynamics drift as you age, and
your own past actions modify them. And you are inside the system you are controlling,
not outside it.

Written in the field's own vocabulary, this is a **single-trajectory, reset-free,
extreme-horizon, non-stationary partially observed control problem with an unknown
multi-objective reward, measurement-as-action, shrinking action sets, absorbing failure
states, and an embedded self-modifying agent.**

Every one of those clauses names a live research area with its own results. Here is what
is known about them.

**Partial observability is where the complexity jumps.** Finite-horizon planning in a
fully observed problem is P-complete. Make it partially observed and it becomes
PSPACE-complete (Papadimitriou & Tsitsiklis 1987). You cannot approximate your way out:
no polynomial-time algorithm gives a constant-factor guarantee unless complexity classes
collapse. And the simplest possible policy class does not rescue you — optimizing a
memoryless reactive controller, which is formally what a *habit* is, is NP-hard.

**The indefinite-horizon version is undecidable.** You do not know your horizon. You are
not solving a fixed-length problem; you are trying to avoid an absorbing set for as long
as possible. That objective has a name — state avoidance — and Madani, Hanks and Condon
proved in 2003 that policy existence for infinite-horizon partially observed problems is
undecidable under discounted reward, undiscounted reward, average reward, **and state
avoidance**. Not intractable. Undecidable. No procedure can determine in general whether
a policy meeting a survival threshold exists at all.

**The regret theory does not apply to you.** The standard single-stream bound scales with
the *diameter* of the problem — the expected time to get from any state to any other. When
some states cannot be reached from others, the diameter is unbounded and, in the authors'
own words, the bounds become vacuous. Death is not reachable-from. Every guarantee in that
literature quietly assumes you can always get back, and you cannot.

The individual pieces are each hard. **Their conjunction is not a research area.** There
is no algorithm, no regret bound, and no benchmark for the problem you are actually in.

## The reward is wrong, and that is a theorem

This is the strongest claim in the argument and the one with the least wiggle room.

You cannot observe your objective. The terminal component — alive or not — is observed
exactly once, at the moment it stops being actionable. Everything you can optimize
day to day is a proxy.

And proxies of this kind cannot be made safe. Skalse and colleagues proved it in 2022: in
a rich enough space of policies, a proxy reward is *unhackable* — meaning increasing the
proxy never decreases the true objective — only if one of the two is constant. There is no
non-trivial safe proxy. Not "hard to find." Does not exist.

The medical record agrees, and the canonical case should be better known than it is. The
Cardiac Arrhythmia Suppression Trial tested drugs that successfully suppressed the
surrogate they targeted — ventricular ectopy after heart attack. The drugs worked on the
marker. In the treated group there were **63 deaths in 755 patients, against 26 in 743 on
placebo**: more than double the mortality. The optimization succeeded and the patients
died.

That is not an anomaly, it is a category. The statistics literature calls it the surrogate
paradox: a treatment can improve the surrogate, and the surrogate can genuinely predict the
outcome, and the treatment can still make the outcome worse — with the sign unpredictable
from the two component effects.

So when you optimize a biomarker you are not doing a crude version of the right thing. You
are doing something whose failure mode is documented, formally characterized, and
occasionally lethal.

The claim that rewards have been bad approximations is not a complaint. It is the
technically central problem.

## What is actually hard is the delay, not the length

Here the intuition needs correcting, and correcting it makes the argument stronger.

It is natural to say the problem is hard because the horizon is fifty years. The field
asked that question formally and answered it: **the horizon is nearly free.** Wang, Wang,
Yang and Kakade showed in 2020 that when total return is normalized, sample complexity
scales *logarithmically* in horizon length. Later work removed the dependence further. A
long episode is not, by itself, what makes learning hard.

What is hard is **delay between action and feedback**. Those are different quantities and
conflating them hides the real problem. With a reward that arrives once, at the end,
temporal-difference methods require a number of updates that grows *exponentially* in the
number of delay steps. And having a good representation does not save you: there are
problems where, even given features that perfectly represent the optimal value function,
finding a good policy requires exponentially many samples.

So the correct statement is not "fifty years is a long time." It is: *you receive one
informative reward signal, at the end, and the credit-assignment problem that creates is
provably hard even under favourable assumptions.*

There are partial tools. Return decomposition methods redistribute delayed reward back
along the trajectory. Off-policy evaluation estimates what would have happened under a
policy you did not follow — formally the right instrument for "what if I had done
otherwise." But applied to one person it is inert, and the reason is provable rather than
rhetorical: importance-sampling variance grows exponentially in trajectory length, and no
estimator can recover a counterfactual for an action your behaviour assigned probability
zero. You cannot estimate the value of a life you never came close to living.

## You cannot explore, and that is not a metaphor

Exploration theory says how much you should try unknown options. It also says the optimal
amount *declines as your horizon shortens* — which is a real result with an uncomfortable
implication for anyone deciding whether to experiment at fifty.

But the deeper problem is structural. Almost every result in that literature assumes
episodes: you try something, you observe, you reset, you try again. You get one episode.
There is no reset. Some actions are absorbing. Exploration in a setting where a mistake
can end the process is a named research area — safe exploration, constrained control,
shielding — and it has partial methods and no general solution.

**And "stuck in a local optimum" is the right complaint under the wrong name.** In high
dimensions, bad local minima are largely not the problem; saddle points are. The rigorous
version of what people actually do wrong has two better names:

The first is **one-factor-at-a-time experimentation.** Change one thing, observe, keep or
discard, move on. It provably cannot estimate interactions between factors, and on a
surface where factors interact it can converge to a point that is optimal along every
individual axis and far from the joint optimum. That is exactly "local optimization instead
of the general picture," stated so it can be acted on. The fix is a century old and sitting
in the design-of-experiments literature: factorial and fractional-factorial designs.

The second is **coverage failure.** In reinforcement learning, converging to a bad policy
is provably not usually a landscape problem — it is that your data never visited the states
where the better policy lives. You cannot learn what you never sampled. Reframed that way,
the problem is not that people are stuck in a valley. It is that they never generated the
observations that would show a valley exists.

## Nobody has run the outer loop

Your claim that almost nobody is seriously running this optimization is, taken literally,
false. Tens of thousands of people have made sustained deliberate attempts — 124 published
mindfulness trials by 2016 alone, a cognitive-training literature large enough to support
meta-analyses of meta-analyses, hundreds of neurofeedback studies.

Under the reading that matters, it is strongly supported: **almost nobody has run a design
capable of telling whether their own update rule caused the change.**

The demonstration is unusually clean. In the best-designed sham-controlled neurofeedback
trial, where the control group received another child's pre-recorded brain activity, read
as a single-arm study the data would report an effect size of **1.63** — an apparent
triumph. Read against its own control, the specific effect was **p = 0.47**. Nothing. The
same numbers, two designs, opposite conclusions.

And when the far-transfer claims of cognitive training are pooled across meta-analyses,
corrected for publication bias, and restricted to active controls, the effect goes to
**exactly zero**, with zero true variance between studies. Not small. Zero.

So: deliberate self-modification has been attempted at enormous scale and demonstrated
essentially never. That is not a claim about human potential. It is a claim about
experimental design.

**One correction to your framing, because it runs the wrong way.** You said that unlike
current neural networks, a brain changes as it runs. Current networks do change as they
run — not in weights, but in activations, and that is precisely meta-learning. In-context
learning *is* runtime adaptation with the weights frozen; there are explicit constructions
under which a single attention layer implements a step of gradient descent, and trained
models converge to them. The comparison you want runs the other direction: machine
learning has runtime meta-learning and has made it work, and the human case is the one
without a demonstrated outer loop.

There is a reason for that, and it is structural rather than a failure of will. Learning to
learn requires a *population*: meta-learning methods train across thousands of tasks;
learned optimizers have consumed thousands of accelerator-months across thousands of
environments. A human life supplies one meta-sample, non-resettable, with the meta-test set
identical to the meta-training set. The number of people who have completed even one full
outer-loop iteration — propose an update rule, run it long enough for the outcome to become
observable, measure it against a counterfactual, revise — is genuinely close to zero.

And a result worth knowing, because it is the formal shadow of aging: neural networks
trained continually **lose the ability to learn**. Not accuracy — plasticity. Under
sustained continual training, standard networks degrade until they learn worse than a
linear model, with large fractions of units effectively dead. It is fixable, by
continually reinitializing the least useful units. A learner that never refreshes any part
of itself stops being able to learn, and the fix is targeted destruction.

## More agents, and the strange lever

A group searches better than an individual, and the mechanism is specifiable rather than
inspirational.

Parallel actors do not merely produce more data — they change the *distribution* of what
gets seen. In distributed reinforcement learning, adding actors improved performance
substantially **without changing the rate at which the model was updated at all**: the gain
was exploration, not throughput. Population-based methods maintain diversity rather than a
single best candidate, and archive-based search deliberately keeps solutions that are not
currently the best because they are novel.

There are two hard limits, and both apply to you.

Parallelism buys wall-clock, not serial depth. There is a floor on the number of sequential
steps no amount of parallelism crosses. For a human problem, that floor is a lifetime of
sequential decisions with feedback delayed by decades. Ten thousand people do not shorten
it.

And human "rollouts" are not rollouts of the same policy in the same environment. Every
other person is a different starting condition in a different context with an unrecorded
behaviour policy. That converts a variance-reduction problem into an off-policy evaluation
problem, which is the hard one.

**Which makes coordination, not headcount, the actual lever** — and there is a startling
demonstration of it. Across 55 large trials of drugs and supplements with cardiovascular
outcomes, 57% of those published before 2000 reported a benefit. After prospective
registration became mandatory, that fell to **8%**. Same field, same funder, same kinds of
question. Installing one coordination device removed seven-eighths of the apparent
positive findings, which means seven-eighths of them were an artifact of the reward
structure researchers faced.

That is the reward-assignment problem again, one level up. The collective learns faster not
by adding minds but by fixing what its minds are rewarded for reporting.

**And then the strange one.** In reinforcement learning, designing the *environment* is
often more powerful than designing the policy — curriculum learning, automatic curricula,
environment design as an explicit optimization target. Environment is also, in the human
case, the least measured variable and plausibly among the most consequential.

The genuinely weird part is what happens when the agent shapes its own environment. It then
changes its own future observation distribution and its own future reward distribution. The
problem becomes non-stationary because of you. That is a real formal object — an agent
inducing its own distribution shift — and it is much less understood than policy
optimization. It is also, roughly, what a person does when they move city, change job, or
choose who they spend their time with.

## What follows

If this is the setting, the work is not a better protocol. It is building the machinery the
setting demands.

**Sustained income**, because every part of this requires resources over decades and an
optimization that stops when money runs out was never going to reach its horizon.

**Better reward assignment** — measurement that is more accurate, cheaper, wider in range,
and more frequent, and validated against outcomes rather than against other markers. This
is the binding constraint. Every improvement elsewhere is multiplied or nullified by it.

**Better optimization procedure**: designs that can estimate interactions rather than one
factor at a time; using AI to propose, screen and evaluate; getting more from a population
rather than more from a single life; and choosing the right exploration policy for a setting
where some mistakes are permanent.

**Environment design**, treated as a first-class intervention rather than background.

That list is not a routine. It is infrastructure for running an optimization that currently
nobody is running.

## What this does not establish

None of this shows the problem is solvable. The formal results point the other way: the
setting you are in is, in its general form, undecidable, and its components are individually
hard.

What the specification buys is different. It says which part is hard, what has been tried,
what partial methods exist, and where effort is currently wasted. A person optimizing a
biomarker with no validated link to an outcome, one factor at a time, without a control, in
a single life, is not doing a rough version of the right thing. They are making a specific
and nameable set of errors, and every one of them has a literature.

That is worth more than another protocol.

## Notes and corrections

The research behind this was re-checked against primary sources by a process instructed to
refute it. Half the headline claims came back needing correction — almost always in the
attribution rather than the number. A famous undecidability result was cited with the right
paper and a loose gloss; a continual-learning experiment's scale was overstated because a
figure describing how many tasks *could* be constructed was read as how many were run; a
proxy-reward paper's correlational sentence was wrong in both halves while its theorems held;
a surrogate-endpoint result was attributed to the wrong authors.

The recurring failure mode is that numbers survive and citations do not. It is the reason
this section exists.

---
title: "What should a running workout maximize?"
description: "Pace and repetitions describe a workout. I want to know which internal state they create, whether time in that state predicts adaptation, and what the adaptation buys me."
updated: 2026-10-10
draft: false
---

I can make a workout harder by running faster, resting less, or adding repetitions. That does not tell me whether I have made it better.

On [September 22](/running/record/2026/#22-september--vo-3800-m--530), I ran three 800 m repetitions with five and a half minutes between them. They averaged **2:48 (3:30/km)**. My breathing felt recovered after roughly two and a half to three minutes; the burning in my legs took about four minutes to ease only slightly. “Recovered” was describing different sensations with different time courses. That gave me a practical question: which remaining limitation would the next repetition encounter?

When I returned to structured running, I started separating four questions. How much oxygen can I use? How much work can I sustain while lactate is being produced and used? How much capacity do I have to work beyond what my aerobic supply can support? How fast can I run, and for how long can I maintain that speed?

I want training to leave me more capable after I recover, and to keep that capacity available over years. It has to fit within the time and recovery I can afford. My current event focus is an [800+ World Athletics point profile across 800–5000 m](/running-notebook/#the-runner-i-am-trying-to-build). That score curve gives later performance a common standard. The difficulty is that I have to choose today's workout before I can observe its lasting effect. Physiological exposure is a possible guide to that choice.

Those questions gave me four working labels: **VO₂** for oxygen uptake, **LT** for lactate-threshold work, **A** for anaerobic capacity, and **F** for fast running. The labels are useful only if they lead to a more precise question about the workout. Calling something a “VO₂ workout” cannot establish that I reached a high oxygen uptake. Calling something “anaerobic” cannot establish which adaptation it will produce.

The distinction I care about is this:

**Prescription → internal state over time → exposure → adaptation → performance.**

The prescription is what I choose: distance, pace, recovery, repetitions. The internal state is what happens to me. Exposure summarizes some part of that history. Adaptation is the change that remains after recovery. Performance is what I can subsequently do.

A training idea can be right about one arrow and wrong about the next. I might find a way to spend more time at high oxygen uptake without establishing that maximizing that time produces the best long-term improvement. I might improve a physiological measurement without improving the running that matters to me.

I want to reason through those arrows instead of collapsing them into “this session was hard.”

## Pace does not tell me my oxygen uptake

Imagine three three-minute repetitions. Suppose, just for this example, that oxygen uptake reaches my chosen target after the first minute of each repetition and stays there until the repetition ends. Nine minutes of running then contains six minutes at the target.

Now suppose a different recovery makes the second and third repetitions start from a state that cuts the delay to thirty seconds. With everything else held equal, I get seven minutes at the target. But if that recovery also makes me stop the third repetition after a minute, I get five. The arithmetic is easy. The assumptions are the experiment.

This is why I cannot optimize the work-to-rest ratio by itself. I need to know how recovery changes both the state at the start of the next repetition and my ability to continue it.

There is direct evidence that a higher running speed can defeat the aim of reaching maximal oxygen uptake. In a small study of seven participants, Billat and colleagues tested runs to exhaustion at several velocities. Four participants did not reach VO₂max at 140% of the velocity associated with VO₂max. Across the seven participants, time at VO₂max peaked at 100%, even though increasing velocity shortened the time needed to reach it. The result is specific to those tests and participants; it establishes the tradeoff, not a universal training pace. [Billat et al., 2000](https://pubmed.ncbi.nlm.nih.gov/10929211/).

The state I want and the speed that gets me there are different objects. A faster pace can bring the state closer while bringing the end of the repetition closer still.

My provisional exposure measure is something like:

$$
Q_{\mathrm{VO_2}} = \int_0^T w\!\left(\frac{\dot V\!O_2(t)}{\dot V\!O_{2,\max}}\right)\,dt.
$$

Here t is time, T is the session duration, and the oxygen-uptake rate is divided by my maximum to give a dimensionless fraction. If w is dimensionless and time is measured in minutes, Q has units of weighted minutes. The integral can include recovery as well as work.

The weighting function says how much I value different oxygen-uptake levels. Counting time above 90% is one possible choice. It gives an abrupt boundary: a second at 89.9% contributes nothing, a second at 90.1% contributes fully. A smooth weighting would avoid that discontinuity, but choosing a nicer mathematical function would not validate it biologically.

The choice can change how I rank actual workouts. Twelve highly trained runners completed four three-minute intervals and twenty-four thirty-second intervals in randomized order on a treadmill, with faster work and recoveries in the short format. On average, the short format produced higher mean oxygen uptake across the session, including recoveries, but less time above 90% of VO₂max. Those measures favored different sessions. This acute comparison does not establish which produces the best long-term training effect. [Fleckenstein et al., 2025](https://doi.org/10.3389/fspor.2024.1507957).

The expression exposes my assumption: the state history contains information the repetition times omit. The weighting and its relationship to later performance still need validation.

## Recovery and pacing are part of the same problem

During recovery, I would like to arrive at the next repetition able to sustain useful work. For a VO₂ objective, I would also like to avoid spending the whole next repetition climbing back toward the state I wanted. How much recovery achieves both depends on the session and on me that day.

Keeping recovery active is not automatically an improvement. Dupont and colleagues compared repeated fifteen-second efforts with either passive recovery or active recovery at 40% of VO₂max. In twelve men, time to exhaustion was substantially longer with passive recovery. That is evidence about repeatability in a particular protocol. It does not establish that passive recovery maximizes time near VO₂max, or that it is best for every interval session. [Dupont et al., 2004](https://pubmed.ncbi.nlm.nih.gov/14767255/).

Pacing within the repetition offers another control. I could start harder to accelerate the rise in oxygen uptake, then reduce speed to keep running in the desired state. That is a testable idea, but “fast start” is not sufficient specification.

Bailey and colleagues studied seven men cycling with fast, even, and slow starts. A fast start sped the oxygen-uptake response and improved the final sprint in their three-minute test; pacing did not improve final-sprint performance in the six-minute test. In a later study of eight cyclists, Miller and colleagues matched the interval formats for modeled W′ expenditure—the work assigned above critical power—and found no statistically significant difference in time above 90% of VO₂max between fast-start and steady-power formats. That model match did not directly measure the reserve remaining in my A hypothesis below. [Bailey et al., 2011](https://pubmed.ncbi.nlm.nih.gov/20689463/); [Miller et al., 2023](https://doi.org/10.3390/sports11120238).

These results make the question more interesting. Did a pacing strategy improve the oxygen response at comparable expenditure, or did it simply spend more of the available capacity earlier? Does the advantage survive repeated efforts? Does it survive comparison over the entire session? Evidence from cycling can inform those questions without fixing the answer for my running.

There is also some evidence connecting internal exposure with adaptation. Odden and colleagues measured oxygen uptake during an interval-training program in twenty-two trained cyclists. A higher fraction of VO₂max during training was associated with greater improvement in several fitness and performance measures. The study supports investigating the exposure; the association does not prove that deliberately maximizing it would cause the greatest improvement. [Odden et al., 2024](https://doi.org/10.1002/ejsc.12202).

That last distinction matters. An athlete who tolerates more useful exposure might also differ in other ways. A candidate dose is not yet an optimal dose.

## Lactate is a stock-and-flow problem

The question behind my LT label is not “how much lactate can I accumulate?” It is how much work I can sustain while producing, transporting, and using it.

Blood lactate concentration is a measurement of a stock relative to a volume. Rates of appearance and disappearance describe flows through the measured system. Bergman and colleagues measured those flows with tracers, alongside measurements across the exercising legs. Their results show why concentration and net release alone are inadequate descriptions of lactate metabolism. [Bergman et al., 1999](https://doi.org/10.1152/jappl.1999.87.5.1684).

For a simplified compartment containing an amount L:

$$
\frac{dL}{dt} = R_a - R_d.
$$

L is the amount in that compartment; $R_a$ and $R_d$ are its rates of appearance and disappearance, measured in amount per unit time.

Equal inflow and outflow could both be ten units per minute or both be twenty. In either case the amount stays constant. The second case has twice the turnover. This is bookkeeping, not a claim that the body is one perfectly mixed container; translating an amount into a blood concentration also requires accounting for distribution volume.

That distinction changes how I read an improvement. A lower lactate concentration at the same running speed would not, by itself, tell me that I had become better at removing lactate. Perhaps less was appearing. Perhaps removal changed. I need measurements capable of separating those explanations.

The comparison also needs the right denominator. In Bergman's longitudinal study, nine men completed nine weeks of cycle training. At the same absolute workload after training, lower arterial lactate accompanied reduced appearance, while no statistically significant increase in whole-body metabolic clearance was detected. At the same relative workload—65% of the new, higher VO₂peak—clearance increased. “Training lowers lactate” conceals two different comparisons and two different mechanisms. [Bergman et al., 1999](https://doi.org/10.1152/jappl.1999.87.5.1684).

Clearance has another trap. Metabolic clearance rate is disappearance rate divided by concentration. It is not the disappearance rate itself. Messonnier and colleagues compared six trained and six untrained men and tested the trained group both at and below their lactate threshold. Metabolic clearance was higher below threshold than at threshold. A claim that threshold is the point of maximal *clearance* would therefore need to specify which quantity it means; the study does not establish that lactate disappearance flux is greatest at the lower intensity. [Messonnier et al., 2013](https://pubmed.ncbi.nlm.nih.gov/23558389/).

The LT exposure I want to investigate is time near the highest lactate disappearance flux I can sustain for a specified duration, supported by endogenous lactate production, with appearance roughly balancing disappearance and a stated limit on drift in the stock. That is a proposed training question, not an established definition of lactate threshold.

Bergman's same-absolute-work result is a warning against turning that score into the outcome: lower turnover could accompany an adaptation I wanted. Moving more lactate through the system is not valuable by itself. I would need to test whether sustained high flux describes a productive stimulus, while judging success by the work I can subsequently sustain. Pace and a single lactate reading cannot supply that test.

I can still make the question operational. If I repeat a session at the same absolute pace, am I comparing its cost? If I increase pace to match the same relative intensity, am I comparing the new work I can sustain? Both comparisons can be valuable. They answer different questions.

## My anaerobic hypothesis: time near empty

For A, I have been thinking about a reserve: capacity to supply work beyond what the aerobic contribution supports. The word “reserve” is a model I can reason with, not a claim that there is one anatomical tank with a readable gauge.

Even a laboratory estimate is model dependent. Medbø and colleagues estimated anaerobic capacity from maximal accumulated oxygen deficit: estimated oxygen demand minus measured oxygen uptake, accumulated over exhausting exercise. Demand was estimated from the relationship between submaximal running intensity and oxygen uptake. This is a way to estimate a total contribution; it does not reveal my moment-by-moment reserve during an ordinary track session. [Medbø et al., 1988](https://pubmed.ncbi.nlm.nih.gov/3356666/).

My hypothesis is that the training-relevant state might be spending time with little reserve remaining. Why consider the remaining fraction? In the model, producing a high power briefly and continuing to demand work when little capacity remains are different challenges. If challenging that remaining capacity promotes its later growth, time near empty could matter beyond the total work performed. That is the conjecture. A competing explanation is that useful output or force maintained under fatigue matters, rather than the depleted state itself.

Write the fraction left as a(t), and consider:

$$
Q_A = \int_0^T g(a(t))\,dt,
$$

where a is dimensionless, T is session duration, and g gives more weight to a small remaining fraction. With dimensionless weights and time in minutes, Q_A is again weighted minutes. Counting time below a chosen small fraction would be a rough version of the same idea.

This differs from counting how many times I “empty the tank.” Consider two hypothetical sessions. One reaches a low reserve for ten seconds, then allows a long recovery, ten times. Another reaches it once, then alternates small amounts of work and recovery while staying near that low state for three minutes. Counting visits favors the first; counting time near empty favors the second. Neither score establishes which session produces more adaptation. The competing output explanation also makes a prediction: time spent nearly empty while producing very little might contribute little useful stimulus.

As written, Q_A also counts passive recovery while reserve remains low. Because g depends only on a, the same reserve fraction receives the same weight whether I am running or resting. If useful output under fatigue matters, the expression does not account for it.

My October 6 attempt made that last question tangible. I planned twelve ten-second sprints with ten-second recoveries. My phone timer failed after five; after a three-to-five-minute interruption, I did eight more. It was two sets, not one continuous thirteen-repetition sequence. Very early, I felt as if I was trying hard with little happening. The nominal ten-second recovery also included several seconds of deceleration before a few walking steps and the next start. Those details changed the actual session. The effort felt extreme, but neither the suffering nor the interruption measured a depleted reserve.

The short work–rest pattern also appears in my [May 18, 2021 record](/running/record/2021/#18-may--10-seconds-hard-10-seconds-rest), programmed as sixteen ten-second efforts with ten-second recoveries. Recovering that earlier attempt gives the experiment a history; it does not establish what adaptation either session produced.

There is a direct running comparison worth separating from my experiment. Saraslanidis and colleagues had sixteen men train for eight weeks, three times a week, using two or three sets of two 80 m sprints. The recovery between paired sprints was ten seconds in one group and sixty in the other. Both improved sprint performance; the ten-second group improved more over the final 100 m of the 200 m and 300 m tests. Recovery structure can therefore matter to later speed maintenance. The tested unit was a pair of sprints, however, and the result does not validate time near empty as the cause or establish a continuous 10/10 set as the best format. [Saraslanidis et al., 2011](https://pubmed.ncbi.nlm.nih.gov/21777153/).

Tabata's research is relevant, but it cannot finish that argument for me. In a 1997 acute cycling experiment, a protocol of twenty-second efforts with ten-second recoveries accumulated an oxygen deficit close to the participants' measured maximum. A different protocol, with harder thirty-second efforts and two-minute recoveries, accumulated less. Intensity, effort duration, and recovery all changed together. The experiment cannot isolate recovery as the cause, and accumulated deficit is not a measured trace of reserve remaining. [Tabata et al., 1997](https://pubmed.ncbi.nlm.nih.gov/9139179/).

An eight-week running trial makes the adaptation question more concrete. Thirty-one aerobically well-trained men were analyzed after forty-eight were randomized to three interval formats: four four-minute efforts with three-minute active recoveries, roughly eight twenty-second efforts with ten-second passive rests, or ten thirty-second efforts with three-and-a-half-minute active recoveries.

The four-minute format produced greater gains in VO₂max per kilogram of body mass than either sprint format. Only the twenty-second group had a statistically significant increase in estimated anaerobic capacity, with a greater change than the four-minute group. All three improved over 3000 m, including the thirty-second group without a detected increase in VO₂max or anaerobic capacity. The protocols changed several variables together, and the trial did not measure time near a depleted reserve. It separates outcomes without establishing my Q_A as the cause. [Hov et al., 2023](https://doi.org/10.1111/sms.14251).

The hypothesis specifies a comparison, but two pieces are missing: a way to define or independently estimate reserve, and evidence connecting that estimate to later adaptation. Until then, Q_A cannot supply a score for my track session. A satisfying reservoir story must not be allowed to fill either gap.

## Fast running has a duration and a cost

F is my working label for a useful fast running velocity together with the duration for which I can maintain it. It is not simply the greatest instantaneous speed I can reach.

A speed without a duration hides the problem. For a chosen fast velocity $v_F$, I also care about $T_{\max}(v_F)$, the longest time I can maintain it. In my own planning, a six-hundred-metre effort has served as a practical fast-running reference. It is a personal anchor, not a measured physiological boundary.

There are at least three different improvements I could notice. I could run a relaxed two hundred metres faster. I could hold the same fast velocity for longer in one continuous effort. Or I could maintain it across more two-hundred-metre repetitions with the same recovery. For that last comparison, I need the repetition distance, count, and recovery—not just the pace. Changing one minute of recovery to three changes the question even if every repetition has the same time. Faster running, longer continuous endurance, and better repeatability belong in the picture separately.

Economy is an overlapping cost question: can I pay less for the same movement? Paavolainen and colleagues studied nine weeks of combined explosive-strength and endurance training in eighteen well-trained endurance athletes. The experimental group improved five-kilometre performance and running economy without an increase in VO₂max. The intervention involved several kinds of training; it does not show that my fast repetitions alone would reproduce the result. It does show why oxygen capacity cannot be the whole performance objective. [Paavolainen et al., 1999](https://doi.org/10.1152/jappl.1999.86.5.1527).

For F, an exposure score would have to say which speed, which duration, and which quality criterion I value. If later repetitions lose that quality, adding them may increase the written volume while adding little of the intended exposure. If I can sustain the same quality at lower cost, that may be progress even before I add volume.

“Quality” also needs an observable definition. A repetition time is one observation. Economy requires a cost measurement at a specified speed. Looking smooth and feeling less strained can help me choose what to test, but they cannot establish a change in oxygen cost.

## The workout competes with the next workout

These four questions do not describe four isolated systems. The twenty-second running format improved both oxygen capacity and estimated anaerobic capacity. A fast repetition can involve high oxygen uptake and substantial work beyond the aerobic contribution. An LT session still has a movement cost. Assigning one purpose helps me make a decision; it does not partition the body.

I could try to create an enormous session that touches everything. My concern is that “touches everything” is too weak an objective. I want enough exposure to change something, at a cost that lets me keep training. Maximizing one acute quantity without considering what follows could reduce the useful exposure I accumulate over the next week.

That is a planning principle I am adopting, rather than a formula the cited experiments have proved. I do not yet have a validated exchange rate between minutes at high oxygen uptake, time near a hypothetical depleted reserve, fast-running quality, and recovery cost. Adding those scores into one impressive total would hide the uncertainty.

The immediate discipline is simpler. Name the adaptation I want. Specify the internal state I think will promote it. Choose controls that plausibly create that state. Record what happened, including the circumstances that could change the comparison. Then test whether performance actually improved, at a cost that lets the training continue.

The current choices put that principle to work. On [8 October](/running/record/2026/#8-october--lt-31200-m--1-min), my three 1200 m LT repetitions averaged **4:42.17 (3:55.1/km)** with one-minute recoveries, and I felt another repetition was available. That passed the gate for the next LT workout to become three 1600s. VO₂ remains at three 800s with 5:30 between them; its own gate is a 2:40 average without a major final-repetition collapse. These are independent decisions based on completed work and how it felt; neither establishes that my physiological explanation was right. The [running notebook](/running-notebook/) keeps the choices and their evidence together.

Continuity also makes the surrounding activity relevant. A hard bike commute can change what the same track workout costs me. Running to the gym and carrying a backpack belong in the same life as the formal sessions. A programme I can keep using has to account for that movement too.

The framework earns its place by changing what I notice and what I compare. If it only gives my existing workouts more elaborate names, it has failed.

I want better running, and I also want the freedom that comes with it: [a city that feels smaller](/running-makes-the-city-smaller/). Those are the outcomes. Internal exposure is a tool for understanding how to get there, and every proposed tool has to answer to the result.

## References

All studies below are primary research. Several used cycling, small samples, or acute tests; those limits are part of the argument, not details to discard when translating them into running.

- Billat VL, Morton RH, Blondel N, et al. “Oxygen kinetics and modelling of time to exhaustion whilst running at various velocities at maximal oxygen uptake.” *European Journal of Applied Physiology* 82, 178–187 (2000). [doi:10.1007/s004210050670](https://doi.org/10.1007/s004210050670).
- Fleckenstein D, Braunstein H, Walter N. “Faster intervals, faster recoveries — intensified short VO₂max running intervals are inferior to traditional long intervals in terms of time spent above 90% VO₂max.” *Frontiers in Sports and Active Living* 6, 1507957 (2025). [doi:10.3389/fspor.2024.1507957](https://doi.org/10.3389/fspor.2024.1507957).
- Dupont G, Moalla W, Guinhouya C, Ahmaidi S, Berthoin S. “Passive versus active recovery during high-intensity intermittent exercises.” *Medicine & Science in Sports & Exercise* 36, 302–308 (2004). [doi:10.1249/01.MSS.0000113477.11431.59](https://doi.org/10.1249/01.MSS.0000113477.11431.59).
- Bailey SJ, Vanhatalo A, DiMenna FJ, Wilkerson DP, Jones AM. “Fast-start strategy improves VO₂ kinetics and high-intensity exercise performance.” *Medicine & Science in Sports & Exercise* 43, 457–467 (2011). [doi:10.1249/MSS.0b013e3181ef3dce](https://doi.org/10.1249/MSS.0b013e3181ef3dce).
- Miller P, Perez N, Farrell JW III. “Acute Oxygen Consumption Response to Fast Start High-Intensity Intermittent Exercise.” *Sports* 11, 238 (2023). [doi:10.3390/sports11120238](https://doi.org/10.3390/sports11120238).
- Odden I, Nymoen L, Urianstad T, et al. “The higher the fraction of maximal oxygen uptake is during interval training, the greater is the cycling performance gain.” *European Journal of Sport Science* 24, 1583–1596 (2024). [doi:10.1002/ejsc.12202](https://doi.org/10.1002/ejsc.12202).
- Bergman BC, Wolfel EE, Butterfield GE, et al. “Active muscle and whole body lactate kinetics after endurance training in men.” *Journal of Applied Physiology* 87, 1684–1696 (1999). [doi:10.1152/jappl.1999.87.5.1684](https://doi.org/10.1152/jappl.1999.87.5.1684).
- Messonnier LA, Emhoff CA, Fattor JA, Horning MA, Carlson TJ, Brooks GA. “Lactate kinetics at the lactate threshold in trained and untrained men.” *Journal of Applied Physiology* 114, 1593–1602 (2013). [doi:10.1152/japplphysiol.00043.2013](https://doi.org/10.1152/japplphysiol.00043.2013).
- Medbø JI, Mohn AC, Tabata I, Bahr R, Vaage O, Sejersted OM. “Anaerobic capacity determined by maximal accumulated O₂ deficit.” *Journal of Applied Physiology* 64, 50–60 (1988). [doi:10.1152/jappl.1988.64.1.50](https://doi.org/10.1152/jappl.1988.64.1.50).
- Saraslanidis P, Petridou A, Bogdanis GC, et al. “Muscle metabolism and performance improvement after two training programmes of sprint running differing in rest interval duration.” *Journal of Sports Sciences* 29, 1167–1174 (2011). [doi:10.1080/02640414.2011.583672](https://doi.org/10.1080/02640414.2011.583672).
- Tabata I, Irisawa K, Kouzaki M, Nishimura K, Ogita F, Miyachi M. “Metabolic profile of high intensity intermittent exercises.” *Medicine & Science in Sports & Exercise* 29, 390–395 (1997). [doi:10.1097/00005768-199703000-00015](https://doi.org/10.1097/00005768-199703000-00015).
- Hov H, Wang E, Lim YR, et al. “Aerobic high-intensity intervals are superior to improve V̇O₂max compared with sprint intervals in well-trained men.” *Scandinavian Journal of Medicine & Science in Sports* 33, 146–159 (2023). [doi:10.1111/sms.14251](https://doi.org/10.1111/sms.14251).
- Paavolainen L, Häkkinen K, Hämäläinen I, Nummela A, Rusko H. “Explosive-strength training improves 5-km running time by improving running economy and muscle power.” *Journal of Applied Physiology* 86, 1527–1533 (1999). [doi:10.1152/jappl.1999.86.5.1527](https://doi.org/10.1152/jappl.1999.86.5.1527).

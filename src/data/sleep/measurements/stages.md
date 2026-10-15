---
title: "Sleep stages and brain activity"
description: "Estimated light, deep and REM sleep are useful research signals, with different evidence from direct EEG measurements."
updated: "2026-10-15"
order: 5
role: "Investigate"
attention: "Validate before setting stage targets"
---

## What the labels mean

Clinical sleep staging uses brain electrical activity, eye movements and muscle activity. Its conventional labels are wake, N1, N2, N3 and REM. Consumer devices usually combine N1 and N2 as **light**, call N3 **deep**, and report REM separately. That mapping makes a four-class comparison possible; it also hides differences within light sleep. [Clinical comparison methods](https://pmc.ncbi.nlm.nih.gov/articles/PMC11511193/).

Oura Ring 5 measures optical pulse signals, movement and finger temperature. Its listed sensors do not include EEG. The stages are algorithmic estimates from signals associated with sleep states, rather than direct recordings of those brain states. [Ring 5 sensor specification](https://ouraring.com/store/rings/oura-ring-5).

## Dream recall is a separate observation

Not remembering dreams does not establish that REM was absent. In a high-density EEG study using repeated awakenings, dreaming and no-experience reports were compared within both REM and NREM sleep. Dreaming also occurred in NREM. Immediate awakening reports do not calibrate an ordinary morning recollection into a whole night's REM duration. [Siclari et al., 2017](https://www.nature.com/articles/nn.4545).

On [15 October](/sleep/record/#night-2026-10-15), I recalled no dreams, while Oura estimated **37m30s REM** and COROS reported **16% REM**. These observations can coexist. The devices estimate stages; recall describes what I remember. Neither supplies direct EEG confirmation of an exact personal REM total.

Deep NREM sleep is usually more concentrated early in the night, and REM later. Ending a night early can reduce REM-rich opportunity, but clock times alone cannot establish how much occurred or was missed. This is a reason to examine sufficient obtained sleep, rather than infer zero REM or force a percentage quota. [NHLBI stage overview](https://www.nhlbi.nih.gov/health/sleep/stages-of-sleep).

## The first observation

For the sleep ending October 13, Oura returned **1h43 deep, 1h41 REM and 3h38 light**, totaling 7h02 asleep. These are approximately 24.4%, 23.9% and 51.7% of its estimated sleep. Deep and REM contributor grades were 95 and 81; those grades are distinct from minutes or percentages.

COROS returned deep/light/REM ratios of 20%/50%/27%, with 3% awake. Its connector did not explicitly specify the ratio denominator. Those percentages should remain as returned rather than being converted into apparently exact stage minutes using an assumed denominator. [First record](/sleep/record/#night-2026-10-13).

## What published validation establishes

A 2024 study of **Gen3 running OSSA 2.0**, with 35 healthy adults and one laboratory PSG night each, found **92.0% sleep/wake agreement but 76.3% four-stage agreement**. Nightly deep and REM duration concordance was poor, despite similar group averages. Oura funded the study; its lead author disclosed Oura advisory and consulting relationships. These are findings for the tested generation and algorithm. [Robbins and colleagues](https://pmc.ncbi.nlm.nih.gov/articles/PMC11511193/).

Our actual device reports hardware `or5` and firmware `2.1.25`. A supplementary API request reports sleep algorithm version `v2`; the exact model revision and mapping to published validation protocols remain unverified. A Ring 5-specific independent PSG validation has **not been verified in this research pass**. Earlier studies provide background evidence, not an exact error bound for this ring. The [validation investigation](/sleep/research/measurement-and-validation/) records those distinctions.

## The target to develop

The immediate task is to characterize repeated estimates, disagreement between devices and associations with meaningful outcomes. Between-night variation contains both real physiology and possible measurement error; it is not automatically a measure of sensor noise. A numerical stage target remains unresolved.

Published guidance does contain some stage bands. The NSF's 2017 consensus rated N3 at 16–20% and REM at 21–30% as good-quality indicators for ages 26–64. It identified no positive consensus band for either stage at ages 18–25. These are expert judgments, not trials establishing personal performance optima; downstream health outcomes were outside the report's scope. Our broad 19–30 age context spans both groups. The first ring-estimated 24.4% deep sleep therefore cannot be declared harmful or reduced merely to fit the adult band. NSF funded the report; several panelists disclosed industry relationships. [Original consensus and figures 6/9](https://doi.org/10.1016/j.sleh.2016.11.006).

For a future experiment, state whether the desired change concerns estimated minutes, a proportion of total sleep, EEG slow-wave activity or a functional outcome. These are different achievements. A higher percentage could result from less sleep in other stages without obtaining any additional deep minutes. A longer total night could add REM minutes without changing its percentage.

Extra estimated deep sleep therefore needs an interpretation: what changed, how securely was it measured, and what benefit did it accompany? Light sleep should remain a measured component of the night, not be treated as time to eliminate.

## A route beyond the ring

If stage physiology becomes the limiting question, PSG or a specifically validated EEG system can supply a closer reference. EEG also permits questions about slow-wave activity, spindles and their timing that stage totals alone cannot answer. A headband's validity depends on its montage, model, algorithm and use conditions; it cannot inherit the credentials of every other EEG device. [EEG reference discussion](/sleep/research/measurement-and-validation/#brain-states-and-sleep-staging).

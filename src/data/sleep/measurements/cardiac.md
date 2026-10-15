---
title: "Heart rate and heart-rate variability"
description: "Overnight pulse and beat-interval measurements can track change, provided their sampling and definitions remain visible."
updated: "2026-10-15"
order: 6
role: "Trend"
attention: "Match the measurement window"
---

## Distinguish the measurements

Heart rate is beats per minute. HRV describes variation between successive beat intervals; its numerical value depends on the statistic and sampling window. A minimum HR, overnight average HR, predicted waking HR and HRV are separate quantities.

Oura's overnight HRV display averages five-minute samples. COROS describes averaging ten-minute intervals. COROS's current resting-HR estimate predicts **seated HR shortly after waking** from sleeping measurements. It is not simply the lowest sleeping value. [Oura HRV](https://support.ouraring.com/hc/en-us/articles/360025441974-Heart-Rate-Variability), [COROS HRV](https://support.coros.com/hc/en-us/articles/20959044334612-Overnight-HRV), [COROS resting-HR definition](https://coros.com/stories/coros-metrics/c/resting-heart-rate-explained).

The Oura API also distinguishes its sleep-HR average and minimum from the app display: these API values use thirty-second samples, whereas the app uses aggregated five-minute samples. A small API/app difference can therefore arise without a sensor disagreement. [API reference](https://cloud.ouraring.com/v2/docs).

## The first observation

Oura returned **50.4 bpm average during sleep**, a **45 bpm sleep minimum**, and **61 ms average HRV**. COROS returned **61 ms overnight HRV**, **44 bpm daily minimum**, **64 bpm daily average** and **55 bpm predicted seated resting HR**. [October 13 record](/sleep/record/#night-2026-10-13).

The identical rounded HRV values are encouraging agreement for that summary. They do not verify identical beat intervals or processing. The 44 versus 45 minima also cover different scopes. The 55 versus 45 difference is not a demonstrated 10 bpm sensor error, because the definitions differ.

COROS recorded average HR 148 during the previous evening's track run. There were no returned Oura samples in that workout interval, so that session does not support an exercise accuracy comparison.

## The evening decline is a different measurement

Before the sleep ending [15 October](/sleep/record/#night-2026-10-15), I noticed a decline from the high 70s around 22:00 to the high 50s around 01:30. The targeted API query broadly supports a declining sampled pulse: awake-labelled half-hour medians were 82 bpm at 22:00, 63 at 23:00, 56 at 00:30 and 55 at 01:00. Values fluctuated and coverage was irregular. The record shows sample counts, ranges and gaps; differently sampled workout/rest categories were excluded from this awake-only comparison.

This is not a continuous resting-heart-rate trajectory or a test that isolates dinner. Food, posture, movement and settling can coincide with clock time. A randomized meal/autonomic experiment supports a post-meal cardiac response, but does not identify the cause or duration of this personal trend. The study had Flax Council of Canada and NIH support; West reported consulting for the Flax Council. [Sauder et al.](https://onlinelibrary.wiley.com/doi/abs/10.1111/j.1469-8986.2011.01335.x).

The overnight mean was 49.375 bpm, compared with 49.5 the previous night; the minima were 47 and 45. Those summaries are separate from the evening readings. Earlier meals can be tested for sleep, comfort and functioning without making the lowest possible bedtime pulse the success criterion.

## How much confidence is justified?

Independent 2025 work compared Gen3 and Ring 4 with a Polar H10 electrical chest strap. Thirteen people contributed 536 nights overall; Ring 4 had 138 usable RHR nights. Mean absolute percentage error was 1.94% for nocturnal RHR and 5.96% for HRV, with considerable variation between nights. AFRL funded it; authors declared no competing interests. This supports those tested nightly summaries, not Ring 5 or PACE 4 accuracy. [Dial and colleagues](https://pmc.ncbi.nlm.nih.gov/articles/PMC12367097/).

The current product's “99%” HR headline is an r-squared claim citing older research. The original 2020 paper describes second-generation hardware and 49 analyzed nights, with Oura employment and equipment support disclosed. Correlation is not the fraction of readings within a chosen bpm error. [Original paper](https://oulurepo.oulu.fi/bitstream/handle/10024/28178/nbnfi-fe2020091869988.pdf?isAllowed=y&sequence=1), [product footnote](https://ouraring.com/store/rings/oura-ring-5).

A separate Gen3 investigation found HRV agreement depended on signal-quality filtering and improved with longer aggregation. Aggressive filtering also discarded data. A clean-looking average can therefore conceal missing periods. [Signal-quality study](https://pmc.ncbi.nlm.nih.gov/articles/PMC11644394/).

## The target

Develop a repeatable personal series, then examine changes in relation to training, sleep, illness and functioning. We have not selected a personal HRV maximum or HR minimum as the sleep goal. A change earns its interpretation from the circumstances and relevant outcomes, not its direction alone.

For comparisons, specify the HRV statistic, interval length, selected sleep episode, valid coverage, artifact handling and aggregation. Keep each device as a named series. Do not splice the highest HRV or lowest HR into a composite result.

## Reference choices

A validated electrical chest strap offers a practical comparison for HR and beat intervals; ECG provides a clinical or research reference when the question requires it. A 2026 H10 study directly compared raw intervals with laboratory ECG in 43 healthy young adults and found excellent agreement in its short resting/reflex protocol. It does not make every recording app, exercise setting or overnight implementation equivalent. [Blalock and colleagues](https://pubmed.ncbi.nlm.nih.gov/42275859/).

The first comparison should use simultaneous measurements and matched processing. A morning spot measurement cannot validate an overnight mean from hours earlier. [Validation plan](/sleep/research/measurement-and-validation/#heart-rate-and-beat-intervals).

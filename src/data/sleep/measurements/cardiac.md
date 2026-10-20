---
title: "Heart rate and heart-rate variability"
description: "Overnight pulse and beat-interval measurements can track change, provided their sampling and definitions remain visible."
updated: "2026-10-20"
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

Before the [16 October sleep](/sleep/record/#night-2026-10-16), I reported pulse in the high 40s, the lowest personally recalled while awake. After synchronization the focused Oura query returned **47 bpm at 23:53:59 and 48 bpm at 23:59:15**, both labelled awake. These samples support the reported range, without establishing a continuous resting-HR curve or an independently verified lifetime minimum. The half-hour sample medians declined from 60.5 to 56 bpm, with irregular coverage. Overnight mean HR was 49.125 bpm and minimum 45; average HRV was 51 ms versus 58 the preceding night. The later COROS retrieval returned **56 ms official sleep HRV**, compared with 55 the preceding night. Its daily snapshot reported average HR 52 bpm and minimum 43, while predicted seated resting HR was 51; those scopes do not match Oura’s sleep-window HR. These scopes remain distinct; a meal effect has not been isolated.

## The social-night exception and a provider-returned range

On [17 October](/sleep/record/#night-2026-10-17), after the reported hard workout, late food, vodka and uncomfortable floor sleep, Oura returned mean sleeping HR **63.625 bpm** and minimum **56**, versus 49.125 and 45 the preceding night. Its sleep HRV fell **51 → 28 ms**. COROS official sleep HRV fell **56 → 32 ms** and was labeled **Below normal**, with an explicitly returned **42–64 ms normal range and 53 ms baseline**. These are COROS’s own assessment values, not thresholds reconstructed from our few earlier observations. Its normal range comes from previous nights and is not a diagnostic boundary or a range to apply to Oura. [COROS definition](https://support.coros.com/hc/en-us/articles/20959044334612-Overnight-HRV).

The cardiac change accompanies a shorter, subjectively uncomfortable night. Training, meals, alcohol, timing and sleeping conditions changed together; their isolated contributions remain unresolved. COROS’s daily HR snapshot of 71 bpm average and 52 minimum, with predicted seated resting HR of 59, retains its different scope. A return toward the familiar series over subsequent ordinary nights would be informative; this one record does not establish an arrhythmia or a new long-term baseline.

## The following long night

On [18 October](/sleep/record/#night-2026-10-18), Oura’s sleep-HR mean returned from **63.625 to 51.625 bpm**, with minimum **46 versus 56**. Its average sleep HRV rose **28 → 59 ms**; COROS’s official sleep HRV rose **32 → 61 ms**, now labeled **Normal** with a returned **44–64 ms range and 54 ms baseline**. Each day retains its own provider-supplied range; the earlier 42–64 range and baseline 53 remain in the October 17 record. A change in provider reference values does not justify silently rewriting history.

This follows a much longer sleep episode, after food around 20:00, gym ending 22:00 and a midnight sleep attempt. It is a return toward earlier readings across one subsequent night, not proof that one exposure caused the change or that full recovery is complete. COROS’s daily-average HR snapshot was **53 bpm**, daily minimum **45**, and predicted seated resting HR **55**; these remain separate from Oura’s selected sleep-window mean and minimum. The October 18 follow-up reports feeling awake on waking; later-day experience remains unreported. It also retrospectively describes October 17 as feeling good despite that night’s lower HRV and grades.

## October 19: lower sleeping pulse, higher HRV

The [October 19 record](/sleep/record/#night-2026-10-19) returned Oura mean sleeping HR **47.625 bpm**, minimum **44**, and average sleep HRV **69 ms**. COROS official sleep HRV was **67 ms**, labeled **Above normal** against its returned **46–66 ms range and 56 ms baseline**. Its daily snapshot averaged 53 bpm with minimum 42, while predicted seated resting HR was 53. Each retains its own scope and provider assessment; the COROS label is not a diagnosis or a range to apply to Oura.

This follows reported stressful activity before bed, with sleep described as okay and multiple brief remembered awakenings. Those conditions do not contradict the measurements, but their isolated effects are unresolved. The ring configuration now reports **firmware 2.1.36**, previously 2.1.25, with the sleep algorithm field still v2. Exact update timing and any effect on the estimates are unknown, so the version boundary remains part of the interpretation. The October 19 follow-up reports feeling pretty sleepy initially and back to normal speed within 10–15 minutes; later-day experience remains unreported.

## October 20: cardiac summaries and the experienced night

On [October 20](/sleep/record/#night-2026-10-20), Oura mean sleeping HR was **47 bpm**, minimum **43**, and average sleep HRV **70 ms**. COROS official sleep HRV was **71 ms**, labeled **Above normal** against its returned **47–69 ms range and 58 ms baseline**. Its daily snapshot averaged 52 bpm with minimum 42; predicted seated resting HR was 49. These scopes remain distinct. Firmware 2.1.36 and sleep algorithm v2 match the preceding retrieval.

The diary describes okay-ish sleep, many brief remembered awakenings and plentiful dreams. High HRV and a lower sleeping pulse do not erase that experience or establish complete recovery. The follow-up reports waking around 09:30 feeling super sleepy, then an unsuccessful 5–10-minute attempt to sleep more. A second follow-up clarifies feeling normal within 10–15 minutes; sustained later-day function remains unreported. No snoring or breathing symptoms were known to the user, which is not a negative clinical test. The reported roughly 5½-hour meal gap and unquantified later sips have not been isolated as explanations for the measurements.

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

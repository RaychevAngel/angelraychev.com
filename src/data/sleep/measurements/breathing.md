---
title: "Breathing rate and oxygen signals"
description: "Respiratory rate, optical oxygen estimates and breathing-disturbance indices answer different questions."
updated: "2026-10-13"
order: 7
role: "Monitor"
attention: "Clarify the index and validate persistent changes"
---

## Three separate signals

**Respiratory rate** is breaths per minute. **SpO₂** is an optical estimate of oxygen saturation. **Oura's Breathing Disturbance Index (BDI)** is derived from detected drops in the SpO₂ time series. They should remain separate fields.

Oura derives nighttime respiratory rate from its pulse signal, using breathing-related modulation of beat intervals. It is not directly measuring airflow. Oura notes that airflow obstruction may not always match the pattern inferred from the pulse. [How Oura estimates respiratory rate](https://ouraring.com/blog/respiratory-rate/).

## The first observation

For October 13, the API returned **12.375 breaths/min**, **95.244% average SpO₂**, and **BDI 3**. Displaying the first two as 12.4 and 95.2 preserves readable precision while retaining the original values in the record. These are a single night's estimates, not a diagnosis or personal baseline. [First record](/sleep/record/#night-2026-10-13).

The downloaded official API schema defines BDI as an integer or null, calculated from detected SpO₂ drops, with values in [0,100]. It does not specify the desaturation threshold, duration, rounding or per-hour unit. [Oura API documentation](https://cloud.ouraring.com/v2/docs).

Oura's 2026 enterprise case study describes BDI generally as the average detected disturbances per hour of sleep. The exact correspondence between that enterprise description and this public integer field is not established here. We therefore keep **BDI 3**, rather than relabeling it three clinically scored respiratory events per hour. [Oura's enterprise description](https://ouraring.com/blog/how-essence-healthcare-uses-oura/).

**BDI is not the clinical apnea–hypopnea index (AHI).** AHI requires a specified respiratory-event scoring procedure. The ring's average oxygen value and BDI cannot establish that sleep apnea is absent or present.

## Evidence and measurement limits

Oura's older manufacturer analysis described respiratory-rate agreement with ECG-derived respiration in 43 young participants. That is historical evidence using another derived signal, not verified Ring 5 accuracy against directly measured airflow. [Manufacturer analysis](https://ouraring.com/blog/how-accurate-is-ouras-respiratory-rate/).

Oura's oxygen-sensing documentation describes overnight averages and oxygen-variation patterns. Ring fit, movement and signal quality affect interpretation. An average alone also cannot reveal the timing or depth of brief drops. We have not verified an independent Ring 5-specific validation of oxygen saturation or BDI. [Oxygen feature explanation](https://ouraring.com/blog/blood-oxygen-sensing-spo2/).

## What to strive toward

Establish coverage and a personal pattern, document persistent unexpected changes, and resolve uncertainty when it matters. Do not pursue ever-lower respiratory rate or 100% oxygen as competitive endpoints. A better measurement or a resolved breathing problem can be an achievement even if a rounded nightly average scarcely changes.

The physiological aim is adequate ventilation and oxygenation without meaningful breathing-related disruption. A future validated assessment can make that aim more specific. The public ring index does not yet supply a clinical event target for this notebook.

If symptoms or persistent concerning patterns create a clinical breathing question, the appropriate reference is a clinician-selected respiratory study. AASM guidance describes PSG or technically adequate home sleep-apnea testing for appropriate patients; a consumer score is not a substitute. Testing should answer that question, rather than be ordered merely to populate the notebook. [AASM diagnostic guideline](https://aasm.org/resources/clinicalguidelines/diagnostic-testing-osa.pdf).

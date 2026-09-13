---
layout: "../../layouts/Post.astro"
title: "Rectangle searches: manuscript and evidence"
description: "The rectangle capture-time manuscript, fixed-size numerical completion criterion, sources and exact proof boundaries."
updated: 2026-09-13
---

Angel Ivanov Raychev · September 2026

**Research manuscript in preparation. The full fixed-size closed-form rectangle classification remains open. No Princess paper has been submitted to arXiv.**

[Read the rectangle paper](/princess/princess-searches.pdf) · [LaTeX sources](/princess/manuscript-source.zip) · [Mathematical sources and evidence](/princess/research-sources.zip)

[Overview](/princess/) · [Manuscript-derived proofs](/princess/proofs/) · [Exact coverage and gaps](/princess/coverage/) · [Lean coverage](/princess/lean/) · [Parked extensions](/princess/extensions/)

## Fixed scope and completion criterion

For every rectangular board with positive side lengths $a,b$ and constant daily inspection budget $k$, determine $T_k(a,b)$ from full initial uncertainty. Inspections are simultaneous; after each miss the target must traverse one edge. The answer is the minimum worst-case guaranteed number of days, with infinity for infeasibility. Rotation gives $T_k(a,b)=T_k(b,a)$.

The numerical goal is a **fixed-size closed-form expression using an absolute $O(1)$ number of standard numerical operations, independent of $a,b,k$**. Fixed finite cases, arithmetic, powers, roots, floors and ceilings are allowed. A recurrence, parameter-length sum, iterative array, shortest-path calculation or parameter-dependent preprocessing is an intermediate result. Such an algorithm cannot be concealed inside a newly named operation. This is an operation-count goal, not a claim of constant bit complexity or a theorem that the desired expression must exist.

There is a separate requirement of directly specified optimal inspections and proofs of capture and minimality. Printing all days need not take constant time. The [scope document](/princess/scope.md) records these obligations, including the no-inspection convention and the independent formalization requirement.

## What this manuscript contains

The core retains all rectangle results: complete formula families on paths and widths through five; additional fixed-width formulas; the uniform high-budget formulas for each side parity; exact neighborhood profiles; the all-odd minimum-budget law; bounded odd evaluation; and the physical boundary framework for even-area boards. General lemmas, partial-state inequalities and counterexamples remain when they support the rectangle objective.

Several exact results fall short of the corrected numerical criterion. The all-odd minimum-budget constant still requires a width-dependent clock. The eventual solo criterion still requires scalar evaluation whose operation count grows with width. The even-area representation still requires parameter-dependent boundary optimization. These achievements are preserved as exact intermediate results, with their strategy and proof status identified in the [reconciliation](/princess/coverage/).

The inverse fixed-deadline problem minimizes a constant daily budget and describes the same rectangle capture relation. Relevant rectangle consequences and supporting transfer arguments remain in scope. Independent higher-dimensional applications, cube classifications and general-cylinder extensions are preserved in the [parked companion](/princess/extensions/), with their own PDF, sources, demonstrations and formal guide.

This release performs **scope separation and reassessment, not mathematical unification**. It introduces no newly solved parameter range. The previous [128-page combined release](/princess/archive/2026-09-13-combined/) is frozen with its original files and checksums; its broader objective and recurrence-based descriptions are historical.

## Proof and verification boundaries

Paths and two-row grids have complete physical-game Lean proofs. The wider rectangle formulas and recent geometric arguments have reviewed ordinary proofs, with individual arithmetic and semantic components verified in Lean. The independently verified cube classifications are now presented with the companion. An aggregate count of checked modules is not a formal proof of the general rectangle theorem.

- [Rectangle Lean package](/princess/lean-proofs.zip)
- [Exact module roles and shared dependencies](/princess/lean-scope.json)
- [Source-specific compiler receipt](/princess/lean-verification.json)
- [Current PDF and archive checksums](/princess/release.json)
- [Bibliography](/princess/references.bib)

The proof pages are generated from the same sources as the manuscripts. Current compilation, dependency and link checks are distinguished from historical computational evidence; source hashes identify which formal statements were actually checked.

## Provenance and credit

The original path work dates to **October 2019–March 2020**. The historical [student-conference manuscript](/princess/raychev-rusev-2020-student.pdf) lists Angel Raychev and Dimitar Rusev; the [spring-conference manuscript](/princess/raychev-2020-spring.pdf) lists Angel Raychev. Their original authorship is preserved.

Dimitar Rusev contributed the exposition of Section 3 of the earlier joint manuscript. With his agreement, his contribution is acknowledged in the revised account. I thank my mathematics teacher and mentor **Dimitar Dimitrov** for encouraging my early mathematical research and providing guidance and support.

The September 2026 investigation and proof development used substantial assistance from **Astra 6 through the Codex harness**, including mathematics, counterexample searches, computation, formalization and exposition. This contribution went beyond editing. Angel Raychev directed the investigation and retains responsibility for the manuscript. The [research history](/princess/research-history.md) distinguishes original work, reconstructed arguments, prior literature and later development.

No new claim of literature priority follows merely from deriving a result here. Literature review and final publication preparation remain separate work.

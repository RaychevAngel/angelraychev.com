---
layout: "../../layouts/Post.astro"
title: "Rectangle searches — manuscript and resources"
description: "The 29 October 2026 manuscript, proof sources, two-day uniform bound and precise Lean coverage."
updated: 2026-10-29
---

Angel Ivanov Raychev · checkpoint of 29 October 2026

**Research manuscript in preparation. The proved computable bounds have a gap at most two everywhere. Global gap zero and the fixed-size numerical expression remain open. No Princess paper has been submitted to arXiv.**

The [overview](/princess/) supplies the selected PDF and Lean guide through the shared publication header. Its [Resources](/princess/#resources) section collects buildable LaTeX, proof evidence, companions and archived versions.

[Current checkpoint](/princess/checkpoint/) · [Readable proofs](/princess/proofs/) · [Exact coverage](/princess/coverage/) · [Remaining gaps](/princess/gaps/) · [Lean coverage](/princess/lean/)

## What this release adds

The manuscript integrates the two-day whole-domain bracket, exact capture at every budget and every even length for odd widths at least 8,193, and the new paired-boundary construction. Actual strategies with matching lower bounds establish the 285-day and 413-day examples that disprove universal optimality of the older fixed-corner construction. A partial-state arrival counterexample records the remaining reachability obstacle.

The [checkpoint](/princess/checkpoint/) gives exact parameter guards and evidence levels. The [source supplement](/princess/checkpoint-sources-2026-10-29.zip) preserves proofs, dependencies, independent reviews, exact checks and failed approaches. The [previous public PDF](/princess/archive/2026-10-24-pre-october29-release/princess-searches.pdf) remains a dated archive.

One new Lean module proves conditional paired compression and real-history overlap preservation. Its claims are separate from the ordinary proofs of the new capture-time theorems.

## Fixed scope and completion criterion

The game starts with full uncertainty on a two-dimensional rectangle. Inspections are simultaneous; after each unsuccessful day the princess must traverse exactly one edge. The target quantity $T_k(w,n)$ is the minimum worst-case guaranteed capture time, including infinity for infeasibility. Relevant constant-budget inverse-deadline consequences remain in scope.

The immediate priority is matching computable lower and constructive upper bounds for every feasible $w,n,k$. Recurrences, finite-state calculations and parameter-dependent preprocessing are acceptable intermediate results. General numerical simplification is deferred until those bounds match throughout the domain.

The ultimate numerical goal remains a **fixed-size expression using an absolute $O(1)$ number of standard numerical operations independent of $w,n,k$**. Fixed finite cases, arithmetic, powers, roots, floors and ceilings are allowed. A variable recurrence, sum, iterative array, shortest path or preprocessing computation cannot be concealed inside a newly named atomic operation. This is an operation-count goal, not constant bit complexity or a claim that such an expression must exist.

Directly specified optimal inspections, guaranteed capture and minimality are separate requirements. Printing all days need not take constant time. The [scope document](/princess/scope.md) includes the no-inspection convention and the independent formalization obligation.

## Earlier achievements retained in the manuscript

The main manuscript retains the complete formulas for paths and widths through five, every seven-row odd-length budget, the three uniform high-budget formula regions, the even-width family $k=b(b-1)$, the all-odd minimum-budget law, exact neighborhood profiles, bounded odd evaluation, and the physical boundary framework for even-area boards. Its earlier one-day comparisons and independently certified finite equalities remain valid. Older bounds are strengthened by taking the maximum lower and minimum upper, never by discarding a better proved result.

The all-odd minimum-budget constant still uses a width-dependent clock. Exact odd joint evaluation can still select inspections by optimization outside the direct scalar regions. The general even-area representation still requires parameter-dependent boundary optimization. These remain substantial intermediate results, with distinct value, evaluation and construction boundaries. The [coverage assessment](/princess/coverage/) gives their exact ranges; the [reconciliation](/princess/reconciliation/) separates new progress from what was already known at the fixed-scope baseline.

The latest paired-boundary construction retains actual arrival times, phases and inherited overlap. Its remaining generalization is a uniform reachability or impossibility theorem at every unresolved deadline. The [gap assessment](/princess/gaps/) records current limitations and failed approaches.

Independent higher-dimensional applications, cube classifications, varying-budget classifications and general-cylinder extensions remain in the [parked companion](/princess/extensions/), with their proofs, sources, demonstrations and formal guide. Shared lemmas needed for rectangles remain in the main project. The [previous combined release](/princess/archive/2026-09-13-combined/) remains frozen. Separating those applications was scope selection; the new common-history proofs are mathematical consolidation. This publication pass does not resume the parked work.

## Proof and verification boundaries

Paths and two-row grids have complete physical-game Lean proofs at positive budgets. Wider-board statements have reviewed ordinary proofs and selected formally verified supporting components. **The global two-day bound and wider exact families remain ordinary proofs. The new PairedCompression module verifies an abstract supporting theorem, not those classifications.** The former symbolic candidate has since passed the independent checks recorded in the current source supplement.

- [Rectangle Lean package](/princess/lean-proofs.zip)
- [Exact module roles and shared dependencies](/princess/lean-scope.json)
- [Source-specific compiler receipt](/princess/lean-verification.json)
- [Current PDF and archive checksums](/princess/release.json)
- [Bibliography](/princess/references.bib)

The proof pages are generated from the same sources as the manuscripts. Publication checks confirm the compilation, links and packaged sources; they do not turn a candidate into a theorem. Compiler receipts identify the actual formal sources checked, not a blanket verification of the general rectangle classification.

## Provenance and credit

The original path work dates to **October 2019–March 2020**. The historical [student-conference manuscript](/princess/raychev-rusev-2020-student.pdf) lists Angel Raychev and Dimitar Rusev; the [spring-conference manuscript](/princess/raychev-2020-spring.pdf) lists Angel Raychev. Their original authorship is preserved.

Dimitar Rusev contributed the exposition of Section 3 of the earlier joint manuscript. With his agreement, his contribution is acknowledged in the revised account. I thank my mathematics teacher and mentor **Dimitar Dimitrov** for encouraging my early mathematical research and providing guidance and support.

The September–October 2026 investigation used substantial assistance from **Astra 6 through the Codex harness**, including mathematics, counterexample searches, computation, formalization and exposition. This contribution went beyond editing. Angel Raychev directed the investigation and retains responsibility for the manuscript. The [research history](/princess/research-history.md) distinguishes original work, reconstructed arguments, prior literature and later development.

No new claim of literature priority follows merely from deriving a result here. Literature review and final publication preparation remain separate work.

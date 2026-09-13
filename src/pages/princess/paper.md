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

The core retains all rectangle results: complete formula families on paths and widths through five; additional fixed-width formulas; the uniform high-budget formulas for each side parity; exact neighborhood profiles; the all-odd minimum-budget law; bounded odd evaluation; and the physical boundary framework for even-area boards. New corner, erosion and localization theorems strengthen the lower bounds and yield further exact finite cases. General lemmas, partial-state inequalities and counterexamples remain when they support the rectangle objective.

Several exact results fall short of the corrected numerical criterion. The all-odd minimum-budget constant still requires a width-dependent clock. The eventual solo criterion still requires scalar evaluation whose operation count grows with width. The even-area representation still requires parameter-dependent boundary optimization. These achievements are preserved as exact intermediate results, with their strategy and proof status identified in the [reconciliation](/princess/coverage/).

The inverse fixed-deadline problem minimizes a constant daily budget and describes the same rectangle capture relation. Relevant rectangle consequences and supporting transfer arguments remain in scope. Independent higher-dimensional applications, cube classifications and general-cylinder extensions are preserved in the [parked companion](/princess/extensions/), with their own PDF, sources, demonstrations and formal guide.

The earlier scope separation and the new mathematical consolidation are distinct. Moving independent higher-dimensional results to the companion set the paper's boundary. The new shared corner and localization arguments genuinely replace several isolated restrictions and history calculations within the rectangle problem. The previous [128-page combined release](/princess/archive/2026-09-13-combined/) remains frozen with its original files and checksums; its broader objective and recurrence-based descriptions are historical.

## New results in this checkpoint

The finite-board corner bounds now include the critical expansion size, with explicit exceptions. An erosion refinement also records how many opposite-color corners have both neighboring rooms still possible. This extra information distinguishes room arrangements that have the same cardinality and the same occupied corners. On odd-width, even-length boards, a new localization theorem applies throughout an interval of sizes near the pronic capacity, rather than only at exact equality. Its resulting transition restriction is already represented by the erosion count, so the eleven-row argument needs no additional history bit. See the [critical bound](/princess/proofs/#cor:critical-corner-unified), [erosion theorem](/princess/proofs/#thm:erosion-corner-profile), and [localization and dual rule](/princess/proofs/#cor:dual-near-pronic).

A reviewed [merger theorem](/princess/proofs/#thm:erosion-model-merger) preserves the enriched restrictions while combining the two checkerboard groups into one necessary lower-bound calculation. It proves an impossibility tool; physical attaining strategies remain a separate part of each equality proof. The [overview](/princess/) illustrates the geometric obstruction with the new corner-localization figure.

The [finite-cases theorem](/princess/proofs/#thm:even-area-finite-certificates) establishes:

- $T_5(8,8)=40$ and $T_7(12,12)=72$.
- $T_4(7,8)=68$ and $T_5(9,10)=96$.
- $T_6(11,12)=128$ and $T_6(11,14)=172$.

Every equality combines proved geometric restrictions, checked finite integer calculations, and a matching inspection sequence replayed on the actual board. These numerical certificates settle the displayed cases; they do not establish an all-width time formula. On the larger square, a separately reviewed geometric and equality-case argument gives **$206\le T_{13}(24,24)\le207$**. The upper bound is a checked 207-day physical search. The remaining one-day choice is open. [Proof of the interval](/princess/proofs/#cor:twenty-four-full-bracket).

The envelope constructions now give explicit upper bounds at **every feasible budget on every even-area rectangle**. Their numerical expressions are the same quotient-and-remainder expressions as in the high-budget theorems. The equality thresholds have not moved: for shorter side $2b$, equality is proved at $k\ge\max\{b+1,b(b-1)+1\}$; for shorter side $2b+1$ and even length, it is proved at $k\ge b(b+1)+1$. Below those thresholds the constructions are upper bounds. The all-odd high-budget equality threshold remains $b^2+1$. [Even-width construction](/princess/proofs/#thm:even-rectangle-high-budget) · [Odd-width, even-length construction](/princess/proofs/#thm:odd-short-even-high-budget).

At the minimum budget on odd-width, even-length boards, the same width-clock expression $2wn-C_w$ as for odd lengths is now a proved physical upper bound. Its matching lower bound for every width and even length remains open. Evaluating the width clock with an absolute $O(1)$ operation count is another unresolved obligation. The exact finite results above do not remove either gap.

## Proof and verification boundaries

Paths and two-row grids have complete physical-game Lean proofs. The wider rectangle formulas have reviewed ordinary proofs, with some supporting arithmetic and semantic components verified in Lean. **The new corner, erosion, localization, merger and finite-case results have ordinary proofs and computational evidence; they add no Lean theorem in this checkpoint.** The independently verified cube classifications are presented with the companion. An aggregate count of checked modules is not a formal proof of the general rectangle theorem.

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

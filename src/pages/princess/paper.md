---
layout: "../../layouts/Post.astro"
title: "Rectangle searches — resources"
description: "The October 2026 rectangle checkpoint: proved uniform bounds, exact families, the unverified candidate, and precise formal coverage."
updated: 2026-10-24
---

Angel Ivanov Raychev · checkpoint of 24 October 2026

**Research manuscript in preparation. The accepted computable bounds differ by at most four days for every feasible rectangle. Uniform gap zero and the full fixed-size numerical expression remain open. No Princess paper has been submitted to arXiv.**

The [overview](/princess/) provides the selected PDF and Lean guide. Its [Resources](/princess/#resources) section collects LaTeX, companions and previous versions. The [mathematical evidence archive](/princess/research-sources.zip) supports the account below.

[Overview](/princess/) · [Current checkpoint](/princess/checkpoint/) · [Progress reconciliation](/princess/reconciliation/) · [Manuscript-derived proofs](/princess/proofs/) · [Exact coverage and gaps](/princess/coverage/) · [Lean coverage](/princess/lean/) · [Parked extensions](/princess/extensions/)

## What is proved at this checkpoint

For every rectangle with shorter side $w$, longer side $n\ge w$, and every feasible constant daily budget $k\ge\lfloor w/2\rfloor+1$, the accepted bounds satisfy

$$L_k(w,n)\le T_k(w,n)\le U_k(w,n),\qquad U_k(w,n)-L_k(w,n)\le4.$$

The lower applies to arbitrary physical searches; the upper is supplied by actual inspections. This improves the preceding uniform eight-day ceiling. Every even width $w\ge64$ has gap at most two at every length and feasible budget. Odd widths $w=2b+1\ge65$ with even length also have gap at most two for $k\ge2b$. Widths at most 64 retain the earlier three-day ceiling, and every stronger exact or one-day result is retained. Odd-by-odd rectangles retain their earlier exact joint evaluator.

Two new exact families have attaining physical constructions:

- For $w=2b$, $b\ge32$, and $k=b+d$, every length is exact when $d=1$; for $2\le d\le b-1$, exactness holds when $n\ge2b+2d-2$. The value is $J(k)+J(\lfloor k/2\rfloor)+1$, with $J$ an explicit recurrence and finite endpoint minimum. Selecting minimizing endpoints selects the physical reflection-transport construction. This is still parameter-dependent optimization over endpoints.
- For $w=2b+1$, $n=2\ell\ge w$, and $k=b+d$, exactness holds when $d\ge1$, $b\ge4d+8$, and $(2b+1)(\ell-b)>2d^2$. The value is $P(k)+P(\lfloor k/2\rfloor)+1$, with $P$ the physical prefix recurrence and a prescribed concatenation/palindrome strategy. It covers every admissible length if also $b\ge d^2$, including minimum budget on every odd width at least 25 and every even length.

Under the same natural guard $b\ge4d+8$, a stronger odd-width criterion uses the actual central span $G$ of the capped recurrence: with $h=wn/2$, require $h-k-2b^2>2G(d-1)+d$. The proof gives $1\le G\le d$; a computed $G\le3$ suffices at every length under the natural guard. It does not assert $G\le3$ for every input.

These are reviewed ordinary results with their stated arithmetic certificates and physical constructions. Their recurrence evaluations are not fixed-size numerical expressions. Their full physical-game theorems have not been added to Lean. The [checkpoint page](/princess/checkpoint/) provides the precise accepted statements and [frozen proof/review bundle](/princess/checkpoint-sources-2026-10-24.zip).

## The unverified candidate is separate

A symbolic discovery for odd $w=2b+1$, $b\ge32$, even $n\ge w$, and $2\le d=k-b\le b-3$ closed 751 nondominated profiles in 850 processed states. It proposes a sharper middle comparison. Independent replay, primitive-table ranges, actual entrance and stopping conditions, and the physical full-gate interface remain outstanding. The budgets $d=b-2,b-1$ are outside its stated range.

**This is a candidate certificate, not an accepted theorem. It is not used in the four-day global bound, the two-day refinements, or any exact family.** The [separate candidate archive](/princess/unverified-comparison-candidate-2026-10-24.zip) preserves the discovery and failed earlier abstractions for a future verification pass.

## Fixed scope and completion criterion

The game starts with full uncertainty on a two-dimensional rectangle. Inspections are simultaneous; after each unsuccessful day the princess must traverse exactly one edge. The target quantity $T_k(w,n)$ is the minimum worst-case guaranteed capture time, including infinity for infeasibility. Relevant constant-budget inverse-deadline consequences remain in scope.

The immediate priority is matching computable lower and constructive upper bounds for every feasible $w,n,k$. Recurrences, finite-state calculations and parameter-dependent preprocessing are acceptable intermediate results. General numerical simplification is deferred until those bounds match throughout the domain.

The ultimate numerical goal remains a **fixed-size expression using an absolute $O(1)$ number of standard numerical operations independent of $w,n,k$**. Fixed finite cases, arithmetic, powers, roots, floors and ceilings are allowed. A variable recurrence, sum, iterative array, shortest path or preprocessing computation cannot be concealed inside a newly named atomic operation. This is an operation-count goal, not constant bit complexity or a claim that such an expression must exist.

Directly specified optimal inspections, guaranteed capture and minimality are separate requirements. Printing all days need not take constant time. The [scope document](/princess/scope.md) includes the no-inspection convention and the independent formalization obligation.

## Earlier achievements retained in the manuscript

The main manuscript retains the complete formulas for paths and widths through five, every seven-row odd-length budget, the three uniform high-budget formula regions, the even-width family $k=b(b-1)$, the all-odd minimum-budget law, exact neighborhood profiles, bounded odd evaluation, and the physical boundary framework for even-area boards. Its earlier one-day comparisons and independently certified finite equalities remain valid. Older bounds are strengthened by taking the maximum lower and minimum upper, never by discarding a better proved result.

The all-odd minimum-budget constant still uses a width-dependent clock. Exact odd joint evaluation can still select inspections by optimization outside the direct scalar regions. The general even-area representation still requires parameter-dependent boundary optimization. These remain substantial intermediate results, with distinct value, evaluation and construction boundaries. The [coverage assessment](/princess/coverage/) gives their exact ranges; the [reconciliation](/princess/reconciliation/) separates new progress from what was already known at the fixed-scope baseline.

The new common-cut argument retains the phases and unused allowance of one actual history. Accepted localized-erosion, phase-wall and overlap tools support it. They do not by themselves complete the remaining short-board proof. The static even-square separator analysis is unreviewed, and the conditional normalized $17/16$ overlap inequality has not been assembled with its finite-board physical premises. The [gap assessment](/princess/gaps/) records these limitations, failed approaches and the next dependencies.

Independent higher-dimensional applications, cube classifications, varying-budget classifications and general-cylinder extensions remain in the [parked companion](/princess/extensions/), with their proofs, sources, demonstrations and formal guide. Shared lemmas needed for rectangles remain in the main project. The [previous combined release](/princess/archive/2026-09-13-combined/) remains frozen. Separating those applications was scope selection; the new common-history proofs are mathematical consolidation. This publication pass does not resume the parked work.

## Proof and verification boundaries

Paths and two-row grids have complete physical-game Lean proofs at positive budgets. Wider-board statements have reviewed ordinary proofs and selected formally verified supporting components. **The October global bound, exact transport and natural-range families, phase-wall and overlap results add no complete physical-game Lean theorem in this checkpoint.** The symbolic candidate has not passed ordinary independent acceptance either.

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

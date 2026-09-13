---
layout: "../../layouts/Post.astro"
title: "Optimal searches for a moving target on paths and grids"
description: "Research manuscript, mathematical sources, formal proofs, and the history of the princess-search problem."
updated: 2026-09-13
---

Angel Ivanov Raychev · September 2026

**Research manuscript in preparation. Not submitted to arXiv.** The general problem remains open; the paper states exactly which families are resolved.

[**Read the paper (PDF)**](/princess/princess-searches.pdf) · [LaTeX sources](/princess/manuscript-source.zip) · [Mathematical sources and certificates](/princess/research-sources.zip)

Start with the [interactive overview](/princess/) to explore optimal schedules. The [complete proofs](/princess/proofs/) are generated from the manuscript, and the [Lean guide](/princess/lean/) distinguishes complete formal theorems from ordinary mathematical proofs.

## The problem and results

A princess occupies an unknown room. Each day we may inspect at most $m$ rooms. After an unsuccessful inspection she must move to an adjacent room. How many inspections per day suffice, and how many days are necessary to guarantee finding her?

The manuscript gives exact minimum-time formulas and explicit strategies for paths and for grids with two, three, four, or five rows, at every length and budget. The wider odd-rectangle formula covers width $w=2b+1\ge3$ and odd length $n\ge w$ when $m\ge b^2+1$. It also resolves every budget on the $3\times3\times3$, $4\times4\times4$, and $3\times4\times4$ boxes, and proves that five daily inspections take exactly $18n-36$ days on every $3\times3\times n$ box with $n\ge3$, of either parity.

Two further exact formulas are included: seven rows at five inspections take $2\lceil(7n-16)/3\rceil$ days for odd $n\ge7$, and $3\times3\times n$ at six inspections takes $6n-8$ days for even $n\ge4$. Both have independently reviewed ordinary proofs with finite certificates.

For every box whose side lengths are all odd, in any dimension, a geometric compression theorem reduces the search to two counts. This gives an exact algorithm for feasibility, minimum time, and an optimal strategy, with a number of states quadratic in the number of rooms. A related reduction applies to boxes with a side of length two. Other results provide smaller exact recurrences and explicit search constructions on further families.

The uniform results settle the exact single-color neighborhood profile on **every rectangle**, including odd-by-even and even-by-even boards. Explicit optimal-time formulas now cover all side-parity combinations above quadratic budget thresholds: $\max(b+1,b(b-1)+1)$ for shorter width $2b$, $b^2+1$ for width $2b+1$ at odd length, and $b(b+1)+1$ for width $2b+1$ at even length. Each formula has a physical construction and a matching lower bound against arbitrary strategies.

At **every feasible budget on an odd-by-odd rectangle**, an exact joint-state calculation selects between $2\tau-1$ and $2\tau$. Both its state bound and the number of arithmetic stages depend only on width and budget, not length. A stabilization theorem removes the need to iterate through every day. The implementation has independent comparisons against the full forward game and against unaccelerated evaluation. The criterion using only the two pure solo endpoints is now proved after an explicit width-and-budget-dependent onset. Its remaining open range is shorter rectangles at intermediate budgets; any counterexample at fixed width $2b+1$ has length $O(b^4)$.

For **every even-area rectangle**, a new geometric theorem represents the exact optimum by bounded-duration transitions between physical boundary shapes. It allows arbitrary possible-position sets inside each transition. A finite local table describes the boundary choices. Every interior connection has an explicit endpoint-height weight, so a fixed-size graph gives the exact answer in a bounded number of integer arithmetic stages in the length, after preprocessing depending on width and budget. Integer bit lengths still grow logarithmically with the length. The theorem also applies to a bipartite Hamiltonian cross-section $Q$ with $|Q|\ge2$, budget $m>|Q|/2$, and a cylinder of even order. The generic preprocessing has not been implemented and can be very large. Its principal contribution is an exact geometric representation and constructive optimal-strategy recovery, not an asymptotic improvement over the earlier effective eventual-period theorem.

The manuscript places the general time formulas before their narrow-width applications. General theorems replace overlapping three-row, four-row, and five-row proof arguments. The stronger partial-state statements and the lower-budget obstructions are retained. The exact middle-interval transfer, a two-candidate root optimization, and a graph-theoretic inspection-localization lemma have Lean proofs; the new full rectangle geometry and time theorems have independently reviewed ordinary proofs.

A single enlargement-and-erosion lemma now supplies both even-area rectangle constructions. It applies to every finite connected bipartite cross-section with at least two vertices, and permits arbitrary terminal supports when their predecessor closure fits the inspection allowance. Its sharper occupied-root distance threshold lowers the even-width requirement to $\max(b+1,b(b-1)+1)$, including every four-row budget; the earlier all-fiber threshold is retained as a separate geometric fact. This is a stronger construction theorem, not an assumption that pyramid-shaped terminal sets are always optimal.

These algorithms are proved for unbounded families. They do not yet amount to explicit formulas for every box and every budget. The literature discussion identifies prior results, and new derivations are not automatically claimed as new to the literature.

The five-inspection formula for $3\times3\times n$ now covers both parities. The even-length proof classifies critical boundaries using a113-state finite certificate, records whether the preceding survivor was critical, and matches its lower bound with a direct prefix sweep. It is an ordinary unbounded proof with independent geometry and strategy audits; only the single $3\times3\times3$ member is fully formalized in Lean.

At the minimum budget $m=b+1$, **every odd width** $w=2b+1\ge3$ and every odd length $n\ge w$ has exact time $2wn-C_w$, where $C_w=8b^2-4b-4L_b+4$. The width-only clock $L_b$ is evaluated by an explicit recurrence, equivalently by an $O(b)$-stage solo calculation. This supersedes the earlier seven-width list without assuming an elementary formula for the width constant.

One quadrant theorem now supplies the square, pronic, and omitted-corner bounds: $C_h(s)=\max\{s(s-1)/2,s(s-h)\}$ is the exact capacity after initial diagonals have been forbidden. Conditional half-strip profiles and triangle-localization theorems show why efficient survivors cannot switch corners immediately. The general two-candidate optimization of these capacities is verified in Lean; their physical isoperimetric interpretation has an independently reviewed ordinary proof.

For a single unbounded scalar growth process, the minimum total inspections and minimum duration for every feasible target have one greedy reverse recurrence, valid for a general cyclic family of nondecreasing surjective maps. A suffix exchange also consolidates mixed histories while their primary process stays above the lower square-root bands. Neither theorem is claimed to solve the remaining shared-budget packing problem.

For any fixed odd-sided cross-section, in any dimension, and any fixed sufficient daily budget, sufficiently long odd buildings obey an exact periodic time rule: adding a specified number of floors always adds a specified number of search days. The theorem gives explicit thresholds and a finite procedure to determine the constants. At the minimum budget the eventual rule is linear, with two days per added room. This is proved by a stable decomposition of the two ends and insertion or removal of a central segment of an optimal strategy.

The parity bridge extends eventual affine periodicity to **every fixed rectangular cross-section and both longitudinal parities**. For a cross-section with $A$ rooms and fixed budget $m>A/2$, the leading term is $2An/(2m-A)$. A finite family of efficient boundaries and a protected physical interval let us edit an arbitrary optimal strategy. A one-bit history variable handles the alternating expansion costs when the cross-section has odd order and the growing side is even. Writing $D=2m-A$ and $g=\gcd(A,D)$, the exact eventual rule is $T_m(n+2D/g)=T_m(n)+4A/g$. The proof supplies a polynomial sufficient onset bound by constructing boundary paths directly from their endpoint heights. At the minimum sufficient budget, the length period is two. The new interface theorem supplies a further geometric treatment of all finite lengths in its even-order scope. Simple formulas for all arbitrary boxes remain unresolved.

The reverse, fixed-deadline question also has a general theorem. For any fixed finite cross-section with $A$ rooms and a fixed deadline of $t$ days, the minimum budget is eventually $An/t$ plus a periodic correction. The proof uses a weighted finite-state column description and semilinear sets. This is distinct from fixing the daily budget and allowing the deadline to grow.

## Formal proof and reproducibility

The complete physical classifications for **paths, two-row grids, and the $3\times3\times3$ and $4\times4\times4$ boxes** are verified in Lean 4.33.1. Their statements quantify over arbitrary inspection schedules and legal target walks. The remaining graph classifications have ordinary proofs; individual abstract and arithmetic components also have Lean proofs. The latest full check passed 83 modules, using one compiler worker.

- [Lean source archive](/princess/lean-proofs.zip)
- [Theorem map and exact verification boundaries](/princess/lean/)
- [Source hashes and compiler receipt](/princess/lean-verification.json)
- [PDF and archive checksums](/princess/release.json)
- [Bibliography](/princess/references.bib)

## Research history and contributions

The path work originated between **October 2019 and March 2020**. The historical [student-conference manuscript](/princess/raychev-rusev-2020-student.pdf) lists Angel Raychev and Dimitar Rusev; the [spring-conference manuscript](/princess/raychev-2020-spring.pdf) lists Angel Raychev. Both are in Bulgarian. Their bibliographic authorship is preserved.

Dimitar Rusev contributed the exposition of Section 3 of the earlier joint manuscript. With his agreement, his contribution is acknowledged in the combined manuscript. I thank my mathematics teacher and mentor **Dimitar Dimitrov** for encouraging my early mathematical research and providing guidance and support.

The 2026 extension to grids and boxes was developed with substantial assistance from **OpenAI’s Astra 6 model, operating through the Codex harness**, including mathematical investigation, new proof arguments, counterexample searches, computations, Lean formalization, and manuscript preparation. This assistance went beyond editing. I directed the investigation and retain responsibility for the manuscript. The [research history](/princess/research-history.md) records the distinction between the original work, recovered arguments, established literature, and subsequent investigation.

## Citation

Angel Ivanov Raychev. *Optimal searches for a moving target on paths and grids*. Research manuscript in preparation, September 2026.

The title and scope may change before submission. No arXiv identifier has been assigned to this manuscript.

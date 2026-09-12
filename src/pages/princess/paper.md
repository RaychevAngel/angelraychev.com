---
layout: "../../layouts/Post.astro"
title: "Optimal searches for a moving target on paths and grids"
description: "Research manuscript, mathematical sources, formal proofs, and the history of the princess-search problem."
updated: 2026-09-12
---

Angel Ivanov Raychev · September 2026

**Research manuscript in preparation. Not submitted to arXiv.** The general problem remains open; the paper states exactly which families are resolved.

[**Read the paper (PDF)**](/princess/princess-searches.pdf) · [LaTeX sources](/princess/manuscript-source.zip) · [Mathematical sources and certificates](/princess/research-sources.zip)

Start with the [interactive overview](/princess/) to explore optimal schedules. The [complete proofs](/princess/proofs/) are generated from the manuscript, and the [Lean guide](/princess/lean/) distinguishes complete formal theorems from ordinary mathematical proofs.

## The problem and results

A princess occupies an unknown room. Each day we may inspect at most $m$ rooms. After an unsuccessful inspection she must move to an adjacent room. How many inspections per day suffice, and how many days are necessary to guarantee finding her?

The manuscript gives exact minimum-time formulas and explicit strategies for paths and for grids with two, three, four, or five rows, at every length and budget. The wider odd-rectangle formula covers width $w=2b+1\ge3$ and odd length $n\ge w$ when $m\ge b^2+1$. It also resolves every budget on the $3\times3\times3$, $4\times4\times4$, and $3\times4\times4$ boxes, and proves that five daily inspections take exactly $18n-36$ days on every $3\times3\times n$ box with $n\ge3$, of either parity.

For every box whose side lengths are all odd, in any dimension, a geometric compression theorem reduces the search to two counts. This gives an exact algorithm for feasibility, minimum time, and an optimal strategy, with a number of states quadratic in the number of rooms. A related reduction applies to boxes with a side of length two. Other results provide smaller exact recurrences and explicit search constructions on further families.

These algorithms are proved for unbounded families. They do not yet amount to explicit formulas for every box and every budget. The literature discussion identifies prior results, and new derivations are not automatically claimed as new to the literature.

The five-inspection formula for $3\times3\times n$ now covers both parities. The even-length proof classifies critical boundaries using a113-state finite certificate, records whether the preceding survivor was critical, and matches its lower bound with a direct prefix sweep. It is an ordinary unbounded proof with independent geometry and strategy audits; only the single $3\times3\times3$ member is fully formalized in Lean.

At the minimum budget $m=(w+1)/2$, every odd length $n\ge w$ has exact time $2wn-C(w)$ for each width $w=3,5,7,9,11,13,15$. The corresponding constants are $8,20,44,84,136,208,288$. A general interval-insertion proof extends exact rational certificates to all lengths; a single formula for all odd widths remains open.

For any fixed odd-sided cross-section, in any dimension, and any fixed sufficient daily budget, sufficiently long odd buildings obey an exact periodic time rule: adding a specified number of floors always adds a specified number of search days. The theorem gives explicit thresholds and a finite procedure to determine the constants. At the minimum budget the eventual rule is linear, with two days per added room. This is proved by a stable decomposition of the two ends and insertion or removal of a central segment of an optimal strategy.

The new parity bridge extends eventual affine periodicity to **every fixed rectangular cross-section and both longitudinal parities**. For a cross-section with $A$ rooms and fixed budget $m>A/2$, the leading term is $2An/(2m-A)$. A finite family of efficient boundaries and a protected physical interval let us edit an arbitrary optimal strategy. A one-bit history variable handles the alternating expansion costs when the cross-section has odd order and the growing side is even. Writing $D=2m-A$ and $g=\gcd(A,D)$, the exact eventual rule is $T_m(n+2D/g)=T_m(n)+4A/g$. The proof supplies a polynomial sufficient onset bound by constructing boundary paths directly from their endpoint heights. At the minimum sufficient budget, the length period is two. Exact finite exceptions and simple formulas for all arbitrary boxes remain unresolved.

The reverse, fixed-deadline question also has a general theorem. For any fixed finite cross-section with $A$ rooms and a fixed deadline of $t$ days, the minimum budget is eventually $An/t$ plus a periodic correction. The proof uses a weighted finite-state column description and semilinear sets. This is distinct from fixing the daily budget and allowing the deadline to grow.

## Formal proof and reproducibility

The complete physical classifications for **paths, two-row grids, and the $3\times3\times3$ and $4\times4\times4$ boxes** are verified in Lean 4.33.1. Their statements quantify over arbitrary inspection schedules and legal target walks. The remaining graph classifications have ordinary proofs; individual abstract and arithmetic components also have Lean proofs. The latest full check passed 77 modules, using one compiler worker.

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

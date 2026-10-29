---
layout: "../../layouts/Post.astro"
title: "Rectangle capture time: the 29 October checkpoint"
description: "A two-day uniform bracket, an all-budget exact range, actual boundary constructions, and precise remaining gaps."
updated: 2026-10-29
---

[Overview](/princess/) · [Coverage](/princess/coverage/) · [Remaining gaps](/princess/gaps/) · [Manuscript](/princess/paper/) · [Lean coverage](/princess/lean/)

**The proved lower and constructive upper bounds now differ by at most two days for every rectangle and every feasible constant budget. Global gap zero remains open.** This release incorporates the research completed on 29 October and preserves the previous public release as a dated archive.

## The whole-domain result

For $w\le n$ and $k\ge\lfloor w/2\rfloor+1$,

$$L_k(w,n)\le T_k(w,n)\le U_k(w,n),\qquad U_k(w,n)-L_k(w,n)\le2.$$

The lower bound applies to arbitrary inspection histories and the upper bound comes with real inspections. Retain the strongest lower and upper bounds across every accepted result. The improvement is from the last public four-day ceiling, through the subsequent private three-day ceiling, to two. It is not a claim that every individual instance improved by two days.

For odd $w=2b+1$ with $b\ge2$, even $n$, $b+1\le k<Z=wn/2-b^2$, and $0\le c\le k$, the new uniform comparison gives $\max(0,P(c)-1)\le g(c)\le P(c)$ between the unrestricted gate lower clock and the compatible physical-prefix clock. Writing $p=P(k)$ and $q=P(\lfloor k/2\rfloor)$ gives

$$\max(2p-1,2q-2)\le T_k(w,n)\le\min(2p+2,2q+1),\qquad q\in\{p,p+1\}.$$

This has width two. Widths one and three and the range $k\ge Z$ use retained exact formulas. The earlier even-width results cover all even widths, and odd-by-odd boards retain exact joint evaluation. Every stronger narrow-board, high-budget or finite certified result remains available.

## Every budget at every odd width at least 8,193, with even length

Let $w=2b+1$, $b\ge4096$, and let $n\ge w$ be any even length. Put $h=wn/2$ and $B=b(b+1)$.

- $k\le b$: impossible.
- $b+1\le k\le B$: $T_k(w,n)=P(k)+P(\lfloor k/2\rfloor)+1$, attained by the prescribed prefix/palindrome strategy.
- $B+1\le k<h$: the retained exact high-budget numerical formula applies.
- $h\le k<2h$: two days; $k\ge2h$: one day.

The theorem covers every allowed length, not just sufficiently long boards. The low- and middle-budget answer is recurrence-based and does not meet the final O(1)-operation criterion. A further exact band at $b\ge512$ and $3b\le k\le\lfloor15b/4\rfloor$ supplies additional smaller-width coverage.

The proof uses geometric history constraints and exact finite certificates, including a 924-signature tail reduction. That finite reduction represents its infinite parameter range; it is not merely a sample of boards. The [manuscript proofs](/princess/proofs/#sec:paired-boundary-checkpoint) state the dependencies and guards.

## Physical strategies that beat the old fixed-corner construction

$$T_{48}(64,93)=285,\qquad T_{72}(102,124)=413.$$

Both have matching lower bounds and actual whole-board inspection words checked by a separate bit-grid verifier that imports no discovery code. The older fixed-corner construction takes 286 and 414. Its universal optimality is therefore false.

The general construction joins an actual head and actual suffix through a middle interpolation, preserving their phase and shared overlap allowance. A paired raw-boundary sufficient criterion gives legal inspections when its endpoint, occupancy and regularity guards hold. It is not a classification of every reachable boundary shape.

A counterexample shows why the arrival premise cannot be dropped: on 12-by-12 with budget seven, a particular 22-cell proper-root notch has scalar estimate eight updates but actual arrival ten. Two independent exact enumerations of 888,030 predecessors give minimum shadow 26 where arrival at eight would require at most 25. This concerns a specified partial state, not the board's capture time. The proof includes the repaired strict-collar projection needed at this budget.

## What is still missing

The remaining common obligation is **paired boundary reachability at the required actual clocks**. We need either compatible boundary profiles with physical head and suffix words meeting a proved middle criterion, or a necessary history constraint ruling out the proposed full-board deadline. Every budget, phase and activation branch must remain covered.

The 25 October literal cutset and endpoint-intersection algorithms preserve physical shapes and reconstruct optimal inspections in their stated exact state spaces. They can be costly, and some ranges degenerate to generic finite-state search. Exact computability does not mean that the inexpensive bounds match or that the final numerical goal is solved.

General expression simplification remains deferred until the bounds match everywhere. The eventual goal still requires a fixed-size expression using O(1) standard numerical operations, plus directly specified optimal inspections. Independent extensions remain [parked](/princess/extensions/).

## Evidence levels

The new global bound and exact ranges have ordinary proofs, internal independent reviews and reproducible exact certificates where stated. Internal review is not external peer review. Diagnostic integer models are used to find candidates, not to certify impossibility; successful constructions receive actual-game checks.

The old 751-profile comparison candidate was independently verified in the later 24 October continuation: 4,507 universal obligations and the physical interface were checked. The historical candidate archive retains its original name and date; it no longer describes the acceptance status of that subsequently verified comparison.

**New Lean verification:** `PairedCompression.lean` checks complement-dual compression, the reversed time-dependent compatibility direction, preservation of daily budgets and actual prefix histories, and contraction of the paired endpoint overlap. It requires a supplied valid compression; it does not construct the missing rectangle operator. The uniform two-day bound and new exact capture families are not complete Lean theorems. Paths and two rows retain their complete physical-game formalization.

## Sources and preserved releases

- [Current manuscript PDF](/princess/princess-searches.pdf) and [readable proofs](/princess/proofs/).
- [29 October proof and evidence supplement](/princess/checkpoint-sources-2026-10-29.zip), [file hashes](/princess/checkpoint-source-manifest.json) and [evidence guide](/princess/checkpoint-evidence.md).
- [Complete mathematical sources](/princess/research-sources.zip) and [precise formal coverage](/princess/lean/).
- [Previous 24 October PDF](/princess/archive/2026-10-24-pre-october29-release/princess-searches.pdf) and [archive manifest](/princess/archive/2026-10-24-pre-october29-release/archive-manifest.json).

Historical research records keep their original wording and dates. Their inclusion does not promote experiments or abandoned candidates to accepted theorems. The current assessments and named reviews give the acceptance boundary. No Princess paper has been submitted to arXiv.

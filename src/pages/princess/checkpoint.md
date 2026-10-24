---
layout: "../../layouts/Post.astro"
title: "Rectangle capture time: the October checkpoint"
description: "Proved uniform bounds, new exact families, the unverified comparison candidate, and the remaining gap."
updated: 2026-10-24
---

[Overview](/princess/) · [Coverage](/princess/coverage/) · [Remaining gaps](/princess/gaps/) · [Paper and sources](/princess/paper/) · [Lean coverage](/princess/lean/)

**The proved lower and constructive upper bounds differ by at most four days for every rectangle and every feasible budget. Matching them everywhere remains open.** This is the frozen research checkpoint of 24 October 2026. This publication pass records the results; it does not continue the mathematical search.

Write $w\le n$ for the side lengths and $k$ for the constant daily inspection budget. The bounds cover the entire requested domain $k\ge\lfloor w/2\rfloor+1$. Stronger previously established results are retained by taking the maximum of proved lower bounds and the minimum of constructive upper bounds.

## Accepted results

The global bracket is

$$L_k(w,n)\le T_k(w,n)\le U_k(w,n),\qquad U_k(w,n)-L_k(w,n)\le4.$$

For every even width $w\ge64$, every length $n\ge w$, and every feasible budget, the gap is at most **two**. The same two-day bound holds for odd $w=2b+1\ge65$, even $n$, and $k\ge2b$. Widths at most 64 retain their earlier gap of at most three, together with all sharper cases. Odd-by-odd rectangles retain their earlier exact algorithmic evaluation.

For even width $w=2b$ with $b\ge32$, the new bounds coincide at $k=b+1$ for **every** $n\ge2b$. They also coincide at $k=b+d$ for $2\le d\le b-1$ and every $n\ge2b+2d-2$. The value is $J(k)+J(\lfloor k/2\rfloor)+1$, where $J$ is the ordinary endpoint recurrence and finite endpoint minimum stated in the manuscript. Once that minimum is evaluated, the reflection construction specifies attaining inspections.

For odd width $w=2b+1$, even length $n=2\ell$, and budget $k=b+d$, the exact value is

$$T_k(w,n)=P(k)+P(\lfloor k/2\rfloor)+1$$

whenever $d\ge1$, $b\ge4d+8$, and $(2b+1)(\ell-b)>2d^2$. Here $P$ is the physical prefix gate recurrence in the manuscript. This includes every permitted length when also $b\ge d^2$, and in particular every odd width at least 25 at minimum budget. A stronger criterion uses the actual central phase span instead of its worst-case bound. The [coverage assessment](/princess/coverage/) states it precisely.

These are ordinary mathematical proofs with internal independent reviews and exact computational certificates where stated. They are **not new Lean theorems**, and internal review is not external peer review. The endpoint minima and recurrences are exact algorithms; they do not meet the eventual fixed-operation numerical goal.

## Unverified candidate

The comparison branch has a finite symbolic closure with 751 final nondominated profiles and 850 processed states, for its stated range $b\ge32$, $2\le d\le b-3$. These numbers describe the discovery computation. They do not certify a new capture-time theorem.

Independent replay with a separate encoding, entrance and late-marker applicability, primitive range checks including lagging inputs, the stopping rule, and the physical full-gate assembly remain outstanding. The candidate is **not used** in the accepted four-day or two-day bounds. Budgets $d=b-2,b-1$ are not covered by this candidate.

[Download the unverified candidate and its frozen dependency record](/princess/unverified-comparison-candidate-2026-10-24.zip).

## Remaining gaps

Gap zero still requires a common phase-compatible argument on the remaining short boards. The accepted exact odd-board proof forces two real full-front ancestors at a common cut; outside its length/span conditions, localized ancestors can occur. The existing erosion, overlap and phase-ledger lemmas have not yet been assembled into a uniform zero-gap theorem there.

For even widths, the static critical-set classification still needs the dynamic short-board joining argument. Exact squares retain a separate unresolved geometric analysis. The conditional normalized $17/16$ overlap inequality lacks its finite-board and physical assembly; the stronger $9/8$ conjecture failed. Neither is an extra capture-time theorem.

The next mathematical objective remains matching bounds throughout the domain. Simplifying to an expression with an absolute $O(1)$ number of standard numerical operations is deferred until that objective is achieved. Independent higher-dimensional questions remain [parked](/princess/extensions/).

## Evidence and preserved releases

- [Current manuscript PDF](/princess/princess-searches.pdf) and [manuscript-derived web proofs](/princess/proofs/).
- [Complete mathematical source package](/princess/research-sources.zip), including the earlier dependencies.
- [October checkpoint supplement](/princess/checkpoint-sources-2026-10-24.zip), with proof notes, reviews, computational evidence, failed approaches and explicit status guidance. [File hashes](/princess/checkpoint-source-manifest.json).
- [Evidence guide](/princess/checkpoint-evidence.md), [frozen source-review audit](/princess/wrap-source-review-audit.json), and [explicit reconciliation of one historical review-metadata hash](/princess/wrap-review-metadata-reconciliation.json). The corresponding mathematical source was unchanged; the original receipt is preserved.
- [Current formal-source audit](/princess/checkpoint-formal-coverage-2026-10-24.json). All 83 canonical Lean sources still match the September compiler receipt. No fresh compilation or additional formalization is claimed.
- [Previous published rectangle PDF](/princess/archive/2026-09-13-pre-october-release/princess-searches.pdf), [its sources](/princess/archive/2026-09-13-pre-october-release/research-sources.zip), and [immutable archive manifest](/princess/archive/2026-09-13-pre-october-release/archive-manifest.json).

Historical notes retain their original language, including “proposed” headings predating their reviews. The current manuscript, coverage assessment, frozen result summary and named review receipts identify what was accepted. Inclusion in a source archive does not turn an experiment or candidate into a proved result.

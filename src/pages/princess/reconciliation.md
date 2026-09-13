---
layout: "../../layouts/Post.astro"
title: "Rectangle capture time: progress against the goal"
description: "What changed since the fixed-size formula criterion was introduced, and what remains open."
updated: 2026-09-13
---

[Rectangle overview](/princess/) · [Exact coverage](/princess/coverage/) · [Remaining gaps](/princess/gaps/) · [Progress against the goal](/princess/reconciliation/) · [Manuscript](/princess/paper/) · [Parked extensions](/princess/extensions/)

This page is generated from the private project's canonical assessment. Named research files and certificates are preserved in the [mathematical sources package](/princess/research-sources.zip); theorem links lead to the current manuscript-derived proofs. [Download this assessment](/princess/box-reconciliation.md).

13 September 2026. Research is paused for reconciliation. The comparison
baseline is commit `d38c1b0`: the completed scope-separation pass at which
the absolute $O(1)$ numerical criterion was recorded. Its unchanged assessment
files are preserved in `archive/2026-09-13-scope-baseline/`. This comparison
includes both subsequent research passes, not just the last few updates.

## What would count as filling the box

For every positive rectangle $a,b$ and constant budget $k$, give the exact
worst-case capture time $T_k(a,b)$, including infinity, by a fixed-size
expression in standard numerical operations. Also specify optimal
inspections directly and prove capture and minimality. Initial uncertainty
is the whole board; inspections are simultaneous; movement after a miss
is compulsory along one edge. A recurrence or an optimization is an
intermediate achievement, even when it determines an exact value.

The project has made substantial progress in matching bounds and explaining
why some tempting lower models are too optimistic. The advance toward the
entire fixed-size numerical expression is narrower. None of the four
original infinite residual families has been completely removed. There
is no defensible overall percentage: the domain is infinite and we have
not chosen a distribution or proved that the remaining difficulty is
proportional to the number of parameter triples.

## What was already present at the baseline

Feasibility for all rectangles was already settled, with appropriate credit
to the existing literature. So were fixed-size formulas for every budget
at widths one through five, the three quadratic high-budget regions,
minimum-budget odd widths through fifteen, and seven rows/five inspections
at odd lengths. Complete physical-game Lean classifications covered paths
and two rows.

Every odd rectangle already had an exact joint evaluator and the one-day
interval $2\tau-1\le T\le2\tau$. At minimum budget its value and a direct optimal
strategy were already proved for every odd width, but a width-dependent
clock remained. General even-area rectangles already had an exact boundary
representation with parameter-dependent preprocessing. Those achievements
must not be counted again as progress made after defining the box.

## 1. Even short side: a boundary family closed, broad bounds tightened

The original residual range was $w=2r\ge6$, $n\ge w$,
$r+1\le k\le r(r-1)$. We now have an exact fixed-size floor/root formula and
direct optimal inspections on the entire upper boundary $k=r(r-1)$, for
every $r\ge3$ and every $n\ge2r$. This genuinely removes an unbounded parameter
family from the numerical gap. For width six, for example, budget six
is now settled at every length; budgets four and five remain outside
that new theorem.

The proof required an actual change of shape on $16\times n$ boards at budget 56,
when $n\equiv22\pmod{12}$. Both fixed-corner prefix strategies were one day
too slow there. A prescribed $127\to79\to28$ transition closes that residue.
Thus at least one apparent lower/upper discrepancy was resolved on the
construction side, and a universal claim that the current fixed-corner
upper is already optimal would have been wrong.

For every even width $w\ge4$, the named geometric lower and physical upper
now differ by at most one day whenever $\lceil13w/10\rceil\le k<wn/2$.
The one- and two-day endpoint budgets were already exact. This is a
uniform linear-budget statement, much below the old quadratic threshold.
It does not determine the remaining day throughout that range, and it
does not cover every feasible budget between approximately $w/2$ and $1.3w$.

There is also a fixed-operation evaluator for both bounds whenever
$16(k-r-1)\ge r^2$. It uses at most 168 specified elementary update blocks and
four bulk divisions. Whenever the two resulting integers agree, it is
an exact bounded expression with an attaining strategy. When they differ,
it is still a computable gap. No variable preprocessing is hidden in
this evaluation theorem.

At every even width $2r\ge10$ and minimum budget $r+1$, a new prescribed
corner-changing construction removes the search over where to change
corners. Increasing $n$ by two adds $2r$ solo days; its width constant remains
iterative. This is a uniform construction gain, not a proof of optimality.

At width 24 and budget 13, the lower $24n-370$ holds for every $n\ge24$. For
even lengths we have $24n-370\le T_{13}(24,n)\le24n-369$. In particular the
24-by-24 board remains 206 versus 207. For odd $n\ge25$ the current upper
is $24n-368$, leaving a two-day bracket there. The general even-width minimum-
budget problem remains a substantial open part of the box.

## 2. Odd short side and even long side: one whole family solved

The original residual range was $w=2r+1\ge7$, $n\ge w$ even,
$r+1\le k\le r(r+1)$. A new exact family is

$$
T_{13}(25,n)=50n-925\qquad(n\ge26\text{ even}).
$$

This is a fixed-size formula with direct optimal inspections. It combines
a genuinely joint time 28 obstruction, persistent corner geometry, a
finite exhaustive terminal certificate, and a uniform length argument.
It is one day below the former minimum-budget upper formula; that older
expression cannot be the exact answer throughout the family.
It is not an extrapolation from the 25-by-26 board.

Other independently certified exact cases across both side parities since
the baseline include
$(8\times8,k=5)$, $(12\times12,k=7)$, $(12\times14,k=7)$,
$(16\times16,k=9)$, $(16\times18,k=9)$, $(7\times8,k=4)$,
$(9\times10,k=5)$, $(11\times12,k=6)$ and $(11\times14,k=6)$.
These are useful tests of the
theory; a finite list is not a uniform rectangle classification.

Across every odd width and even length the named bounds are within one
day for $\lceil4w/3\rceil\le k<wn/2$, with the additional sufficient range
$k\ge\lceil13r/5\rceil+3$ and a sharper explicit integer condition. The root-
selected construction is now available at every feasible budget, but
its optimality is not established everywhere. The general remaining
range still has infinitely many widths, lengths and budgets.

The important theoretical advance is that corner counts alone have been
replaced by constraints that remember how far a support can have moved
from earlier corners. Whole near-square and near-pronic intervals,
their critical cases, the intersection of two corner balls, and guarded
mergers have proofs. A radius-aware Bellman potential handles repeated
updates. Its starting value is not yet proved sharp at every full-board
boundary. The proposed charge between consecutive sharp events remains
a conjecture, including the required treatment of the entry and critical
excursions. These tools explain specific false shortcuts, but they do
not close the uniform minimum-budget lower theorem.

## 3. Odd-by-odd minimum budget: the numerical gap remains

The original residual range was $w=2r+1\ge17$, $n\ge w$ odd, $k=r+1$.
It still has the previously proved exact form

$$
T=2wn-(8r^2-4r-4L_r+4),
$$

where $L_r$ is an explicitly defined width-only recurrence. Its optimal
strategy and matching bounds were already established at the baseline.
We have not replaced $L_r$ by a fixed-size expression. This original
family therefore remains wholly open at the missing numerical layer.
Broader theorems that include its exactness do not count as solving that
remaining obligation again.

## 4. Odd-by-odd intermediate budgets: the largest exactness advance

The original residual range was $w=2r+1\ge7$, $n\ge w$ odd,
$r+2\le k\le r^2$, excluding the already solved pair $(w,k)=(7,5)$.
Seven-row odd-length boards now have fixed-size formulas and direct
optimal strategies at every budget. This removes the missing seven-row
lines from the numerical gap; it does not classify seven-row even lengths.

More substantially, for every odd width $w=2r+1$ and every odd length
$n\ge w$, the solo central test is now necessary as well as sufficient for
every feasible budget $k\ge r+1$ satisfying

$$
k\le 2r\quad\text{or}\quad27k^3\le r^4.
$$

Consequently these whole regions have matching bounds and directly
specified optimal inspections without a joint strategy optimization.
The first theorem combines an unbounded ordinary proof with one complete
19,852-case finite complement, checked by an independently reviewed
integer implementation. The second is an ordinary uniform argument.
It extends the all-length budget coverage to order $r^{4/3}$.

This is not yet an $O(1)$ answer throughout either region: the solo clocks
can still have width-dependent stages. The new fixed 49-block evaluator
does give bounded numerical times and residuals whenever
$16(2k-w)\ge r^2$. Combining it with the proved scalar regions, the improved
explicit length onset, or a fixed recent-reset test produces further
exact $O(1)$ subfamilies. The onset itself has been substantially reduced;
a possible remaining scalar counterexample at fixed width is confined
to $n=O(r^2)$, instead of the earlier $O(r^4)$ bound.

Outside the union of these proven scalar-decision regions, the exact
joint evaluator still resolves an instance, but the desired direct
full-board rule remains open. Separately, wherever the width clock has
not been reduced to bounded operations, the numerical goal remains open
even if that central decision has been settled.

## Verification and artifacts are not additional mathematical coverage

The new work has ordinary proofs, independent mathematical reviews and
separately identified exhaustive certificates or physical inspection
replays. There are no new complete physical-game Lean classifications
in this pass. The canonical 83 formal modules and their scope-specific
coverage are unchanged; compiled components are not a formal proof of
the new general rectangle results.

The manuscript, detailed proofs, website assessment and downloadable
sources describe this same boundary. The main manuscript has grown from
109 pages at the scope baseline to 164 pages. It is an expanded research
record, not yet a compact journal-ready exposition; page growth is not
itself progress toward the numerical objective. Archiving the old combined
release and parking independent extensions were scope separation.
The new collar, coupling and geometric statements are mathematical
unification. The finite applications and additional formulas are actual
coverage gains. These are three different operations.

## The remaining critical obligations

First, determine the correct full-board value and a direct optimal
strategy on the remaining even-area parameter ranges. Persistent radius
geometry and a charge between successive sharp events are promising
lower-bound tools; the shape-change construction shows why the upper
side must remain open to improvement too. One day of uncertainty is
small numerically but can still encode the missing structural theorem.

Second, settle the remaining odd-board central decision outside the
proven union. The current attempt isolates an exact orientation-crossing
condition; synthetic capacity pairs violate stronger conjectures, so a
proof must use the genuine solo trajectory or a valid domination exchange.

Third, remove the width-dependent numerical clocks where they remain,
including $L_r$ at minimum budget. No result in this pass supplies a
uniform method for eliminating every changing root band. Fixed-block
evaluation on stated regions is progress toward this goal, not a reason
to weaken it.

Finally, bring the final ordinary theory through the physical-game Lean
boundary. The present research has improved the theorem structure, but
that formal work has not advanced alongside the new mathematics.

The realistic assessment is therefore: several genuine infinite regions
have moved from optimized decisions to proved direct strategies; some
new regions now meet the strict numerical goal; the even-area bounds are
much tighter and better understood. The full box is still incomplete,
and the remaining work cannot honestly be described as a finite handful
of cases or as merely polishing formulas.

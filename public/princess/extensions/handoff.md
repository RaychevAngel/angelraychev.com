# Princess extensions: parked handoff

13 September 2026. PARKED. No new mathematical searches, conjecture repairs
or formalization are authorized by this handoff. Resume only on an explicit
request to work on the companion.

## Relationship to the main project

The active project seeks a fixed-size O(1) standard numerical expression
for T_k(a,b) on every rectangle, feasibility, and directly specified optimal
inspections with proofs. See ../research/CLASSIFICATION_SCOPE.md.
These independent extensions are preserved; their unfinished questions are
not prerequisites for completing the rectangle objective. Scope separation
establishes no new mathematics and does not subsume independent theorems.

## Preserved work

- Arbitrary-dimensional odd boxes: nesting/compression, exact feasibility
  and two-count optimal-time evaluation, with ordinary geometric proofs.
- Boxes with a side of length two; equal-box and odd-side compression
  applications and exact recurrences.
- Complete physical Lean classifications of 3x3x3 and 4x4x4; the independent
  3x4x4 finite classification remains an ordinary/certificate result.
- 3x3xn families, including every-length five-inspection time 18n-36 and
  even-length six-inspection time 6n-8, with their existing proof boundaries.
- General-cylinder feasibility, asymptotics, eventual periodicity and
  inverse-deadline applications beyond rectangles.
- Independent arbitrary-budget-word and partial-initial-state directions
  where their development is not needed by the rectangle argument.

## Sources and dependencies

Companion entry: ../paper/extensions.tex. Required general proof tools stay
in the main/shared source set; applications cite them. Canonical formal
sources remain ../lean, classified by ../publication/lean-scope.json;
package copies are distributions, not additional authoritative sources.
The manuscript/source and artifact manifests record the exact split.
The historical combined 128-page release remains unchanged in
../archive/2026-09-13-combined. Dated research notes retain original statements.

## Restart assessment

Read the relevant theorem, source-specific receipt and failed-approach log
before proposing further work. Exact algorithmic characterization, closed
formula, optimal strategy and formal verification are different achievements.
No complete general multidimensional classification or complete Lean proof
of all companion geometry is claimed. Decide which one companion question
to pursue before launching experiments; do not inherit the former broad
'complete all boxes' objective from historical notes.

Public overview: https://angelraychev.com/princess/extensions/
Public proofs: https://angelraychev.com/princess/extensions/proofs/
Public formal coverage: https://angelraychev.com/princess/extensions/lean/

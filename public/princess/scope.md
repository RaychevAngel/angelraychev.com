# Rectangle capture-time completion criterion

The fixed-size numerical objective was ratified on 13 September 2026.
This scope and priority statement is synchronized to the frozen research
checkpoint of 24 October 2026. This publication pass performs no new
mathematical searches, arXiv submission, or outreach.

## Current priority

First obtain matching, computable lower and constructive upper bounds for
EVERY w<=n and EVERY feasible k>=floor(w/2)+1. Recurrences, finite endpoint
minima, and parameter-dependent preprocessing are acceptable intermediate
answers. The current accepted combined gap is at most four days throughout
that domain; stronger two-day and exact regions remain part of the answer.
Do not begin simplifying the general numerical expression until the bounds
match everywhere. The fixed-size goal below remains unchanged and is not
claimed to be achieved.

## Game and output

For every pair of positive integer side lengths w<=n and every nonnegative
integer constant daily inspection budget k, determine T_k(w,n), the minimum
worst-case days guaranteeing capture from full initial uncertainty.
Inspections are simultaneous. After every unsuccessful day the target must
traverse exactly one grid edge. The shorter and longer sides are w and n;
rotating the board does not change the answer. Infinity means no finite
guaranteed capture horizon. Include the feasibility criterion.
For k=0 define T_k(w,n)=infinity: no room is ever inspected. This
no-inspection convention includes the one-vertex board; compulsory movement
must not turn absence of a legal next move into vacuous capture. Existing
positive-budget formal theorems are not claimed to verify this added convention.

## Numerical completion

The answer must be a fixed-size closed-form expression using O(1) standard
numerical operations, with an absolute bound independent of w,n,k. A fixed
finite case distinction, arithmetic, powers, roots, floors and ceilings are
allowed. This is an operation-count goal, not constant bit complexity.
Recurrences, parameter-length sums/products, iterative array updates,
shortest paths and parameter-dependent preprocessing do not satisfy it.
Newly named operations may not conceal these computations. An O(w) clock
or an O_(w,k)(1) evaluator is an intermediate result, not numerical completion.
No proof that this goal is attainable is claimed. It will not be weakened
if the investigation falls short.

## Strategy and proof completion

Supply directly specified optimal inspections S_t(w,n,k) on finite cases,
with |S_t|<=k, and prove guaranteed capture and minimality against all legal
target movements and all competing inspections. Printing a full sequence
is not required to take O(1) time. Strategy specification and numerical
evaluation are separate deliverables. Ordinary proof, independent finite
evidence, and complete physical-game Lean coverage must be distinguished.
Full formal verification of the final rectangle theorem remains a separate
verification obligation; the existing aggregate module count is not that proof.

## Main and parked scope

Keep rectangle formulas, bounds, exact evaluators, counterexamples, and
needed general/partial-state proof tools in the main project. A useful
intermediate answer is not out of scope because it falls short of O(1).
Park independent higher-dimensional box and general-cylinder applications,
varying-budget classifications, and arbitrary-initial-state objectives at
/princess/extensions/. General lemmas retain their natural generality when
used by rectangle proofs. The fixed-deadline minimum CONSTANT budget is an
inverse formulation of the same capture relation: retain relevant rectangle
consequences, and identify independent broader applications as parked.

Historical achievements and receipts remain unchanged in the dated combined
archive. Scope selection is not mathematical unification and establishes no
new parameter cases. The October phase and shared-history results are actual
mathematical progress within the unchanged rectangle scope. The extension project resumes only on explicit request.

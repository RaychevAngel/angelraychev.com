# Rectangle capture-time completion criterion

Ratified 13 September 2026. This is the active project's fixed objective.
The current pass is scope separation and assessment only: no new mathematical
searches, new conjecture investigations, arXiv submission, or outreach.

## Game and output

For every pair of positive integer side lengths a,b and every nonnegative
integer constant daily inspection budget k, determine T_k(a,b), the minimum
worst-case days guaranteeing capture from full initial uncertainty.
Inspections are simultaneous. After every unsuccessful day the target must
traverse exactly one grid edge. T_k(a,b)=T_k(b,a). Infinity means no finite
guaranteed capture horizon. Include the feasibility criterion.
For k=0 define T_k(a,b)=infinity: no room is ever inspected. This
no-inspection convention includes the one-vertex board; compulsory movement
must not turn absence of a legal next move into vacuous capture. Existing
positive-budget formal theorems are not claimed to verify this added convention.

## Numerical completion

The answer must be a fixed-size closed-form expression using O(1) standard
numerical operations, with an absolute bound independent of a,b,k. A fixed
finite case distinction, arithmetic, powers, roots, floors and ceilings are
allowed. This is an operation-count goal, not constant bit complexity.
Recurrences, parameter-length sums/products, iterative array updates,
shortest paths and parameter-dependent preprocessing do not satisfy it.
Newly named operations may not conceal these computations. An O(w) clock
or an O_(w,k)(1) evaluator is an intermediate result, not numerical completion.
No proof that this goal is attainable is claimed. It will not be weakened
if the investigation falls short.

## Strategy and proof completion

Supply directly specified optimal inspections S_t(a,b,k) on finite cases,
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
new parameter cases. The extension project resumes only on explicit request.

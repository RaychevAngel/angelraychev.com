# Rectangle completion gaps and restart assessment

13 September 2026. Assessment only; no new mathematical searches, experiments,
or proof attempts were performed in this artifact-separation pass.

The fixed goal is [CLASSIFICATION_SCOPE.md](CLASSIFICATION_SCOPE.md): a fixed-size
O(1) standard numerical expression for every T_k(a,b), its infinity criterion,
directly specified optimal inspections, and proofs of capture and minimality.
The separate physical-game formalization obligation remains explicit.
[RECTANGLE_COVERAGE.md](RECTANGLE_COVERAGE.md) gives the exact accepted formula
union, its disjoint residual parameter ranges, and the existing expressions.

This document uses four distinct kinds of gap:

- A **bound gap** means the displayed structural lower and upper bounds differ.
  A separate exact optimizer may already resolve that same input.
- An **evaluation gap** means an exact theorem exists, but its numerical
  evaluation still uses a recurrence, an expanding list, or optimization.
- A **construction gap** means the desired directly prescribed optimal
  inspections still depend on optimization or an unresolved optimal-family
  theorem. A harmless tie choice in a valid construction is distinguished.
- A **verification or presentation gap** concerns an already asserted proof,
  its physical Lean interpretation, or an incomplete statement of the rule.

The existence of a finite-state exact search never removes the fixed-size
numerical obligation. Conversely, it deserves full credit as exact mathematics
and must not be described as merely a pair of unmatched estimates.

## 1. New critical numerical obligation: the width-dependent minimum-budget clock

**Exact range needing a delivered bounded expression:** w=2r+1>=17, odd n>=w,
k=r+1. The fixed constants at widths 3,5,7,9,11,13,15 already qualify and have
been removed from this range.

**What is established:** matching unrestricted bounds give
T=2wn-(8r^2-4r-4L_r+4), with a prescribed optimal greedy-prefix construction.
L_r is the first arrival of an explicit alternating square/pronic recurrence
at B=r(r-1). Termination and an O(r)-stage evaluation are proved.

**What is missing:** a bounded standard-operation expression for L_r, or a
different bounded expression for the same correction to T. There is no bound
gap here. The stronger numerical completion standard makes this an active
evaluation gap despite the complete ordinary value-and-attainment theorem.

**Documented attempts and lessons:** the earlier all-length note tried an
elementary correction that predicted C(11)=144 rather than 136 and C(13)=228
rather than 208. It failed. The root-band translation arguments led to the
correct width-only clock. The ancestry proof subsequently settled the
middle-day issue without proving the abandoned lower-root invariant. The
O(r)-stage improvement removes dependence on board length and day count but
does not evaluate the entire sequence of root bands in bounded form.

**Promising next obligation, not work begun:** isolate the first-arrival
quantity itself and determine whether the alternating root bands admit a
uniform arithmetic summation or a finite number of structural regimes. A
proof must handle all r and recover the existing finite constants. A formula
that simply names this hitting time does not close the gap. Establishing this
would finish the numerical part of the all-odd minimum-budget family; it
would not solve intermediate budgets or even-area boards.

Sources: `thm:odd-minimum-budget`, `prop:solo-bands`,
`research/odd-minimum-budget-all-lengths.md`,
`research/uniform-odd-minimum-budget.md`,
`research/maturation-minimum-budget-independent-review.md`.

## 2. Another numerical obligation: arbitrary-budget solo clocks

**Range:** all odd intermediate-budget families left after the accepted
formula union, including arbitrarily long boards. In sorted notation,
w=2r+1>=7, n odd, r+2<=k<=r^2, excluding (w,k)=(7,5).

**What is established:** the solo time tau and the two precentral residuals
are computed with at most 4r+2 translation intervals. At and beyond the
explicit scalar onset in RECTANGLE_COVERAGE, these determine T exactly without
joint optimization. A prescribed palindrome or central-overlap schedule
attains the selected answer. At minimum budget the previous section gives
the more specialized correction clock.

**What is missing:** eliminate the variable number of square/pronic bands
from the numerical answer. This persists even if the scalar compatibility
conjecture is proved at every length. Evaluating a product, sum, matrix, or
recurrence with parameter-dependent size cannot be presented as O(1).

**Documented progress:** affine interior jumps already aggregate arbitrarily
many search days into floor divisions. The unresolved work is the accumulated
effect of the changing corner bands, not repeating the affine middle.
No accepted bounded expression for those accumulated effects is documented.
That is an absence of an accepted result, not a claim that nobody considered
possible substitutions or summation identities.

**Promising directions for a later research pass:** seek a bounded description
of the combined passage through several bands, or prove that only a fixed
number of extremal bands affect the full-board answer. The latter would bypass
an exact formula for every solo partial state. Either route must supply an
explicit operation audit and retain the floor/root endpoint corrections.
Success would remove this evaluation dependency wherever the scalar decision
is already exact. The shorter-board decision below remains separate.

Sources: `eq:uniform-solo-deficits`, `prop:solo-bands`,
`thm:eventual-odd-scalar`, `research/uniform-rectangle-time.md`.

## 3. Short odd boards: the full-board middle-day decision

**Exact containing range after known formulas are removed:** w=2r+1>=7,
odd n>=w, r+2<=k<=r^2, (w,k)!=(7,5), and (wn-1)/2<M_*(r,k), where
M_* is the explicit polynomial/floor expression in RECTANGLE_COVERAGE.
The unrestricted scalar conjecture includes some additional already solved
special cases, but those are not new completion obligations.

**What is established:** every answer is 2tau-1 or 2tau. An exact retained
joint frontier, including exceptional mixed histories, computes the minimum
central inspection cost and constructs a winning prefix schedule. The pure
solo endpoints give a sufficient central-day test at all lengths and a
necessary test beyond the explicit onset. The all-length minimum-budget and
high-budget cases already have proofs of necessity.

**What is missing:** an optimization-free full-board winning decision at the
central day. It could be the solo test or a different bounded description if
that test fails. A proof of optimality from every partial state is not needed.
Even a successful new decision still leaves Section 2's O(1) evaluation task
unless the new argument simultaneously removes the clock.

**Attempts and precise failures:**

- General serial optimality from arbitrary partial states fails. On 7x7 at
  budget 6, the reachable pair (8,8) has a five-day continuation while the
  serial continuation needs six. Reaching it in the stored witness took
  eighteen days, whereas the full-board optimum is sixteen. It therefore
  does not refute full-board serial optimality.
- Exact separate one-cohort ammunition costs do not imply a legal joint
  schedule. At r=3,k=5,t=2, the putative pair (3,2) has separate costs 5+4<=10,
  but their one-day blocks both need the final day. The actual one-step
  inequality excludes that pair.
- Unconditional two-block domination in the bottom model fails at
  r=4,k=7,t=4: quotas (7,0,1,5) attain (5,6), not dominated by a word with two
  pure blocks and one shared day. It is low-total relative to solo capacities
  (14,12), so the midpoint proof may safely discard it.
- A stronger charge inequality that bounds secondary ammunition by primary
  lag fails on an actual exceptional history: on 21x21, k=12, t=10, the stored
  word reaches deficits (1,55) while solo capacities are (55,56). Secondary
  ammunition is two and primary lag is one. A real unit of rounded-root
  credit must be respected.

**Accepted progress:** the ancestry argument identifies the same initial
primary cohort among retained exceptions. The common ammunition theorem is
exact for a single corner process. The suffix exchange is proved when primary
inverse inputs stay above H=r^2+1. These are useful precise statements, not
proofs of unrestricted schedule compatibility.

**Inconclusive evidence:** exceptional-output seriality passed 48 selected
boards/budgets and 3,931 precapture layers. Bounded checks of 16,970 exceptional
states found no rounding credit greater than one, and 6,546 selected
transitions preserved the relaxed credit condition. These tests prove none
of the corresponding unbounded claims. In particular the same inequality
can fail for synthetic capacities, so actual solo history matters.

**Most direct future target:** bound the central cost of two exceptional
full-board histories sufficiently to decide whether it exceeds k. This asks
less than computing every reachable pair or proving universal seriality.
A second route is a guarded two-block replacement proved only for histories
that could beat the known full-board schedule. Either route must handle the
lower root bands and the demonstrated one-unit credit. A counterexample to
the solo test would require a corrected rectangle answer, not an automatic
obligation to repair all stronger conjectures.

Sources: `lem:exceptional-retention`, `lem:fastest-ancestry`,
`lem:expansive-primary-exchange`,
`research/uniform-rectangle-reachable-counterexample.json`,
`research/maturation-odd-midpoint.md`,
`research/maturation-odd-exceptional-seriality.json`.

## 4. Even-area rectangles: uniform boundary values and an optimal full-board family

**Exact residual ranges:**

- w=2r>=6, n>=w, r+1<=k<=r(r-1);
- w=2r+1>=7, n>=w even, r+1<=k<=r(r+1).

**What is established:** the static neighborhood profiles are exact. Physical
interior height connections have explicit weights. An exact boundary-port
representation determines T and reconstructs optimal physical inspections
after finite preprocessing depending on w,k. The construction includes short
lengths through finite physical-state evaluation. All-parity high-budget
formulas and every width through five have already been removed from the
residual domain.

**What is missing:** a uniform bounded expression for the boundary contribution
and a directly specified optimal full-board inspection family. Optimizing a
larger finite boundary graph is still exact mathematics but does not close
either deliverable. A fixed-dimensional parameterization alone also does
not suffice if it still requires a search over the parameter values.

**Attempts and lessons:**

- Chaining separate neighborhood minima is invalid. The recorded 6x6,k=5
  instance has value 14 where the size-only relaxation predicts 13. The
  important phenomenon is a transition incompatibility, not an inaccurate
  static profile. The finite example retains its computational evidence
  status; it does not establish a uniform six-row theorem.
- A full-board varying-quota word (6,8,5,6,18) on 6x6 refutes always staying in
  all-corner weightlex prefixes. This does not refute a constant-budget
  full-board prefix theorem. Constant budgets from certain partial prefixes
  also defeat the restriction, which again is stronger than the required
  initial condition.
- Size plus both corner-availability bits is not an exact dynamic description.
  On the width-14 half-strip with k=9, the partial-start nine-day two-bit
  relaxation predicts capacity 42 while the physical capacity is 41. The
  forced 33-to-39 and 30-to-36 steps cannot restore the needed opposite
  corner in time. The accepted triangle and propagation lemmas explain this
  obstruction. They do not classify a full rectangular starting board.
- A broad full-diagonal/ramp class is closed under neighborhoods and certain
  truncations but is not a relative winning normal form. From the 29-room
  parent with diagonal counts (3,5,1,2,3,4,5,6), quota word (5,33) succeeds
  using the survivor (1,2,1,2,3,4,5,6). Every broad-class survivor of the needed
  size instead has at least 34 neighbors. Both the varying budget and partial
  start distinguish this counterexample from the present completion goal.
- A monotone cardinality-preserving retraction fixing the proposed broad
  class is excluded by failure of intersection closure. The narrower class
  also fails union closure, excluding that same universal retraction route.
  This does not exclude a global full-board exchange theorem.

**Accepted progress:** sharper clipped erosion lowered the even-width threshold
to max(r+1,r(r-1)+1). The analogous reduction for odd width/even length was not
proved; its accepted threshold stays r(r+1)+1. The unified capacity
C_h(s)=max(s(s-1)/2,s(s-h)), conditional corner profiles, and triangle
propagation locks provide constraints stronger than single-step corner bits.

**Inconclusive evidence:** a narrower four-parameter diagonal family has
counts min(h+2i+1,c+i) and an optional partial tail. Its neighborhood/erosion
closure derivations are still draft. Finite checks cover 565 supports, 2,181
intersections, 80,640 survivor subchoices in eight selected parents, and 796
three-day first/second quota pairs in five parents without finding the
targeted failure. No unbounded optimality or full-board sufficiency follows.

**Most direct future target:** prove that some optimal search from the full
rectangle belongs to a manageable family, then evaluate its optimum uniformly.
A global replacement can charge an awkward boundary state for the cost of
entering it, rather than demand optimal continuation from every possible
partial support. Corner propagation may provide exactly the delay needed to
make that charge. A resulting family still needs a bounded numerical
optimization-free rule; solving its recurrence remains inside scope.

No accepted global replacement theorem of that type is currently documented.
This statement means no accepted proof in the reviewed record, not that the
idea is unconsidered or that it will necessarily work.

Sources: `thm:bounded-cylinder-interfaces`, `thm:guarded-physical-transitions`,
`lem:pyramid-envelope`, `thm:conditional-corner-profiles`,
`research/even-bridge-full-prefix-failure.md`,
`research/maturation-boundary-family-closure.md`,
`research/maturation-cheap-step-rigidity.md`,
`research/maturation-even-transitions.md`.

## 5. Construction and verification work that must not disappear behind the formula

The accepted narrow and high-budget formulas already have ordinary attaining
constructions. Their room-level prescription should be extracted faithfully:
prefix order, orientation, shared-day quota, terminal support, backward
enlargement, and reversal. Where a proof permits any minimal missing ideal
element, a deterministic coordinate tie order finishes the specification;
that is an exposition task, not a new optimality search.

For residual odd boards, an optimizer currently selects the joint frontier
histories. For residual even-area boards, it selects boundary paths. These
are substantive construction dependencies even when the optimized value is
mathematically exact. A direct strategy may take many operations to print or
evaluate over its full duration; the user placed O(1) on the numerical answer,
not on the total output.

Complete physical-game Lean classifications within the main rectangle scope
are paths and two rows. Three through five rows, the general rectangle
profiles and time theorems, the all-width minimum-budget theorem, eventual
scalar criterion, and the boundary interpretation remain ordinary mathematics
with the specific verified components recorded in `publication/lean-scope.json`
and `lean/README.md`. Even a numerically completed family is not thereby fully
formalized. The target is a physical-game theorem for the final rectangle
classification and its actual dependencies, not formalizing every independent
extension before the main project may finish.

## 6. Directions that are parked, and shared tools that stay

Independent higher-dimensional box classifications, higher-dimensional cylinder
applications, varying-budget classifications, and arbitrary-initial-support
optimality objectives are parked at `/princess/extensions/`. Their proofs,
sources, formal achievements, counterexamples, and restart notes are preserved.
Parking establishes no theorem and must not be reported as unification.

General compression, inverse-profile duality, erosion, ancestry, corner
capacity, height transition, and interface lemmas stay available to the main
proof wherever they are genuine dependencies. Their natural generality need
not be artificially removed. Partial-state counterexamples remain relevant
warnings in the rectangle research record without making their resolution an
additional obligation.

The inverse fixed-deadline problem for a **constant** budget expresses the
same rectangle capture relation. Its relevant rectangle consequences remain
in scope. Developing the broader fixed-deadline theory for unrelated cross-
sections is parked. An eventual periodic answer with computed residues still
does not meet the fixed-size numerical criterion on its own.

## 7. Suggested order for a future authorized research pass

1. Attack the minimum-budget correction and the general solo corner passage
   as explicit numerical objects. Success must remove the width-dependent
   count of numerical stages, not only speed the recurrence.
2. In parallel, address the odd-board central winning decision under the full
   initial-state restriction. Aim at the decision needed by T, rather than a
   stronger all-partial-state equality.
3. Address even-area full-board sufficiency using entry costs, propagation
   delays, and global replacement. Then evaluate the surviving boundary choice
   in a bounded expression; a new optimizer is an intermediate milestone.
4. State direct inspections and formalize completed rectangle dependencies
   as they stabilize. Do not expand into parked applications as a condition
   for closing the rectangle theorem.

These are proposed directions, not claims of feasibility or proofs in
progress. The outcome may remain a collection of strong exact intermediate
results. If so, report the residual ranges and dependencies explicitly;
the fixed-size numerical goal must not be weakened to match the outcome.

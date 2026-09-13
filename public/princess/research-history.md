# Mathematical research history and current proof boundaries

## Original work

Angel Ivanov Raychev's path research took place between October 2019 and
March 2020. Two Bulgarian conference manuscripts preserve the results.
The joint student manuscript is cited under Angel Raychev and Dimitar Rusev;
the spring manuscript is cited under Angel Raychev. The combined manuscript
acknowledges Rusev's writing of the preliminary monotonicity section, by
agreement, and thanks Dimitar Dimitrov for his mentorship.

The present investigation reconstructed the intended path formula, restored
the missing single-probe restriction in a printed statement, and recovered
the exceptional residue case. The new indexed strategy compresses the earlier
construction cases. These are reconstructions of the author's earlier result,
with new proof organization, not a reassignment of its original credit.

## September 2026 investigation

Work developed with substantial assistance from Astra 6 through the Codex
harness. The full working log and original documents are preserved locally;
this public record summarizes the mathematics and its evidence.

- Reconstructed and independently attacked the complete path theorem.
- Proved a complete two-row formula by projecting each initial-color cohort
  to a closed-neighborhood path process.
- Proved all-budget three-row and four-row formulas. Critical low-expansion
  states require either a history bit or a relaxation allowing free holding;
  unrestricted interleaving is included in the lower arguments.
- Proved an abstract theorem compressing entire strategies, with unchanged
  daily budgets, and concrete odd-path and square-fiber applications.
- Derived explicit minimum open-neighborhood profiles for all odd rectangles.
  The correct tie order fills the shorter coordinate first within a layer.
- Proved isoperimetric nesting on every odd-sided box in every dimension.
  A linear neighborhood-cost identity and a terminal-coordinate exchange
  lemma complete an induction on dimension. Two independent proof reviews
  checked the arbitrary-dimensional argument.
- Proved the five-row, three-probe formula `T=10n−20` for every `n≥5`.
  The even case uses a finite symbolic column automaton with arbitrary
  empty/full pumping lengths; it is not a finite-length extrapolation.
- Classified every budget on the 3×3×3 box, including exact time. The entire
  table has a Lean proof using arbitrary-support neighborhood bounds and
  concrete physical schedules.
- Proved a height strategy for arbitrary bipartite cylinders. Together with
  the cube obstruction it gives exactly five probes for every 3×3×n box,
  `n≥3`. For odd lengths, five probes take exactly `18n−36` days,
  proved by an independently checked interval-insertion certificate.
- Proved every budget on even-length five-row boards. A history-dependent
  potential, a separate four-probe equality obstruction, and three finite
  high-budget checks complete the endpoint cases.
- Proved `T=2wn−C(w)` at the minimum budget for widths 3,5,…,15 and every
  odd length at least the width. Exact rational certificates extend to
  unbounded lengths by a proved interval-insertion theorem.
- Proved eventual periodic affine capture time for every fixed feasible
  budget and every fixed all-odd cross-section in arbitrary dimension.
  An explicit threshold and finite base computations determine the entire
  later sequence. The minimum-budget case is eventually linear.
- Derived an exact transfer recurrence for neighborhood profiles on cylinders
  of either parity, from compatible transverse profiles. This is not a
  proof of compatible global minimizers or exact capture time on even cylinders.

- The final bounded attack resolved `T₅(3×3×4)=36`. Transverse compression
  gives eight counts; two independent exhaustive implementations agree,
  and the36-day schedule replays on actual rooms. This is a finite
  computer-assisted theorem, not a new complete Lean classification.

## 12 September continuation

- Completed all budgets for odd-length five-row rectangles, so five rows
  are now entirely classified by closed formulas and explicit schedules.
- Solved the odd-rectangle time recurrence for every odd width 2b+1 and
  every budget m>=b²+1. A clipped corner potential and equality analysis
  exclude the final one-day alternative even when the potential loses one
  unit. The stronger budget m>=2b²+1 admits a simpler residue cutoff.
- Proved eventual affine periodicity for every fixed transverse box and
  both parities of its growing side. With A transverse rooms, D=2m−A>0,
  and g=gcd(A,D), adding 2D/g columns eventually adds exactly 4A/g days.
  A direct height-descent argument gives a polynomial sufficient onset
  bound. The length period is two at the minimum feasible budget.
- Proved the dual fixed-deadline theorem: for fixed t and any fixed finite
  cross-section, the minimum budget is eventually An/t plus a periodic
  correction. Survivor-envelope semantics are fully checked in Lean;
  the effective semilinearity argument remains an ordinary proof.
- Classified every budget on 4×4×4 and 3×4×4 by independently checked
  geometric compression and finite certificates. The complete 4×4×4
  classification now has physical Lean proofs, including arbitrary-set
  compression. At eight probes its true optimum is40 days, while a
  count-only relaxation suggests32. The 3×4×4 eight-probe optimum is14,
  while its count-only relaxation suggests12.

- Completed the exact five-inspection formula18n−36 for all3×3×n boxes
  with n>=3, including every even length. A113-state weighted-word
  certificate classifies critical boundaries for all lengths; a one-bit
  potential gives the lower bound, and an explicit reflected prefix sweep
  attains it. Independent geometry and scalar/strategy audits passed.

## Failed approaches and corrections worth retaining

1. Open-neighborhood parity nesting fails on even rectangles. A classical
   closed-neighborhood grid theorem cannot simply be quoted for that claim.
2. Using one fixed sweep orientation for both cohorts can lose a day:
   the 3×6 board with five probes needs four days, whereas that restriction
   can take five. Independent orientations repair the construction.
3. Applying the square diagonal compression unchanged to unequal rectangles
   can enlarge the neighborhood and worsen minimum time.
4. Row-interval restrictions fail for some partial starting states. A six-room
   partial state on 3×5 with four probes can require a hole in a surviving row
   to attain the optimum. Full-board normal forms need their own proof.
5. A reversed reflection instruction in an early manuscript paragraph was
   corrected against the verified path construction: on an even path the
   second cohort is reflected when its starting inspection day is odd.
6. A polynomial fitted to the first four minimum-budget width constants
   fails at larger widths. Exact certificates replace that extrapolation.
7. A middle plateau alone does not prove stable endpoint behavior. The
   cylinder theorem requires explicit corner tables and separate empty-set
   treatment; the two parity groups also require their own contraction cuts.
8. Reflected corner prefixes fail for the full6×6 board with daily quotas
   (6,8,5,6,18), although an unrestricted strategy wins. Shape compatibility
   cannot be deduced from the cardinality profile. This does not refute
   constant-budget prefix optimality from a full board.
9. Abstract dual profiles alone do not justify finishing one cohort before
   working on the other. A general serial-strategy theorem is still open here.

## Verification boundary

The complete physical path, two-row, 3×3×3, and 4×4×4 classifications are verified
in Lean 4.33.1. The public source-specific receipt records the current
module count, hashes, and fresh single-worker build. The abstract compression
theorem and generic bipartite profile duality are also checked. Selected
five-row scalar potentials, row-deficit implications, four-probe equality
lemmas, and finite high-budget bounds are checked; their complete geometry
and the potential for budgets at least five remain ordinary proofs.

The remaining uniform theorems currently have ordinary mathematical proofs
and independent reviews. Exact algorithms are distinguished from closed
formulas. Finite experiments are recorded as evidence, never as proofs of
unbounded parameter claims.

Literature credit includes Britnell–Wildon, Kamenetsky's 2018 OEIS conjectures,
Abramovskaya–Fomin–Golovach–Pilipczuk, Körner–Wei, Bolkema–Groothuis, and the
classical grid isoperimetric literature. New derivations in this investigation
do not by themselves establish priority over all previous literature.

## Final focused extensions

For odd n >= 7, seven rows with five inspections have exact time
2 ceil((7n-16)/3). A periodic rational potential handles all lengths;
a first-two-day obstruction rules out a one-day saving in one residue.
An independent coordinate audit verified the finite bases and the
unbounded insertion argument.

For even n >= 4, six inspections on 3 × 3 × n have exact time 6n-8.
Two non-global-prefix opening moves followed by a prefix sweep attain
this value. A one-bit historical integer potential proves the matching
lower bound. The unbounded proofs remain ordinary mathematics, not Lean.

## Remaining target

Resolve arbitrary even-sided boxes outside the completed families, simplify
the exact recurrences into useful formulas where possible, and extend the
formal proof coverage. The current manuscript is a research draft; it has
not been submitted to arXiv.

## September 2026: uniform two-dimensional results

The next investigation varied rectangle width, length and daily inspection
budget together. It established exact open-neighborhood profiles for every
even-area rectangle, completing the static two-dimensional profile analysis
alongside the odd-area theorem. It also proved a uniform one-day determination
of optimal time on every odd rectangle at every feasible budget, and an
exact formula for every even shorter width2b at budgets at leastb²+1.
The latter uses physical backwards-envelope searches and a matching
midpoint lower bound. These are independently reviewed ordinary proofs;
priority in the literature remains under review.

A new Lean module proves constructive exact transfer through the affine
middle of the two-cohort count process. This formal algebraic result is
separate from the ordinary geometric profile and optimal-time theorems.
General arguments replaced overlapping narrow-grid proofs while retaining
all earlier results. The full arbitrary-budget rectangle classification
remains open, and the research notes preserve failed state-compression and
potential approaches as well as the current proof targets.

## September 2026: stronger common theorems

The next continuation targeted genuine supersession of narrow results.
It completed the odd-short/even-long large-budget formula at every length:
for width 2b+1 the threshold is b(b+1)+1. A history-sensitive potential,
physical corner rigidity, and a separate two-day midpoint obstruction close
the formerly unresolved lower-bound cases. Together with the earlier odd-area
and even-short formulas this covers all side parities above the stated
quadratic thresholds. Repeated narrow-width arguments were replaced by these
theorems; stronger partial-state and low-budget results were retained.

For every odd rectangle and feasible budget, an exact retained joint frontier
has a number of states depending only on width and budget. In its safe middle,
every inherited mixed history disappears after boundedly many steps. The
remaining normalized frontier is periodic with period two. Exact integer
jumps therefore evaluate the minimum time in a number of arithmetic stages
independent of length. This is stronger than the former one-day ambiguity;
it does not prove the conjectured shortcut that uses only pure solo endpoints.
An independent coordinate-based forward game and separate accelerated/daywise
comparisons passed. The unbounded proof was reviewed independently.

For even-area cylinders with a fixed bipartite Hamiltonian cross-section,
optimal searches admit canonical physical checkpoints separated by bounded
time. Inspection localization confines each transition to bounded end or
front bands without restricting intermediate supports. Finite shape controls
and one translation coordinate give an exact shortest-path representation.
Full ordered-pair boundary summaries preserve arbitrary backtracking and
admit associative composition. This gives exact evaluation in logarithmically
many length-dependent arithmetic stages after finite parameter-dependent
preprocessing, and a compressed optimal strategy. The preprocessing has not
been implemented. The structural representation is the strengthening; an
asymptotic speed claim over the prior effective eventual-period theorem would
be misleading.

Two new Lean modules verify the attaining two-candidate root optimization
and the general graph inspection-localization theorem. The full check passes
80 modules. The geometric frontier bounds, stabilization, and new minimum-time
theorems remain ordinary proofs. General elementary formulas at every width
and budget, complete higher-dimensional classification, and full formalization
remain open. No new claim of priority over the literature is made without
further review, and the Princess manuscript remains unsubmitted.

A further common construction replaces the two parity-specific erosion
arguments. On a connected bipartite cross-section Q, its exact empty-fiber
threshold is the maximum over v of the sum over u of ceil(dist(v,u)/2).
Prescribed-size predecessor ideals above that threshold erode by one
physical level, losing exactly the relevant transverse color size. The
terminal survivor may be arbitrary if its predecessor closure fits the
envelope. This strictly extends pyramid-only constructions. A six-vertex
Hamiltonian example demonstrates that a pyramid-only terminal corner rule
can lose a day even above this threshold; independent physical replays
verify its five-day witness, and a spanning rectangle proves minimality.
The general-Q upper bounds are not promoted to matching exact formulas.

## September 2026: all-width minimum budget and corner memory

The next investigation replaced the finite list of odd minimum-budget
widths by one theorem for every odd width and odd length. A width-only
constant is evaluated in a bounded number of arithmetic stages in the
width. At any fixed feasible budget, the two pure solo trajectories now
suffice after an explicit length threshold; the exact joint evaluator
remains necessary in the unproved shorter intermediate-budget range.

A sharper occupied-root erosion bound lowers the even-width time-formula
threshold and absorbs the separate four-row low-budget proof. Exact
height-transition inequalities and balanced physical constructions replace
interior graph powering by explicit edge weights in a finite boundary
graph. The general boundary preprocessing is not claimed implemented.

One punctured-quadrant capacity formula unifies the ordinary and omitted-
corner estimates. Conditional half-strip profiles and a component argument
force sufficiently efficient survivors into particular corner triangles,
giving physical lower bounds on how soon the opposite corner can return.
Counterexamples exclude both a simple availability-bit state model and a
broader proposed family of corner strategies. These are documented failed
reductions, not exceptions to the proved full-board classifications.

Three further Lean modules verify a general convex-capacity optimization
(including all concrete punctured capacities), the shared-budget ancestry
argument under explicit inverse-system hypotheses, and clipped erosion of
actual cylinder cells. They do not constitute complete formalization of
all new geometric results. As throughout this investigation, these are
September2026 AI-assisted developments; the author's2019--2020 path work
and the original manuscript contributions retain their stated credit.

## September 2026: rectangle scope separation

The research objective is now fixed to two-dimensional rectangles, full
initial uncertainty and a constant daily budget, with a fixed-size O(1)
standard numerical expression for T_k(a,b), feasibility, and directly
specified optimal inspections. This is a stronger numerical endpoint than
the prior acceptance of arithmetic recurrences. Exact clocks and evaluators
retain their mathematical value while their remaining evaluation gaps are
made explicit. Independent box/cube/general-cylinder applications are
preserved in a parked companion. Necessary shared lemmas remain in the
rectangle proof. The inverse constant-budget deadline relation remains
relevant to rectangles. This pass changes organization and assessment only;
it reports no new mathematics and preserves original contributions.

## September 2026: resumed even-area rectangle research

After explicit authorization, effort concentrated on the two even-area gaps.
New common corner and erosion capacities, critical refinements, mergers and
near-extremal localization strengthen physical lower bounds. The near-pronic
static dual restriction supersedes an additional history bit. Every feasible
even-area budget now has the stated root-selected upper construction; the
high-budget equality thresholds are unchanged. Independent finite certificates
and literal inspections establish six exact cases; the24-square, thirteen-
inspection case is between206 and207 days. These are ordinary proofs and
computational evidence, with no new complete physical Lean theorem. The fixed-
size endpoint and parked scope remain unchanged. See
`research/RESUMED_RECTANGLE_CHECKPOINT.md` for exact boundaries.

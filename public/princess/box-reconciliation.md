# Progress against the rectangular capture-time objective

24 October 2026. This reconciliation describes the frozen checkpoint and
its publication. The original fixed-size numerical baseline is commit
`d38c1b0`; its unchanged assessment is in
`archive/2026-09-13-scope-baseline/`. The current comparison also distinguishes
the immediately preceding uniform-eight checkpoint from today's four-day
ceiling. No new mathematical search was performed during synchronization.

## The unchanged goal and current priority

For every rectangle $w\le n$ and constant daily budget $k$, determine the
minimum guaranteed capture time $T_k(w,n)$ from full uncertainty, including
infinity, and give optimal inspections with proofs. Ultimately the numerical
answer must use an absolute bounded number of standard operations independent
of $w,n,k$. A recurrence or an optimizer does not satisfy that final standard.

The user has prioritized a necessary intermediate milestone: first make the
computable lower and constructive upper bounds match throughout the feasible
domain $k\ge\lfloor w/2\rfloor+1$. Do not simplify the general final expression
before achieving that uniform match. This priority change does not weaken
the numerical completion criterion. There is no meaningful overall percentage
without a measure on the infinite parameter domain or a justified measure of
remaining proof difficulty.

## What was already present when the box was defined

Feasibility was already known from the literature. Fixed-size formulas covered
all budgets at widths one through five, the three quadratic high-budget
regions, the supplied odd minimum-budget widths through fifteen, and seven
rows/five probes on odd lengths. Paths and two rows had complete physical-game
Lean classifications.

Every odd rectangle already had an exact joint evaluator and the one-day
interval $2\tau-1\le T\le2\tau$. At minimum budget, the all-odd answer and
optimal strategy were already proved, but a width-dependent clock remained.
Every even-area rectangle already had an exact boundary representation with
parameter-dependent preprocessing. These are retained achievements; they
are not counted again as October advances.

## The new whole-domain advance

The accepted computable lower bounds and physical upper constructions now
satisfy

$$L_k(w,n)\le T_k(w,n)\le U_k(w,n),\qquad U_k(w,n)-L_k(w,n)\le4$$

for EVERY feasible triple. The preceding uniform ceiling was eight days.
All even widths $w\ge64$ now have a two-day ceiling for every length and
budget. For odd $w=2b+1\ge65$ with even length, budgets $k\ge2b$ also have
a two-day ceiling. Widths at most 64 retain their earlier three-day ceiling,
and every stronger earlier exact or one-day intersection is preserved.
Odd-by-odd exact evaluation remains available throughout.

The improvement is uniform, not an extrapolation from selected boards or a
finite panel. It replaces earlier larger-width patches with one boundary
and middle comparison. The remaining four-day ceiling is needed only where
a stronger retained statement does not apply, in particular the low-budget
large odd-width/even-length region. A four-day bound does not mean that all
those inputs actually have a four-day gap.

## Exactness now covers additional unbounded families

For even width $w=2b$, $b\ge32$, and $k=b+d$, the new reflection-transport
argument is exact for minimum budget $d=1$ at every length, and for
$2\le d\le b-1$ whenever $n\ge2b+2d-2$. Its exact value is

$$T_k(2b,n)=J(k)+J(\lfloor k/2\rfloor)+1,$$

where $J$ is the stated recurrence and finite endpoint minimum. The proof
supplies real inspections realizing the required phases, followed by the
correct terminal shared-budget construction. This resolves value gaps in
these entire parameter families. Evaluating the endpoint minimum remains
an algorithmic task, not a fixed-size expression.

For odd width $w=2b+1$, even length $n=2\ell\ge w$, and budget $k=b+d$,
we now have exactness under

$$d\ge1,\quad b\ge4d+8,\quad(2b+1)(\ell-b)>2d^2.$$

The answer is

$$T_k(w,n)=P(k)+P(\lfloor k/2\rfloor)+1,$$

with $P$ the genuine physical prefix recurrence and with attaining
concatenation/palindrome inspections. It includes every admissible length
when also $b\ge d^2$. In particular it settles minimum budget on every odd
width at least 25 and every even length, rather than just the earlier
25-row family.

A stronger criterion keeps the actual central span $G$ and requires
$h-k-2b^2>2G(d-1)+d$. The recurrence gives $1\le G\le d$; when $G\le3$,
all lengths satisfy the criterion under the natural guard. No universal
$G\le3$ claim is made. These are exact algorithmic results. They do not
remove the corresponding inputs from the ultimate numerical-evaluation
obligations unless an earlier bounded formula already applies.

## What changed in the proof, rather than only the bounds

The successful odd-width argument compares the beginning and end of one
actual normalized hypothetical faster history at one common cut. Incompatible
phase choices share a single deficit allowance. Two recent broad fronts
would then have to overlap in more cells than that allowance permits.
The length and span conditions ensure that these actual ancestors exist.
This addresses the previously overlapping phase and history dependencies.

Shared tools now preserve original area defect under localized erosion,
charge phase changes once per root wall, and bound overlaps with one common
age/deficit budget. Even-width one-color sets of surplus $b$, with $w=2b$ and $b\ge4$,
have a static classification on the stated cardinality interval for lengths
at least width plus two, and a separate one-longer interval extension.
These are mathematical unification and reusable proof progress, not automatic
new full-board exact formulas. The square classification and finite-board
assembly of the conditional normalized $17/16$ inequality remain unfinished.

## Earlier post-baseline achievements are preserved

The September progress remains in the main proofs and coverage assessment:
all seven-row odd-length budgets have fixed-size formulas; the complete
even-width family $k=b(b-1)$ has a bounded formula and an explicit exceptional
shape change; odd-board scalar decisions are exact at all lengths when
$k\le2b$ or $27k^3\le b^4$; and fixed 49-block/168-block evaluations apply in
their stated budget regions. The improved odd-board onset and reset criteria,
individual finite certificates, and higher-budget one-day comparisons also
remain valid. None is discarded by replacing the headline uniform bound.

The original four residual numerical families have not all disappeared.
October's exact recurrences substantially reduce value uncertainty within
them, but recurrence-based exactness is not a new fixed-size numerical
formula. Conversely, an existing formula remains a genuine completed range
even when a more general theorem still has a recurrence.

## The unverified candidate is not part of the claimed advance

A symbolic discovery for odd widths, $b\ge32$ and $2\le d\le b-3$, closes
751 nondominated profiles after 850 processed states. It keeps both physical
root intervals to prevent false repeated wall crossings. Independent replay,
primitive-range verification, entrance and stopping conditions, and physical
full-gate assembly remain outstanding. It is NOT used in the four-day bound,
the two-day refinements, or the exact families above. The excluded budgets
$d=b-2,b-1$ are not silently included. The
[checkpoint page](/princess/checkpoint/) links the frozen proof and review
record and separates this candidate from accepted results.

## What is still missing

The priority is a uniform zero gap, particularly the short even-area boards
and low budgets outside the exact union. The common-cut proof must cover
localized/localized and localized/full-front ancestors with their actual
phases, shared credit, and finite-board integer corrections. On even widths,
the static geometry must become a valid dynamic lower bound or a comparably
fast physical joining construction. No assumption that the old upper is
always optimal is justified: earlier shape-change examples already show
that improvements can come from the construction side.

Odd-by-odd values are already algorithmically exact, while direct strategy
selection and the fixed-size evaluation requirement still have separate gaps.
After all computable bounds match, the width clocks and finite endpoint
minima must still be reduced to the required bounded operations. These are
infinite uniform obligations, not a finite list of cases or merely editorial
polishing.

## Verification and scope are separate from mathematical progress

The accepted October results have ordinary proofs, independent reviews and
specified exact arithmetic certificates. They have not been added as complete
physical-game Lean theorems. Paths and two-row classifications retain their
full formal coverage; supporting modules keep their documented hypotheses.
The public overview, paper, proofs, evidence downloads and formal coverage
must preserve this exact distinction.

Independent higher-dimensional, general-cylinder and varying-budget projects
remain parked at `/princess/extensions/`. Parking them was scope selection.
The new common-cut and shared-defect proofs are mathematical consolidation.
Publishing the frozen checkpoint is artifact synchronization. These are three
different operations, and only the second supplies the new mathematical
coverage described above.

# Rectangle capture time: coverage under the fixed-size numerical goal

Updated 13 September 2026 after the resumed even-area investigation. The
accepted bounded-formula union remains unchanged; new uniform bounds and
finite exact consequences are recorded below. The controlling objective
is [CLASSIFICATION_SCOPE.md](CLASSIFICATION_SCOPE.md). Historical uses of
“complete” that allowed a width-dependent recurrence do not change that goal.

Write

\[
T_k(a,b)=T_k(b,a),\qquad w=\min(a,b),\quad n=\max(a,b),\quad V=wn.
\]

Side lengths are positive integers and the constant daily budget is a
nonnegative integer. An inspected room catches the princess before her
compulsory single-edge move. The initial position is completely unknown.
At zero budget set T_0(a,b)=infinity, including on a one-room board; failure
to make a compulsory move is not counted as capture. This is the separately
stated no-inspection convention, not a new claim about the existing
positive-budget physical Lean theorem.

“Numerically complete” below means a **delivered fixed-size expression** using
an absolute bounded number of standard numerical operations independent of
all three parameters. It does not mean a recurrence, an exact optimization,
or a constant depending on width and budget. O(1) here concerns arithmetic
operation count, not bit complexity or printing the inspection sequence.

The authoritative theorem identifiers below survive the manuscript split.
The frozen combined source and its checks are preserved in
`archive/2026-09-13-combined/`. Current proofs may extract shared lemmas into
different sections without changing these conclusions.

## 1. Feasibility is already a bounded numerical answer

For every rectangle,

\[
T_k(a,b)<\infty\quad\Longleftrightarrow\quad
k\ge\lfloor w/2\rfloor+1.
\]

This is the rectangular-grid feasibility theorem from the existing literature,
with the path and single-room conventions treated separately in our sources.
Its credit remains distinct from the later capture-time results. The general
rectangle feasibility theorem is not a completed physical-game Lean theorem
in this project. Paths and two-row rectangles have that complete formal bridge.

If \(k\ge V\), the answer is one day: inspect every room. If \(V\ge2\) and
\(\lfloor V/2\rfloor\le k<V\), the answer is two days. A bipartition-class
inspection captures one initial cohort and its same-color repetition captures
the other; no single day can inspect the whole board. These endpoint clauses
are already proved in the path, narrow-grid, and general rectangle sources.

Sources: `sec:foundations`, the introduction's cited feasibility result,
`thm:bounded-odd-frontier`, `thm:even-rectangle-high-budget`, and
`thm:odd-short-even-high-budget`. No new feasibility or endpoint theorem is
being asserted by this assessment.

## 2. The delivered bounded-formula union

The following union describes the accepted **formula families**, not every
isolated numerical instance present in the experimental receipts. It is a
fixed finite union. All comparisons, remainders, and indicators in the formulas
are standard arithmetic with fixed finite case distinctions.

### Paths: w=1, every n and k

For \(k\ge n\), \(T_k(1,n)=1\). For one inspection, the remaining cases are
\(T_1(1,2)=2\) and \(T_1(1,n)=2n-4\) for \(n\ge3\). For \(n>k\ge2\),

\[
T_k(1,n)=\left\lceil\frac{2n-4}{2k-1}\right\rceil+\varepsilon,
\]

where \(\varepsilon=1\) exactly when
\(n\equiv k+1\pmod{2k-1}\) and \(n,k\) are not both even.

**Value and construction:** matching unrestricted lower and upper bounds;
direct room-indexed sweeps. **Verification:** ordinary proofs, independent
checks, and complete physical-game Lean classification in
`PathClassification.lean`. Source: `eq:path-main`, `sec:paths`.

### Two rows: w=2, every n>=2 and k

Budget one is impossible; budgets at least \(2n\) take one day. Otherwise put
\(A=n-1\), \(D=k-1\). Then

\[
T_k(2,n)=\left\lceil\frac{2A}{D}\right\rceil+
\mathbf1_{\{D\text{ even and }A\equiv D/2\pmod D\}}.
\]

**Value and construction:** exact two-counter lower bound with directly
specified interval sweeps and at most one shared day. **Verification:**
complete physical-game Lean theorem in `LadderGame.lean`, in addition to the
ordinary proof and semantic review. Sources: `eq:ladder-main`, `sec:two-rows`.

### Three rows: w=3, every n>=3 and k

Use the feasibility and one-/two-day clauses first. In the remaining range
\(2\le k<\lfloor3n/2\rfloor\), write
\(3n-4=q(2k-3)+r\), with \(0\le r<2k-3\). The answer is

\[
\begin{cases}
2q,&r=0,\\
2q+1,&r>0\text{ and }k\ge r+4-\mathbf1_{\{n\text{ even},q\text{ odd}\}},\\
2q+2,&\text{otherwise}.
\end{cases}
\]

**Value and construction:** matching bounds and attaining oriented prefix or
envelope sweeps. **Verification:** reviewed ordinary proof; no complete
physical-game Lean classification. Sources: `eq:three-main`, `sec:three-rows`.

### Four rows: w=4, every n>=4 and k

Use the endpoint clauses first. For \(3\le k<2n\), write
\(2n-2=q(k-2)+r\), \(0\le r<k-2\). The answer is

\[
\begin{cases}
2q,&r=0,\\
2q+1,&r=1\text{ or }(r\ge2\text{ and }k\ge2r+4),\\
2q+2,&\text{otherwise}.
\end{cases}
\]

**Value and construction:** matching unrestricted bounds and backward envelope
construction. This range is now a specialization of the sharper all-even-width
theorem rather than an additional obligation. **Verification:** ordinary
proof, with reusable Lean components but no full physical classification.
Sources: `eq:four-main`, `sec:four-rows`, `thm:even-rectangle-high-budget`.

### Five rows: w=5, every n>=5 and k

Budgets at most two are impossible. At budget three, for both length parities,
\(T_3(5,n)=10n-20\). At budget four,

\[
T_4(5,n)=
\begin{cases}
2\lceil(5n-8)/3\rceil,&n\text{ even},\\
2\lceil(5n-9)/3\rceil+2\mathbf1_{\{3\mid n\}},&n\text{ odd}.
\end{cases}
\]

For \(5\le k<\lfloor5n/2\rfloor\), write
\(5n-6=q(2k-5)+r\), \(0\le r<2k-5\). Set

\[
J(0)=0,\ J(1)=2,\ J(2)=3,\ J(3)=J(4)=4,
\qquad J(r)=\lceil(r+5)/2\rceil\quad(r\ge5),
\]

and \(\delta(r)=\mathbf1_{\{r\in\{1,2,4\}\ \text{or}\ (r\ge5\text{ odd})\}}\).
For \(r=0\) the answer is \(2q\). For \(r>0\) it is \(2q+1\) exactly when

\[
2J(r)+\mathbf1_{\{n\text{ odd}\}}\delta(r)\le k;
\]

otherwise it is \(2q+2\). Larger budgets use the one-/two-day clauses.

**Value and construction:** all lengths and budgets have matching bounds and
attaining specified sweeps. **Verification:** reviewed ordinary proofs,
unbounded symbolic reductions, independent finite certificates, and selected
Lean arithmetic inequalities. The geometric-to-game interpretation and full
five-row classification remain outside the complete Lean coverage.
Sources: `thm:five-row-time`, `thm:five-even-all-budgets`,
`thm:five-odd-all-budgets`.

### Every even width above its quadratic budget

Let \(w=2r\ge2\), \(n\ge w\), \(h=rn\), and
\(k\ge\max\{r+1,r(r-1)+1\}\). If \(k<h\), write

\[
h-r=q(k-r)+s,\qquad0\le s<k-r,
\quad J(s)=s+\min\{\lceil\sqrt s\rceil,r\}\quad(s>0).
\]

The answer is \(2q\) when \(s=0\); otherwise it is \(2q+1\) if
\(2J(s)\le k\), and \(2q+2\) if not. Higher budgets have the endpoint values.
Both parities of \(n\) are included, with no length threshold other than
\(n\ge w\).

**Value and construction:** exact unrestricted lower bounds and a prescribed
backward enlargement/erosion construction; there is no strategy optimization
in this construction. The text allows the choice of a minimal missing ideal
element, so a common deterministic room order remains an exposition detail,
not a new mathematical existence issue. **Verification:** ordinary geometric
proofs and independent reviews; `ClippedPyramidErosion.lean` verifies the
physical erosion component, not the complete construction or classification.
Source: `thm:even-rectangle-high-budget`.

### Every odd width and odd length above its quadratic budget

Let \(w=2r+1\ge3\), \(n\ge w\) odd, \(h=(wn-1)/2\), and \(k\ge r^2+1\).
For \(k<h\), write

\[
wn-w-1=q(2k-w)+s,\qquad0\le s<2k-w.
\]

The following operations are explicitly standard roots, not hidden searches:

\[
R(x)=\lceil\sqrt x\rceil,\qquad
Q(x)=\left\lceil\frac{1+\sqrt{1+4x}}2\right\rceil.
\]

For positive \(x\), put
\(L_0(x)=x+\min\{R(x),r\}\),
\(L_1(x)=x+\min\{Q(x),r+1\}\), and \(L_0(0)=L_1(0)=0\).
For positive \(s\), define

\[
J(s)=\begin{cases}L_1(s/2),&s\text{ even},\\
L_0((s+1)/2),&s\text{ odd},\end{cases}\qquad
\delta(s)=\begin{cases}L_0(s/2+1)-L_1(s/2),&s\text{ even},\\
L_1((s+1)/2)-L_0((s+1)/2),&s\text{ odd}.\end{cases}
\]

The answer is \(2q\) for \(s=0\); for \(s>0\), it is \(2q+1\) if
\(2J(s)+\delta(s)\le k\), and \(2q+2\) otherwise. Higher budgets use the
endpoint values. The root-free specialization at \(k\ge2r^2+1\) is useful
but does not enlarge numerical completion: roots are already permitted.

**Value and construction:** matching bounds and directly specified prefix
sweeps, with at most one shared day. **Verification:** ordinary proof and
independent reviews; full physical Lean classification is incomplete.
Sources: `thm:odd-rectangle-high-budget`, `cor:odd-rectangle-root-free-time`.

### Every odd width and even length above its quadratic budget

Let \(w=2r+1\ge3\), \(n\ge w\) even, and \(k\ge r(r+1)+1\).
Use exactly the preceding quotient, remainder, and \(J\), but omit the
\(\delta\) correction. Thus the positive-remainder middle case is
\(2J(s)\le k\). Endpoint values apply at \(k\ge wn/2\).

**Value and construction:** matching arbitrary-strategy lower bounds and
backward envelope inspections with optional central overlap. The construction
is prescribed, with the same harmless ideal-element tie-choice as the
even-width proof. **Verification:** ordinary proofs and selected formal tools;
not a complete physical Lean theorem. Source: `thm:odd-short-even-high-budget`.

### Fixed minimum-budget odd widths through fifteen

For odd \(n\ge w\), the fixed list

\[
(w,C_w)=(3,8),(5,20),(7,44),(9,84),(11,136),(13,208),(15,288)
\]

gives \(T_{(w+1)/2}(w,n)=2wn-C_w\). This **fixed finite list of constants**
qualifies as a bounded numerical expression. It must not be discarded merely
because the wider theorem supersedes its mathematical conclusion: that wider
theorem has not yet evaluated its width-dependent constant in bounded form.
Widths three and five overlap the complete narrow families above.

**Value and construction:** matching bounds and greedy compatible-prefix
attainment. **Verification:** ordinary unbounded proofs with exact finite
rational certificates and independent reviews, but not a complete Lean
classification. Source: the constant list in `thm:odd-minimum-budget` and
`research/odd-minimum-budget-all-lengths.md`.

### Seven rows and five inspections

For every odd \(n\ge7\),

\[
T_5(7,n)=2\left\lceil\frac{7n-16}{3}\right\rceil.
\]

**Value and construction:** matching bounds, finitely supplied base schedules,
and explicit plateau insertion; greedy prefix sweeps need no search over
strategies. **Verification:** ordinary proof plus independently replayed
rational certificates. There is no complete physical Lean theorem.
Source: `thm:seven-row-five-probe-time`.

## 3. Exact partition of the remaining formula-family obligation

Subtract **all** the accepted formula families in Section 2, together with
infeasibility and endpoint cases. The residual parameter domain is the
following disjoint union. Membership means that the **present family-level
expression** does not meet the numerical goal; it does not say every point
has never been computed or lacks an exact algorithm.

1. **Even short side:** \(w=2r\ge6\), \(n\ge w\), and
   \(r+1\le k\le r(r-1)\).
2. **Odd short side, even long side:** \(w=2r+1\ge7\),
   even \(n\ge w\), and \(r+1\le k\le r(r+1)\).
3. **Odd-by-odd at minimum budget beyond the supplied constants:**
   \(w=2r+1\ge17\), odd \(n\ge w\), and \(k=r+1\).
4. **Odd-by-odd at intermediate budgets:** \(w=2r+1\ge7\),
   odd \(n\ge w\), and \(r+2\le k\le r^2\), excluding
   \((w,k)=(7,5)\).

The upper budget bounds in these four items already lie below the two-day
threshold on their permitted rectangles. Small illustrations of the
partition are: width six leaves budgets four through six; odd-length width
seven leaves budgets six through nine; even-length width seven leaves
budgets four through twelve. These are illustrations of the extracted
inequalities, not new time classifications.

The finite 6x6 computation records
\(T_4=22,T_5=14,T_6=10\) and all other budget values. It is preserved as
computational evidence in `even-bridge-full-constant-prefix-6x6.json`.
Its accompanying note states that final external audit was pending; it is
not silently promoted into the accepted theorem-family union. Other finite
samples within the residual domain likewise retain their exact original
evidence status. This distinction prevents “remaining family” from meaning
“every point unknown.”

## 4. What is already exact inside that residual domain

### The minimum-budget odd clock: exact value, evaluation gap only

For every \(r\ge1\), odd \(n\ge2r+1\), and \(k=r+1\), the ordinary theorem is

\[
T_k(2r+1,n)=2(2r+1)n-(8r^2-4r-4L_r+4).
\]

Here \(A_0=B_0=0\),

\[
A_{t+1}=B_t+k-\min\{q(B_t+k),r\},\qquad
B_{t+1}=A_t+k-\min\{R(A_t+k),r+1\},
\]

\(q(x)=\lceil(\sqrt{1+4x}-1)/2\rceil\), and \(L_r\) is the first time
\(B_t=r(r-1)\), with \(L_1=0\). Termination and exact arrival are proved.
The clock can be evaluated in O(r) arithmetic stages. This is a prescribed
arithmetic recurrence, **not an optimization**, but it does not meet the new
O(1) numerical goal. A name such as “corner clock” does not make it atomic.

The upper strategy is a prescribed greedy prefix solo sweep and its reversal;
the ordinary proof establishes its optimality. The important missing piece
here is a bounded expression for the correction, not a new lower-bound
theorem or an arbitrary-partial-state policy. Full Lean interpretation also
remains incomplete. Source: `thm:odd-minimum-budget`.

### Every odd rectangle: exact joint evaluation and a one-day bracket

Let \(w=2r+1\), \(M=(wn-1)/2\), \(E=M+1\), and \(k\ge r+1\). The exact
inverse-profile recurrence defines the pure deficits \(D_0(t),D_1(t)\) and
the first solo clearing time \(\tau\). The theorem gives

\[
2\tau-1\le T_k(w,n)\le2\tau.
\]

The lower alternative is attained whenever
\(E+M-D_0(\tau-1)-D_1(\tau-1)\le k\). The universal upper construction
is a specified solo sequence followed by its reversal; the lower alternative
uses two opposite preparations and a central inspection.

The solo calculation uses at most \(4r+2\) translation intervals. Sorting its
endpoints uses O(r log r) comparisons; the division stages number O(r).
These are independent of n, but **not independent of r**.

The retained joint frontier decides the binary alternative exactly for every
length. Its bounds are explicit. Set

\[
d=2k-w,\quad H=r^2+1,\quad\Gamma=k-1,\quad
K=H-1+2k(\lfloor\Gamma/w\rfloor+1),
\]
\[
W=\Gamma+K+1,\qquad J=2K+\Gamma+2k+H+2.
\]

There are at most \(2+2\Gamma(K+1)\) retained states and at most
\(4\lceil J/d\rceil+W+8\) ordinary updates. Each update considers up to
\(k+1\) allocations, and a final pair minimization decides the central day.
The method reconstructs actual compatible-prefix inspections from recorded
choices. This is an exact geometric optimization and reconstruction theorem,
not a delivered bounded formula or a direct allocation rule in every case.

Sources: `thm:uniform-odd-half-time`, `prop:solo-bands`,
`thm:bounded-odd-frontier`, `lem:exceptional-retention`. Ordinary proofs are
reviewed; the complete physical rectangle theorem is not formalized.

### The exact eventual scalar threshold

With those same constants, put

\[
M_*=2J+\Gamma+k(W+3).
\]

The scalar criterion is necessary and sufficient whenever
\((wn-1)/2\ge M_*\). This is the exact sufficient condition in
`thm:eventual-odd-scalar`; no smallest-threshold claim is made. For an explicit
length condition one may say: n is odd, n>=w, and wn>=2M_*+1. This avoids
concealing parity rounding inside an undefined threshold symbol.

Below that threshold, in the intermediate-budget residual range of Section 3,
necessity of the solo criterion remains open. The exact retained-frontier
optimizer still decides each input. Above the threshold, **joint optimization
has been removed**, and the attaining strategy is prescribed by the scalar
test. But the O(r) solo evaluation remains an O(1)-goal gap at both short and
long lengths. Proving scalar necessity for all lengths would close one gap,
not complete the numerical objective by itself.

The remaining scalar conjecture has finitely many lengths for each fixed
width and budget; the paper further confines a possible counterexample to
n=O(r^4). The domain across all widths remains infinite. Neither statement
converts the preceding lengths into a single fixed finite lookup table.

### Every even-area rectangle: exact physical boundary representation

The rectangle specialization of `thm:bounded-cylinder-interfaces` gives the
exact time and an optimal physical strategy for every feasible budget. It has
finite preprocessing depending on width and budget, a bounded boundary-port
graph, and explicit interior edge weights. For each fixed w,k the remaining
arithmetic-stage count is O_(w,k)(1) in n. Small lengths are included by finite
physical-state computation. The general boundary tables have not been
evaluated uniformly or implemented as a practical evaluator for every input.

This is an exact characterization. It does **not** meet the numerical goal,
because the preprocessing and number of cases are parameter-dependent. Its
strategy is reconstructed from an optimizing path, so a uniformly prescribed
optimal full-board family remains a construction goal. The explicit interior
connections, scalar lower bounds, and existing feasible sweeps remain in the
rectangle project as tools. None is weakened by parking unrelated cylinder
applications. Full physical Lean coverage remains incomplete.

## 5. Verification and construction are separate axes

Within rectangles, complete physical-game Lean classifications currently cover
paths and two-row boards. The other numerical formula families have ordinary
proofs and the stated certificates or reviews. The reusable Lean results prove
their own precise statements: root-cost convolution, shared-budget arithmetic,
ancestry under explicit hypotheses, physical clipped erosion, or finite
certificates. The total module count cannot be read as a classification proof.

A deterministic tie order for a freely chosen ideal extension is a small
specification task. Choosing an optimizing frontier path is a substantive
construction dependency. Neither should be hidden under the phrase “an
algorithm supplies a strategy.” Printing a long already-specified strategy is
allowed to depend on its length.

The source of scope-specific formal module ownership is
`publication/lean-scope.json`, with `lean/README.md` and the source-hashed
verification receipt supplying the actual semantic and build coverage.

## 6. Assessment boundary

This reconciliation adds no mathematical cases and changes no result's
provenance. It makes the accepted bounded-formula union and its residual
domain explicit. [RECTANGLE_GAPS.md](RECTANGLE_GAPS.md) records the critical
dependencies, prior attempts, and possible next steps. Independent extensions
are preserved and parked; a relevant general proof tool remains in the main
project even if its statement is broader than a rectangle.


## 8. New even-area lower bounds and constructions

The resumed investigation strengthens the first two residual families without
claiming their complete formula classification. The two even-area envelope
expressions above now supply **constructive upper bounds at every feasible
budget**; their matching lower proofs retain the displayed quadratic budget
thresholds. The strengthened root-selected construction is in
`lem:pyramid-envelope`, `thm:even-rectangle-high-budget`, and
`thm:odd-short-even-high-budget`.

At minimum budget on odd width, the expression
T<=2wn-(8r^2-4r-4L_r+4) is now an attained upper bound at every even length
as well; `prop:odd-even-minimum-upper` proves it. The general even-length
lower equality and the fixed-size evaluation of L_r remain separate gaps.

`thm:finite-corner-count` and `cor:critical-corner-unified` give uniform
necessary bounds for arbitrary supports on every even-area rectangle,
retaining their current and outgoing corners. `thm:erosion-corner-profile`
adds the corners whose two neighbors are present, and corner closure makes
its dual index observable. Its critical refinement is presently proved for
odd width/even length. `thm:corner-model-merger` and
`thm:erosion-model-merger` reduce the corresponding joint necessary lower
calculations to solo clocks. The latter deliberately drops a positive feature
lower-cardinality constraint; it does not assert physical attainment.

`thm:even-pronic-rigidity`, `thm:near-pronic-localization`, and
`cor:dual-near-pronic` retain shape information at and near the capacity
extrema. The near-pronic dual rule replaces a proposed extra history bit:
existing erosion counts already forbid the consecutive transitions.
`thm:near-square-localization` gives the corresponding near-square confinement.

The independently checked finite consequences are T_5(8,8)=40,
T_7(12,12)=72, T_4(7,8)=68, T_5(9,10)=96,
T_6(11,12)=128, and T_6(11,14)=172. They combine uniform ordinary proofs,
finite integer certificates, and literal-room inspection replays. They are
not a family-level fixed-size formula or complete physical Lean proofs.

The current full-board diagnostic interval is 206<=T_13(24,24)<=207.
A stronger physical SOLO lower is 103 days, versus a 104-day solo upper;
a separate time-sensitive joint equality certificate transfers its history
barrier to merged full-board histories. Together with the filtered model
and reversed midpoint cut, this proves the 206-day lower.
See `prop:twenty-four-boundary-history` and the resumed checkpoint in the
mathematical sources for the precise proof and computational boundary.

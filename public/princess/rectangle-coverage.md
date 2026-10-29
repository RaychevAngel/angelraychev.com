# Rectangle capture time: current coverage

Updated 29 October 2026. Write $w\le n$ for the positive side lengths and $k$ for the constant daily budget; put $V=wn$. The princess starts anywhere, inspections are simultaneous, and she must move across one edge after each unsuccessful day. The immediate goal is matching constructive upper and rigorous lower bounds everywhere; the eventual fixed-size numerical goal and direct optimal inspections are unchanged.

## Current uniform bounds

For every feasible input $k\ge\lfloor w/2\rfloor+1$,

$$L_k(w,n)\le T_k(w,n)\le U_k(w,n),\qquad U_k(w,n)-L_k(w,n)\le2.$$

No width, length or feasible budget is omitted. Take the maximum of all accepted lower bounds and the minimum of all physical upper bounds, retaining every stronger earlier result. Odd-by-odd rectangles retain exact joint evaluation at every budget; even-area rectangles now have a universal two-day ceiling, with exact and one-day subranges below. This improves the previous public four-day ceiling and the preceding private three-day ceiling. It does not assert a two-day improvement on every instance.

For odd $w=2b+1$ with $b\ge2$, even $n$, and $b+1\le k<Z=wn/2-b^2$, put $p=P(k)$ and $q=P(\lfloor k/2\rfloor)$, where $P(c)$ is the compatible physical-prefix gate recurrence. The new comparison, for $0\le c\le k$, gives

$$\max(2p-1,2q-2)\le T_k(w,n)\le\min(2p+2,2q+1),\qquad q\in\{p,p+1\}.$$

Widths one and three and the range $k\ge Z$ use the retained exact formulas; the odd-width argument above does not silently extend its guards. The earlier even-width two-day results cover all even widths. High-budget and narrow-board formulas remain stronger wherever applicable. The lower bound concerns arbitrary inspection histories; the upper bound has actual inspection words.

## New exact range: every budget at odd widths at least 8,193

Let $w=2b+1$, $b\ge4096$, and let $n\ge w$ be **any even length**. Put $h=wn/2$ and $B=b(b+1)$.

- $k\le b$: capture is impossible.
- $b+1\le k\le B$: $T_k(w,n)=P(k)+P(\lfloor k/2\rfloor)+1$, with attaining prefix/palindrome inspections.
- $B+1\le k<h$: the retained high-budget formula gives the exact value and inspections.
- $h\le k<2h$: two days; $k\ge2h$: one day.

This covers every budget and every length with the stated parity and width. The low- and middle-budget value remains a recurrence, not an O(1)-operation expression. A further exact range, not subsumed at smaller widths, is $b\ge512$ and $3b\le k\le\lfloor15b/4\rfloor$ at every even length.

## New physical constructions and tools

Matching lower bounds and independently replayed whole-board strategies establish $T_{48}(64,93)=285$ and $T_{72}(102,124)=413$. The old fixed-corner construction takes 286 and 414 respectively. Thus its universal optimality is false. These examples identify a necessary change in the general construction, rather than replace the all-parameter objective.

A conditional paired-boundary theorem now constructs a middle passage from **actual reached head and suffix states**, preserving phase and inherited overlap. It does not assert that every favorable raw boundary shape can arrive at its scalar clock. A 12-by-12, budget-7 target disproves that stronger claim: its scalar estimate is eight updates, while the specified target first arrives at ten. This is a partial-state arrival statement, not the board's capture time.

The 25 October literal cutset and endpoint-intersection evaluators are retained. They reconstruct physical strategies and reduce the state exponent in their stated parameter ranges, but can degenerate to generic finite-state search. Exact finite computability is not the final numerical classification.

## Evidence and formalization

The [current checkpoint](/princess/checkpoint/) and [proofs](/princess/proofs/) identify the ordinary proofs and internal independent reviews. The [29 October source supplement](/princess/checkpoint-sources-2026-10-29.zip) includes all dependencies and precise guards. These are not external peer reviews. The formerly unverified 751-profile comparison was independently verified in the later 24 October continuation; its old candidate archive preserves historical status only.

The new Lean module `PairedCompression.lean` checks an abstract complement-dual compression and paired-overlap theorem with explicit hypotheses. The global two-day bound, all-budget 8,193-width theorem and new physical constructions are **not complete Lean classifications**. Paths and two rows retain complete physical-game proofs. See [formal coverage](/princess/lean/).

## Retained numerical families and exact evaluators

The detailed earlier ranges below remain valid. Any weaker upper/lower ceilings are superseded by the current two-day bound above; none of their stronger conclusions is discarded. “Numerically complete” means a delivered fixed-size expression with an absolute bounded number of standard numerical operations. An exact recurrence or optimizer does not meet that final requirement.

## 1. Feasibility is already a bounded numerical answer

For every rectangle,

\[
T_k(w,n)<\infty\quad\Longleftrightarrow\quad
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

### Seven rows, every odd length and every budget

The remaining budgets six through nine now have bounded expressions. For
\(n\ge7\) odd, \(k\in\{6,8,9\}\), put \(D=2k-7\),
\(q=\lfloor(n-7)/(2D)\rfloor\), and \(j=(n-7)/2-Dq\). Then
\[
T_k(7,n)=28q+c_k(j).
\]
The fixed lists, starting at index zero, are

- \(c_6=(16,21,26,32,38)\).
- \(c_8=(10,12,16,18,22,25,28,31,34)\).
- \(c_9=(8,10,13,16,18,20,23,26,28,30,33)\).

The fourth formula is \(T_7(7,n)=2n-2\). Combined with the already proved
minimum-budget, five-inspection and high-budget results, this covers **all
budgets on every seven-row odd-length rectangle**. Even lengths remain in
their separately stated range; this is not an all-seven-row classification.

**Value and construction:** exact values, fixed numerical expressions and
prescribed prefix/palindrome inspections. **Proof:** the 296 short cases
exhaust the complement of the explicit unbounded scalar-onset theorem.
An independent full Pareto calculation checks every quota split and agrees
with the earlier retained solver; an ordinary period proof covers unbounded
lengths. There is no new complete physical Lean theorem.
Source: `thm:bridge-seven-odd`, `research/bridge-odd-clock-width-seven-check.json`.

### The complete first budget below the former even-width threshold

For \(w=2r\), \(r\ge3\), \(n\ge2r\), and \(k=r(r-1)\), put
\[
h=rn,\quad s=r(r-2),\quad
j=\max\{0,\lfloor(h-k-s-3)/s\rfloor\},\quad
z=h-(j+1)s-k-1,\quad c=z+\lceil\sqrt z\rceil.
\]
Then
\[
T_k(2r,n)=2(j+3)-\mathbf1_{\{2c\le k\}}.
\]
This is a fixed-size expression on the entire stated family. Its direct
optimal construction includes an explicit shape change for width16,
budget56, and n=22 modulo12. That class has no remaining exception.
Proof and construction: `research/bridge-boundary-numeric-quadratic-edge.md`
and `research/bridge-quadratic-edge-exception.md`.

### Twenty-five rows at the minimum budget, every even length

For every even \(n\ge26\),
\[
T_{13}(25,n)=50n-925.
\]
The proof combines a uniform joint time28 obstruction, persistent radius
geometry and merger, a finite terminal certificate, and a prescribed
physical construction. It covers all even lengths, not only the checked
smallest board. Source: `research/bridge-boundary-numeric-25-exact.md`.

### Fixed-operation evaluations that supply further exact subfamilies

On odd rectangles \(w=2r+1\), whenever
\[
16(2k-w)\ge r^2,
\]
each solo clock or prescribed-day residual uses at most49 conditional
paired-map blocks and one bulk division. These are fixed compositions of
the displayed square/pronic-root maps. Four evaluations give the solo time
and central residual test. No block count depends on the parameters.

This gives an exact bounded expression and direct optimal inspections
where the scalar test is proved necessary: the low-linear or cubic range,
the explicit improved onset, the fixed recent-reset condition below, or
an already classified family. On other inputs it evaluates the solo bracket
and sufficient central test only. Source: `thm:bridge-quadratic-solo`.

On even widths \(w=2r\ge4\), if
\[
k\ge r+2,\quad k<rn,\quad16(k-r-1)\ge r^2,
\]
the critical-corner lower bound \(L\) and a physical upper bound \(U\)
use at most168 elementary blocks and four divisions together. Whenever
\(L=U\), their common value is an exact fixed-size answer, with the
prescribed upper construction optimal. The comparison itself has bounded
size. When \(L<U\), this theorem supplies numerical bounds only.
The block definitions are in `research/bridge-boundary-numeric-budget.md`;
fixing16 once is essential to the assertion.

## 3. Residual domain under the eventual fixed-size numerical criterion

The original scope baseline had four residual families. The bounded-formula
union, including the September improvements above, leaves the following
containing ranges. October exact recurrences close value gaps inside these
ranges but do not remove them from the fixed-size numerical obligations. These are formula-family obligations; isolated
certified values inside them retain their own exact status.

1. **Even short side:** \(w=2r\ge6\), \(n\ge w\),
   \(r+1\le k\le r(r-1)-1\), excluding inputs where the preceding
   fixed168-block evaluation is defined and returns \(L=U\).
2. **Odd short side and even long side:** \(w=2r+1\ge7\),
   \(n\ge w\) even, \(r+1\le k\le r(r+1)\), excluding
   \((w,k)=(25,13)\).
3. **Odd-by-odd minimum budget beyond the supplied constants:**
   \(w=2r+1\ge17\), \(n\ge w\) odd, \(k=r+1\).
4. **Odd-by-odd intermediate budgets:** \(w=2r+1\ge9\),
   \(n\ge w\) odd, \(r+2\le k\le r^2\), excluding inputs where
   \(16(2k-w)\ge r^2\) and one of the accepted scalar-decision
   conditions in Section4 holds.

These are evaluation obligations, not claims of unknown exact values at
every input. None of these four infinite families has disappeared altogether. Width6
now leaves budgets4 and5; odd-length width7 has no remaining budget;
even-length width7 still has general obligations. Minimum-budget odd
widths beyond15 retain their original width-clock evaluation gap.
See [BOX_RECONCILIATION.md](BOX_RECONCILIATION.md) for the before/after
assessment against the exact scope-baseline commit.

## 4. Exactness and direct strategies on odd rectangles

Let \(w=2r+1\), \(n\ge w\) odd, \(E=(wn+1)/2\), \(M=E-1\).
For \(r+1\le k<M\), define the simultaneous solo deficit recurrence
\[
D_0(0)=D_1(0)=0,\qquad
D_0(t+1)=I_0(D_1(t)+k),\quad
D_1(t+1)=I_1(D_0(t)+k).
\]
Here \(R(z)=\lceil\sqrt z\rceil\),
\(\rho(z)=\lceil(\sqrt{1+4z}-1)/2\rceil\), and the proper inverses are
\[
I_0(z)=z-\min\{\rho(z),r,\rho(M-z)\}\quad(0\le z<M),
\]
\[
I_1(z)=z-\min\{R(z),r+1,1+R(E-z)\}\quad(0\le z<E).
\]
Their saturated endpoints are \(I_0(z)=E\) for \(z\ge M\) and
\(I_1(z)=M\) for \(z\ge E\). Let \(\tau\) be the first saturated
solo layer and \(L=\tau-1\).
Every odd rectangle already has the exact one-day interval
\(2\tau-1\le T\le2\tau\), an exact joint evaluator, and sufficient
solo central test. The new all-length result makes that test necessary
for feasible budgets k>=r+1 satisfying
\[
k\le2r\quad\text{or}\quad27k^3\le r^4.
\]
In these ranges,
\[
T=2\tau-\mathbf1_{\{E+M-D_0(L)-D_1(L)\le k\}}.
\]
The inspections are directly specified by the canonical solo prefixes,
reflection and the central intersection, or the ordinary two-half solo
construction. There is no optimizing joint path left in these ranges.
The recurrence still needs bounded numerical evaluation when the fixed
block hypothesis fails. Proof: `research/bridge-odd-clock-linear-budget-all.md`
and `research/bridge-odd-clock-superlinear-budget.md`.

### A smaller explicit onset

In the remaining intermediate range \(r+2\le k\le r^2\), put
\[
G=k-1,\quad H=r^2+1,\quad
K_0=r^2+2k(\lfloor G/(2r+1)\rfloor+1),
\]
\[
q=\max\{\lceil\sqrt r\rceil,\lceil G/(r-1)\rceil\},\quad
u=\left\lceil\frac{q(r+1)+G}{2q}\right\rceil,\quad
K=\min\{K_0,(q-1)k+u(u-1)\},
\]
\[
J=\max\{2K+k+1,K+H\},\quad W=2\lceil\sqrt G\rceil,
\quad M_{\rm new}=J+G+k(W+1).
\]
The scalar test is necessary if \(M\ge M_{\rm new}\). These are
fixed-size expressions. The quantity W is used in the proof of the onset;
it is not iterated to evaluate the answer. A possible remaining scalar
counterexample at fixed width is confined to \(n=O(r^2)\), improving
the old \(O(r^4)\) containing range. No smallest-onset claim is made.

### A fixed recent-reset condition

Write \(\Delta_i=D_0(i)-D_1(i)\). If \(\Delta_L=0\), the scalar
test is exact. Otherwise let p be its slower physical color, and put
\(c=\lceil(C_p-k)/2\rceil\), with \(C_0=E,C_1=M\).
The test is also exact if, for at least one of the fixed ages
\(j=0,1,\ldots,16\) with \(j\le L\),
\[
D_p(j)<c,\qquad
L-j=0\ \text{or}\ \Delta_{L-j}\Delta_{L-j-1}\ge0.
\]
Under the fixed49-block hypothesis, testing this condition uses at most38
fixed-block calls and16 inverse updates. The seventeen age cases are
fixed independently of the board. If the condition fails, it makes no
necessity claim. Source: `research/bridge-odd-clock-reset.md`.

### The minimum-budget clock remains an evaluation gap

For every odd rectangle at \(k=r+1\), the previously established law is
\[
T=2wn-(8r^2-4r-4L_r+4).
\]
The width-only L_r is the first arrival of the bottom simultaneous
recurrence at its minority value r(r-1). Its evaluation takes O(r)
root-band stages. Matching bounds and direct optimal inspections were
already proved at the scope baseline. No new fixed-size formula for L_r
has been obtained. Source: `thm:odd-minimum-budget`.

## 5. Current even-area bounds, exact regimes, and constructions

The uniform bound stated at the top applies to all feasible inputs. Earlier
one-day ranges remain valid: in particular every even-area rectangle with
$w\ge4$ and $k\ge\lceil4w/3\rceil$ has the established one-day bracket
below its two-day endpoint. For even widths the earlier sufficient threshold
is $\lceil13w/10\rceil$. The older exact high-budget, finite-width, and
individually certified cases are retained. The current uniform ceiling is two; the preceding public ceiling was four. This does not imply the same improvement for each individual instance.

### Exact even-width transport families

Let $w=2b$, $b\ge32$, and $k=b+d$. The bounds match when

- $d=1$, for every $n\ge2b$;
- $2\le d\le b-1$, for every $n\ge2b+2d-2$.

Put $h=bn$, $H=b(b-1)$, $R(x)=\lceil\sqrt{x}\rceil$, and
$\rho(x)=\min\{r\ge0:x\le r(r+1)\}$. Define simultaneous pairs

$$
A_0=(0,0),\quad
A_{j+1}=(A_j[1]+k-\rho(A_j[1]+k),\ A_j[0]+k-R(A_j[0]+k)),
$$
$$
V^c_0=(c,c),\quad
V^c_{j+1}=(k+V^c_j[1]-\rho(V^c_j[1]),\ k+V^c_j[0]-R(V^c_j[0])).
$$

Let $e(Q)$ and $\ell_c(Y)$ be the first times their respective maxima
reach $Q$ and $Y$. Over all integer endpoints
$H-d+1\le Q\le H$ and $H+1\le Y\le H+d+1$, set

$$J(c)=\min_{Q,Y}\left(e(Q)+\left\lceil\frac{h-Q-Y}{d}\right\rceil+\ell_c(Y)\right).$$

Then

$$T_k(2b,n)=J(k)+J(\lfloor k/2\rfloor)+1.$$

This is an exact finite recurrence and endpoint minimum. The proof gives
physical reflection transport and the final concatenation or palindrome;
selecting endpoints that attain the stated minimum selects an optimal
inspection sequence. This is constructive, but the endpoint optimization
has not become a fixed-size numerical expression or an optimization-free
parameter rule. Source: `upper-exact-even-transport-families.md`; independently
accepted in `lower-exact-even-transport-review.json`, both in the October
checkpoint directory.

### Exact odd-width, even-length natural range

Let $w=2b+1$, $n=2\ell\ge w$, $k=b+d$, and $h=(2b+1)\ell$. If

$$d\ge1,\qquad b\ge4d+8,\qquad(2b+1)(\ell-b)>2d^2,$$

then every full-origin signed terminal-quota gate has its exact physical
prefix clock $P(c)$, and

$$T_k(w,n)=P(k)+P(\lfloor k/2\rfloor)+1.$$

For precision, $P(c)$ is the first time the maximum reaches $h$ in the
following simultaneous recurrence, with $h$ absorbing:

$$X^c_0=(c,c),$$
$$X^c_{t+1}[0]=\min\{h,k+X^c_t[1]-\min(\rho(X^c_t[1]),R(h-X^c_t[1]),b)\},$$
$$X^c_{t+1}[1]=\min\{h,k+X^c_t[0]-\min(R(X^c_t[0]),1+\rho(h-X^c_t[0]),b+1)\}.$$

The concatenation/palindrome rule specifies attaining inspections on the
actual board. The proof constrains one actual hypothetical faster history
at one common time, keeping both phases and their combined unused allowance.
It does not assume that arbitrary partial states are optimized by prefixes.
The length condition holds for every admissible length whenever also
$b\ge d^2$. At $d=1$ this includes every odd width $w\ge25$ and every even
$n\ge w$. Sources: `lower-full-front-exact-gates.md`, its independent upper
and root reviews, and the separate reviewed minimum-budget argument.

### Stronger exact criterion from the actual central span

Under the same guard $b\ge4d+8$, define the genuine capped forward pair

$$
C_0=(0,0),
$$

$$
C_{t+1}=(\max\{C_t[1]+k-\rho(C_t[1]+k),C_t[1]+d\},
\max\{C_t[0]+k-R(C_t[0]+k),C_t[0]+d-1\}).
$$

At its first time $s$ with $\min C_s>b^2$, set
$D=C_s[0]-C_s[1]$ and $G=\max\{|D|,|1-D|\}$. We have $1\le G\le d$.
Put $A=h-b^2-k$. The same exact formula and attaining inspections hold if

$$A-b^2>2G(d-1)+d.$$

This subsumes the preceding length condition. In particular, $G\le3$
suffices for every admissible length under the natural guard. The actual
orbit must be evaluated: there is no claim that $G\le3$ always holds.
Source: `upper-central-span-exact-gates.md`, independently accepted in
`lower-central-span-exact-gates-review.json`.

### Later verification and geometric tools

The previous 24 October proof tools have since been strengthened: the critical even-width collar classification now includes squares with their appropriate orientation alternatives; the normalized overlap estimates were assembled with actual finite-board hypotheses in their stated large-width ranges. The new current theorem does not imply that arbitrary endpoint shapes are reachable at scalar clocks. See the current checkpoint and gaps assessment.

The former 751-profile symbolic comparison, at odd width $2b+1$, $b\ge32$, $2\le k-b\le b-3$ and even length, was independently accepted in the later 24 October continuation. The independent replay discharged 4,507 universal obligations, and a separate physical interface supplied entrance, marker, range and stopping hypotheses. It is not a complete Lean theorem or an exact reachability automaton. The earlier candidate zip is a preserved discovery snapshot, not its current acceptance status.

## 6. Verification and scope boundary

Complete physical-game Lean classifications in the main scope remain paths and two-row boards. The 29 October release adds PairedCompression, an abstract theorem about complement-dual compression, actual prefix histories and joining overlap under explicit hypotheses. The canonical source tree now has 84 modules; this new tool does not formalize the global two-day bound or the new exact wide-rectangle statements. Those retain ordinary proofs, internal independent reviews and exact certificates where stated. The scope manifests preserve one authoritative source tree and the parked companion's separate coverage.

The exact even-area boundary representation and exact odd joint evaluator
remain valuable achievements. Their parameter-dependent optimization does
not meet the fixed-size numerical goal or the direct optimal inspection
requirement throughout the remaining ranges. Independent higher-dimensional,
varying-budget and unrelated partial-state objectives remain parked.
[RECTANGLE_GAPS.md](RECTANGLE_GAPS.md) records the remaining proof tasks;
[BOX_RECONCILIATION.md](BOX_RECONCILIATION.md) distinguishes baseline
coverage, new mathematics, and the still-open numerical obligations.

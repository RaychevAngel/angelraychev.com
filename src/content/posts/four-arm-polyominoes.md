---
title: "Four-arm polyominoes and Golomb’s hierarchy"
description: "The complete Golomb hierarchy classification for every four-arm polyomino, with proofs and an interactive classifier."
updated: 2026-09-11
draft: false
---

*A complete classification for nonnegative integer arm lengths, with explicit constructions, impossibility proofs, independently checked certificates, and an unconditional Lean proof of all eight capabilities for every four-tuple.*

Start with one square and attach straight arms in the four compass directions. How much of the square grid can repeated copies cover? A rectangle is a much stronger achievement than the whole plane: its corners and edges impose constraints that an infinite tiling can avoid.

This article studies this question for a family that includes bars, L shapes, T shapes, and crosses. The starting point is Angel Raychev's 2021 work on L polyominoes. The investigation extends those questions to three and four arms.

## The shapes and the rules

We identify a unit square with its integer coordinate. For nonnegative integers $a,b,c,d$, define

$$
P(a,b,c,d)=\{(x,0):-c\le x\le a\}\;\cup\;\{(0,y):-d\le y\le b\}.
$$

The parameters count squares **beyond** the shared central square, in east, north, west, south order. Thus the area is $1+a+b+c+d$. Rotations, reflections, and integer translations are permitted. Tiles must cover the requested region exactly, without gaps or overlaps.

<figure>
<img src="/polyominoes/four-arms.svg" alt="A cross with its shared central square and four labeled arms." />
<figcaption>The arm lengths exclude the central square. This drawing is P(4,3,2,1).</figcaption>
</figure>

Cyclic shifts and reversal of the tuple describe congruent shapes. Degenerate bars have further descriptions: $P(1,0,2,0)$ and $P(0,0,0,3)$ are the same straight tetromino. For a genuine T shape we set $d=0$ and normalize $a\ge c\ge1$, with $b\ge1$ the stem length. These conventions distinguish the geometry without pretending that every tuple is a unique name.

## What counts as a level?

The seven regions used here are:

| Symbol | Region, expressed as grid cells |
| :-- | :-- |
| R | A finite nonempty rectangle |
| HS | A half-strip $\mathbb N\times\{0,\ldots,w-1\}$ |
| BS | A bent strip $\{(x,y)\in\mathbb N^2:x<u\text{ or }y<v\}$ |
| Q | A quadrant $\mathbb N^2$ |
| S | A full strip $\mathbb Z\times\{0,\ldots,w-1\}$ |
| HP | A half-plane $\mathbb Z\times\mathbb N$ |
| Plane | The whole grid $\mathbb Z^2$ |

Here $\mathbb N=\{0,1,2,\ldots\}$. Widths are existential: a shape tiles a strip if *some finite positive width* works. This is a branching hierarchy. In particular,

$$
\mathrm R\Longrightarrow\mathrm{HS}\Longrightarrow\mathrm{BS}
\Longrightarrow\begin{cases}\mathrm Q\\\mathrm S\end{cases}
\Longrightarrow\mathrm{HP}\Longrightarrow\mathrm{Plane}.
$$

A **plane-only** tile covers the plane but not a half-plane. A **non-tiler** does not even cover the plane. A separate classical branch asks whether congruent copies of a tile can tile an enlarged copy of itself, a *rep-tile*. Here the linear enlargement factor is a natural integer at least two, with all copies placed on the square grid. Rectangle tilings imply this property, and the property implies quadrant tileability. This branch is included in the classification below.

<figure>
<img src="/polyominoes/hierarchy.svg" alt="Implication diagram for the seven tiling regions, with the rep-tile branch between rectangles and quadrants." />
<figcaption>An arrow means that tileability of the first region guarantees tileability of the next. The rep-tile branch uses congruent copies of the original tile.</figcaption>
</figure>

These are capability implications, not permission to reverse the arrows. Nor does a failed search through several widths prove failure for all widths. For the original hierarchy and its subtleties, see [Golomb's paper](https://doi.org/10.1016/S0021-9800(66)80033-9) and [Winslow's 2018 problem survey](https://andrewwinslow.com/papers/polyprobs-dlt18.pdf).

## The complete classification

**Classification theorem.** Every shape in this family has exactly one of the following five capability profiles. A check means that some region of the indicated kind is tileable; a dash means that none is. The column I denotes the rep-tile property.

| Profile | R | I | HS | BS | Q | S | HP | Plane |
| :-- | :--: | :--: | :--: | :--: | :--: | :--: | :--: | :--: |
| R | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| BS | — | — | — | ✓ | ✓ | ✓ | ✓ | ✓ |
| S | — | — | — | — | — | ✓ | ✓ | ✓ |
| Plane-only | — | — | — | — | — | — | — | ✓ |
| Non-tiler | — | — | — | — | — | — | — | — |

To classify a tuple, first rotate or reflect the shape into the normal form in the table. A shape whose cells lie on one straight line is a bar, even if two opposite tuple entries are positive.

| Shape and normalized parameters | Exact profile |
| :-- | :-- |
| Bar, including the single square | R |
| L: $P(a,b,0,0)$, $a\ge b=1$ | R |
| L: $a\ge b=2$, or $(a,b)=(4,3)$ | S |
| L: all other $a\ge b\ge1$ | Plane-only |
| T: $P(a,1,1,0)$, $a=1,2,3$ | R |
| T: $P(a,1,1,0)$, $a\ge4$ | BS |
| T: $P(a,1,c,0)$, $a\ge c\ge2$ | S |
| T: $P(a,b,c,0)$, $a\ge c\ge1$, $b\ge2$, with $c=1$ or $b=2$ or $(c=2,\ b=a+3)$ | Plane-only |
| T: all other $a\ge c\ge1$, $b\ge1$ | Non-tiler |
| Cross: $a,b,c,d\ge1$, with $a=c=1$ or $b=d=1$ | Plane-only |
| Cross: all other $a,b,c,d\ge1$ | Non-tiler |

In particular, a genuine T tiles the plane exactly when

$$
b\le2\quad\text{or}\quad c=1\quad\text{or}\quad(c=2\text{ and }b=a+3).
$$

A genuine cross tiles the plane exactly when **two opposite arms have length one**. Thus four arms all longer than one always give a non-tiler.

The two initially exceptional cases, $P(4,1,1,0)$ and $P(5,1,1,0)$, both have profile **BS**: they tile bent strips, quadrants, full strips, half-planes, and the plane, but no half-strip, rectangle, or enlarged copy of themselves. There are no unresolved tuples in the table. The L obstruction results are credited to the supplied 2021 papers and now also have complete Lean reconstructions; the following sections and proof appendix establish the T and cross cases.

## A two-row strip and a bent strip

**Theorem.** Every $P(a,1,c,0)$ tiles a strip of width two.

Put $T=P(a,1,c,0)$, $L=a+c+1$, and $n=L+1$. For every $k\in\mathbb Z$, place

$$
T+(kn+c,0),\qquad -T+(kn+L,1).
$$

On row zero, the first tile contributes $L$ consecutive cells and the second fills the next cell. On row one, their roles reverse, with the start shifted by $c$. Each row is partitioned into blocks of length $n$; all tiles stay within these two rows. This proves exact coverage.

<figure>
<img src="/polyominoes/strip.svg" alt="Three periods of a two-row strip tiling by T shapes." />
<figcaption>A cropped view of the infinite strip for P(4,1,2,0). The cut ends are not a rectangle-tiling claim.</figcaption>
</figure>

When $c=1$, restrict the same construction to $k\ge0$. It covers the jagged half-strip

$$
H=\{(x,0):x\ge0\}\cup\{(x,1):x\ge1\}.
$$

Reflect $H$ across the diagonal and shift it upward by one cell. The resulting region is

$$
H'=\{(0,y):y\ge1\}\cup\{(1,y):y\ge2\}.
$$

These two regions are disjoint. Their union is precisely the bent strip with both arm widths two. Thus **every $P(a,1,1,0)$ tiles a bent strip**, including both initially exceptional shapes.

<figure>
<img src="/polyominoes/bent-strip.svg" alt="Two tiled jagged half-strips fit together into the arms of a bent strip." />
<figcaption>P(4,1,1,0) tiles a bent strip. Translating this bent strip repeatedly by (2,2) also tiles the quadrant.</figcaption>
</figure>

In contrast, if both crossbar arms are at least two, a quadrant is impossible. A tile at the corner must put a crossbar endpoint there. Suppose that bar lies along the bottom boundary. The tile covering the next cell up the left boundary must put a vertical crossbar there. The cell $(1,1)$ then cannot be covered: either kind of crossbar hits an existing stem, while either kind of perpendicular stem forces its crossbar outside the quadrant. This checks all possible orientations and uses only the first four corner cells.

## Why the two exceptions cannot tile a half-strip

**Theorem.** For every $a\ge4$, $P(a,1,1,0)$ tiles a bent strip but no half-strip, no rectangle, and no enlarged copy of itself by congruent copies.

The positive construction is above. The obstruction follows a corner through a hypothetical tiling. It uses five small states, each consisting of an occupied vertical wall immediately left of an empty quadrant and an occupied floor immediately below it:

| State | Wall height | Floor length | Already occupied cells inside the quadrant |
| :-- | :-- | :-- | :-- |
| $\alpha$ | 4 | 4 | None |
| $\beta$ | 5 | 6 | $(0,0)$ |
| $\gamma$ | 5 | 6 | $(0,0),(1,0)$ |
| $\beta^{\mathsf T}$ | 6 | 5 | $(0,0)$ |
| $\gamma^{\mathsf T}$ | 6 | 5 | $(0,0),(0,1)$ |

<figure>
<img src="/polyominoes/corner-states.svg" alt="Five small corner configurations with occupied walls, floors, and zero, one, or two occupied corner cells." />
<figcaption>The five corner states. Dark cells are occupied; white cells in the new quadrant must still be tiled.</figcaption>
</figure>

Here the wall cells are $(-1,0),\ldots,(-1,w-1)$ and the floor cells are $(0,-1),\ldots,(f-1,-1)$. The superscript means reflection across the diagonal.

The finite case analysis has a precise conclusion: every completion of any state either overlaps an occupied cell or creates one of these states at a new origin $(\Delta x,\Delta y)$, where both coordinates are nonnegative and their sum is positive. Previously placed tiles leave that new quadrant empty except for its listed decoration. The first transition from $\alpha$ increases both coordinates strictly.

Moreover, transitions with $\Delta y=0$ can only follow

$$
\gamma\longrightarrow\beta^{\mathsf T}\longrightarrow\alpha,
\qquad \beta\longrightarrow\alpha.
$$

Some of these arrows are absent at $a=4$. There is no directed cycle consisting only of zero-height moves. An infinite sequence of corner states must therefore reach arbitrarily large heights.

Suppose a half-strip of some positive integer height $H$ were tiled. Stacking four copies gives a tiled half-strip of height $4H\ge4$, enough to support the initial four-cell corner walls. At each step, the queried cell lies inside this half-strip. Follow the actual tile covering it; the checked local cases supply a new clean corner, still below height $4H$.

There is a finite descent proof. Assign the five states ranks $r=(0,1,2,1,0)$ in the table's order. A transition with no height increase strictly decreases $r$; a positive height increase lowers $3(4H-Y)+r$ even if $r$ increases. This nonnegative integer therefore strictly decreases at every step, which is impossible indefinitely. Lean checks both the local cases and this arbitrary-height deduction. A rectangle would yield a half-strip by repetition, so it is impossible too.

The case analysis is available as explicit proof trees: 1,750 nodes for $a=4$ and 872 for $a=5$. A separate symbolic tree handles **every integer $a\ge6$ without an upper bound**. Independent checkers verify every possible whole-tile placement through each queried cell, including overhangs, and the exact geometry of every successor corner. These are exhaustive proofs; testing a long list of strip widths would not establish the theorem.

**The rep-tile obstruction requires an additional argument.** Assign the five states potentials $h=0,2,2,1,0$, respectively. Every transition satisfies

$$
\Delta x-4\Delta y\le h(\text{old})-h(\text{new}).
$$

Thus a corner at $(X,Y)$ reached from the initial state satisfies $X-4Y\le-h$. These inequalities and all query bounds are checked by exact integer arithmetic.

If a rep-tiling existed with scale factor $k$, an original unit-length boundary segment would become a segment of length $k$ on the boundary of a union of lattice tiles. Thus $k$ would be an integer. Iteration would then tile arbitrarily large integer enlargements. At the lower-right corner of an enlargement by factor $k$, measure $X$ to the left and $Y$ upward. The long horizontal arm has height $k$ and the stem starts at $X=ak$. An interior corner before the stem has an occupied wall of height $w\ge4$, hence $Y+w\le k$. Therefore

$$
ak-X\ge(a-4)k+4w+h>a+8.
$$

Every queried cell has relative horizontal coordinate at most seven; a whole tile through it extends at most $a+1$ farther. Consequently every tile used by the corner argument remains strictly before the stem. The supported queries stay inside the rectangular arm, and the next corner does too. The same unbounded-height contradiction applies. The initial exterior corner is handled by choosing $k\ge a+2$. This proves the sharp $a=4$ case as well as all longer cases.

The historical starting point was section 23 of [Karl Dahlke's Gun Theorem](https://github.com/eklhad/trec/blob/master/theorems/gun), which states nonrectifiability for this family. The clean-corner certificates above independently check the local alternatives and supply the separate half-strip and rep-tile arguments.

## Three plane constructions for T shapes

**T boundary theorem.** A genuine $P(a,b,c,0)$ tiles a half-plane if and only if $b=1$. The forward obstruction is proved by exhaustive boundary-contact cases in the [proof appendix](/polyominoes/proofs/#4-t-boundary-and-quadrant-obstructions); the reverse direction is the two-row strip above. Consequently every plane construction in this section with $b\ge2$ has exact profile Plane-only.

A convenient way to prove an infinite tiling is to give finitely many tiles and two translation vectors. If their cells represent each residue class of the translation lattice exactly once, repeating them gives an exact plane tiling.

**A unit crossbar arm.** For $T=P(a,b,1,0)$ put $n=a+b+2$. Repeat

$$
T,\quad -T+(2a+1,0)
$$

over the lattice generated by $(2n,0)$ and $(2,1)$. The quotient coordinate is $x-2y\pmod{2n}$. The two horizontal bars cover all integers from $-1$ through $2a+2$. The remaining stem cells supply the missing even and odd residues, respectively. Every residue appears once.

<figure>
<img src="/polyominoes/t-unit-arm-plane.svg" alt="A periodic plane tiling by T shapes with a unit crossbar arm." />
<figcaption>A cropped plane tiling by P(4,3,1,0).</figcaption>
</figure>

**A stem of length two.** For $T=P(a,2,c,0)$ put $n=a+c+3$. Repeat

$$
T,\quad -T+(a+1,1)
$$

over the lattice generated by $(n,0)$ and $(c+1,2)$. Use row parity $j=y\bmod2$ and horizontal residue $x-\lfloor y/2\rfloor(c+1)\pmod n$. In the even row class the cells form the consecutive residue interval $[-c-1,a+1]$. In the odd class the horizontal bar gives $1,\ldots,n-2$ and the stems give $0,n-1$. Again every class occurs exactly once.

**An exceptional four-copy construction.** There is a further family, $T=P(a,a+3,2,0)$ for every $a\ge2$. Write $b=a+3$ and $\sigma(x,y)=(y,x)$. Repeat

$$
T,\quad -\sigma T+(b-2,-2),\quad -T+(b-1,1),\quad \sigma T+(1,3)
$$

over the lattice generated by $(4,4)$ and $(b,-b)$. Each tile has area $2b$, so the four tiles contain $8b$ cells, the index of the lattice. Exact coverage follows by reducing $x-y$ modulo $2b$ and then the transverse coordinate modulo four. The detailed eight-interval partition is retained with the research proofs; it verifies every parameter, not just the illustrated example.

<figure>
<img src="/polyominoes/exceptional-t-plane.svg" alt="A four-copy periodic tiling by the T shape P(3,6,2,0)." />
<figcaption>P(3,6,2,0). This family was found after a local search contradicted a proposed impossibility classification.</figcaption>
</figure>

## Crosses cannot touch a straight infinite boundary

**Theorem.** No collection of crosses whose four arms are positive can tile a half-plane. The crosses need not even have the same arm lengths.

Suppose such a tiling covers $y\ge0$. A tile meeting the boundary must do so at the tip of its downward arm. If its horizontal bar met the boundary, its downward arm would leave the region.

The tiles covering $(0,0)$ and $(1,0)$ therefore have junctions $(0,r)$ and $(1,s)$, with $r,s\ge1$. If $r\le s$, the first tile's right arm contains $(1,r)$, which is already on the second tile's vertical arm. If $s\le r$, the second tile's left arm intersects the first. Both alternatives are impossible.

This entire statement, with arbitrary infinite indexed families, is checked in Lean. It immediately excludes every region above HP in the hierarchy for a genuine four-arm cross.

## Opposite unit arms tile the plane

**Theorem.** If two opposite arms have length one, the cross is plane-only.

After rotation write $C=P(a,1,c,1)$ and put $n=a+c+3$. Repeat

$$
C,\qquad -C+(a+2,1)
$$

over the lattice generated by $(n,0)$ and $(1,2)$.

To check the tiling, reduce each cell by row parity $j=y\bmod2$ and the residue $x-(y-j)/2\pmod n$. In the even class, the first horizontal bar gives $n-2$ consecutive residues $-c,\ldots,a$ and the second tile's tips give the two missing residues $a+1,a+2$. In the odd class, the second bar gives $2,\ldots,n-1$ and the first tile's tips give $0,1$. These are disjoint complete partitions. The preceding theorem excludes a half-plane, so the classification is exact.

<figure>
<img src="/polyominoes/cross-plane.svg" alt="A periodic plane tiling by crosses with two opposite unit arms." />
<figcaption>P(4,1,2,1) tiles the plane. Its two short opposite arms are essential to this construction.</figcaption>
</figure>

## Four long arms cannot tile the plane

**Theorem.** If $a,b,c,d\ge2$, then $P(a,b,c,d)$ is a non-tiler.

Suppose a plane tiling exists. Let $M$ be the longest arm length. Choose a tile $O$, rotate the entire tiling so that one of its longest arms points east, and translate its junction to $(0,0)$.

Consider the four diagonal cells $(\pm1,\pm1)$ around that junction. A tile covering the northeast cell must end an arm there: extending farther west or south would hit $O$. Its junction must lie beyond the tip of $O$'s east arm or beyond the tip of its north arm. Assign this diagonal to east or north accordingly. Assign the other diagonals in the same way.

Two diagonals cannot be assigned to the same direction. For example, if both eastern diagonals were supplied from the east, their covering junctions would be $(r,1)$ and $(s,-1)$. If $r\le s$, the first tile's downward arm, of length at least two, meets the second tile's horizontal arm at $(r,-1)$. If $s\le r$, reverse their roles.

The four assignments must therefore use all four directions exactly once. Reflect vertically if necessary so the northeast diagonal is assigned east. Its covering tile $U$ has west tip $(1,1)$ and junction $(r,1)$ with $r>M$. Since its west arm has length at most $M$, we have $r-1\le M$, forcing $r=M+1$.

<figure>
<img src="/polyominoes/cross-obstruction.svg" alt="Two maximal arms lie on adjacent rows; two question-mark cells above them are trapped between vertical stems." />
<figcaption>The forced maximal-arm pair. The two marked cells cannot both be filled. The illustration uses M=4; the proof works for every M≥2.</figcaption>
</figure>

Now inspect $(1,2)$ and $(2,2)$. Neither can lie on another tile's horizontal bar. A bar extending past either side would hit $O$'s vertical arm at $x=0$ or $U$'s vertical arm at $x=M+1$. A junction between those walls would send a downward arm into $U$'s horizontal bar at height one.

Thus the two cells must be covered by distinct vertical arms coming from above. If their junction heights are $h\le k$, the first tile's right arm meets the second vertical arm at height $h$. For $k\le h$, the second tile's left arm gives the same contradiction. No tiling exists.

## Completing the cross classification

The only positive crosses not covered by the all-long-arm obstruction or the opposite-unit-arm construction have either exactly one unit arm or exactly two adjacent unit arms. Up to rotation and reflection these are

$$
P(a,1,c,d),\quad 2\le a\le c,\quad d\ge2,
$$

and

$$
P(1,1,c,d),\quad 2\le c\le d.
$$

Both families are non-tilers. Their proofs are finite symbolic case trees with 89 and 57 nodes, respectively. A node names a cell near the already placed crosses and lists every possible next cross covering it without overlap. Coordinates and arms remain arbitrary integers subject to the displayed inequalities. No maximum arm length is imposed.

All branches terminate in an uncovered cell. The independent checker allows **an arbitrary integer junction** for the proposed covering cross, so the proof does not rely on assuming that an initially plausible list of tip placements is complete. Lean then checks the arithmetic alternatives and replays the whole geometric argument for an arbitrary infinite family of disjoint crosses covering every integer cell. The translation and D4 normalization from an arbitrary tiling to the origin are also proved in Lean.

Thus a genuine cross tiles the plane **if and only if two opposite arms have length one**. It never tiles a half-plane.

## Completing the plane classification for T shapes

**Theorem.** A T shape whose three positive arms are all at least three cannot tile the plane.

The useful local object is a run of empty cells with an occupied floor and occupied cells at both ends. Write $A=a+c+1$ for the crossbar length. When $b<A$, a run of length $3\le g<A$ is impossible: a horizontal crossbar cannot fit; a horizontal stem would put its junction's downward arm into the floor. The cells must therefore start vertical crossbars or vertical stems. A vertical stem's top crossbar meets its neighbor, while three adjacent vertical-crossbar starters cannot point their stems away from each other.

When $b\ge A$, the corresponding argument permits vertical-crossbar starters only at the two ends. Four or more starters force adjacent vertical stems, which overlap. A three-cell run is also impossible when one side wall reaches both possible crossbar-junction heights. A longer run of length $b$ is excluded by examining its first horizontal crossbar: the cells just above that bar form one of the forbidden shorter runs, with the new long stem supplying the necessary tall wall.

Apply these gap facts to the two cells diagonally above the junction of an upright T. The legal alternatives force at least one of them to be the endpoint of a horizontal crossbar whose stem points down. Reflect so this second bar occupies $(-A,1),\ldots,(-1,1)$. The next cell $(-1,2)$ is then forced to start a vertical crossbar pointing its stem right. If $b\ge A$, that stem immediately overlaps the original tile. If $b<A$, the next cell $(-2,2)$ has no legal cover: each orientation either intersects an existing piece or creates a forbidden gap. The endpoint case $b=A-1$ creates a gap of length $A-1$ one row higher. The proof appendix supplies every coordinate case and wall-height hypothesis.

**Theorem.** For $a\ge2$ and $b\ge3$, $P(a,b,2,0)$ tiles the plane if and only if $b=a+3$.

The equality case has the four-copy construction above. The shorter-stem complement $3\le b<a+3$ has a 300-node symbolic obstruction, independently checked with arbitrary integer junctions and no upper bound on either parameter. Lean also verifies the full geometric deduction for an arbitrary infinite tiling, using 2,700 arithmetic lemmas. Translation and D4 normalization of an arbitrary tiling to the anchor are also checked in Lean.

The longer-stem complement $b>a+3$ admits a geometric proof. Here $A=a+3$. A useful stronger gap lemma says that **a run of any length $g\ge3$ is impossible when its floor and endpoints are occupied and one endpoint is a straight wall reaching $a+1$ rows above the run**. The supporting tiles must leave the run clear, and the tall wall’s tile must have no cells inside the run’s horizontal span in the next row. To see this, take the first horizontal crossbar, if there is one. The cells just above its left arm form a gap of length two or $a$, with two sufficiently tall walls. No horizontal bar fits there; the remaining vertical starters intersect each other or a wall. If there is no horizontal bar, only the two endpoint cells can start vertical crossbars. The interior cells must start perpendicular stems, and two adjacent such stems have overlapping crossbars. For a three-cell run the tall wall also excludes the endpoint crossbar on that side.

This lemma first excludes an antiparallel pair of horizontal crossbars at a concave corner. Checking the remaining arm-tip covers then forces some upright tile $O$ to have the following neighbor: a vertical crossbar in column one, rows $1,\ldots,A$, with junction $(1,3)$ and a long stem pointing right. The two cells $(2,1),(2,2)$ jointly force a downward-stem horizontal bar $R$ in row one and a leftward perpendicular stem $W$ in row two. The other concave corner of $W$ forces a second downward-stem bar $Z$ at the far end.

The resulting finite interval of $b$ cells in row one lies below $W$'s stem, with $R$ and $Z$ covering its two ends. A vertical-crossbar starter at an interior cell intersects its next neighbor. A perpendicular-stem starter either intersects its neighbor or encloses an $a$-by-$(b-1)$ rectangle into which no orientation fits. Hence the entire interval consists of adjacent horizontal bars of length $A$.

There are at least two such bars because $b>A$. For any consecutive pair with junction offsets $r,s\in\{2,a\}$, the run just below their bars and between their downward stems has length

$$
g=A-1+s-r\ge4.
$$

Their stems supply straight walls taller than the gap lemma requires. The lemma gives a contradiction. This closes every remaining T case. The full proof records the exact forced placements, including both possible arm orders of $O$, $R$, and $W$; it does not rely on a numerical search or an assumed periodicity.

## A small shape can require a large rectangle

The first three members of $P(a,1,1,0)$ tile rectangles. For $a=3$, the Y hexomino, there is a $24\times23$ rectangle made from 92 copies. The historical arrangement was extracted into explicit coordinates and independently checked: all 552 cells are covered once, and every piece is a congruent copy of the intended shape.

<figure>
<img src="/polyominoes/y-hexomino-rectangle.svg" alt="A 24 by 23 rectangle partitioned into 92 Y hexominoes." />
<figcaption>A verified reconstruction of the arrangement recorded by <a href="https://sicherman.net/mikereid/y6_rect.html">Michael Reid</a>, attributed to T. W. Marlow and Karl A. Dahlke. The verification here proves existence, not the minimum number of tiles.</figcaption>
</figure>

This example explains why small rectangle searches are weak evidence: a simple six-cell shape can hide its first successful construction surprisingly far away.

## How the computation is checked

Positive certificates specify whole tile placements and, for infinite constructions, their translation lattice. Verification checks both the shape of every tile and exact coverage. The written residue arguments extend these constructions to arbitrary parameter values.

Negative finite certificates enumerate **every** legal placement that could cover each required cell, including tiles extending beyond an artificial search box. Each branch chooses a still-uncovered cell and tries every nonoverlapping placement; a branch ends only when some required cell has no legal cover. A second checker regenerates the placement universe and verifies every branch. Such a certificate proves non-tileability for its stated parameters and region. It does not prove an unbounded parameter family.

For a fixed strip width, a different finite graph records occupancy across a moving cut. Its cycles describe periodic continuations. Exhausting the graph can rule out every possible length at that width; exhausting several widths still does not rule out all widths. Boundary-prefix certificates can sometimes exclude all half-strip heights at once, but that stronger inference is stated only where its hypotheses have been checked.

For unbounded parameter families, symbolic certificates add a further obligation: every branch implication must hold for all integers in the stated domain. **Lean 4.33.1 verifies the unconditional eight-capability classification for every tuple of natural arm lengths $(a,b,c,d)$**, including zero arms, all degenerate shapes, and the rep-tile branch. The final theorem is `PolyominoFormal.all_tuples_classified`; it has no remaining obstruction premise. The half-strip proof includes the entire infinite-propagation argument for arbitrary widths. The unequal long-arm L half-plane obstruction is also fully formalized, completing the Lean reconstruction of the supplied 2021 L results.

Start with the [unconditional all-tuples theorem](/polyominoes/lean/MainClassification.lean), or the short statements for [the two disputed cases](/polyominoes/lean/InitialTwoClassification.lean), [the complete gun family](/polyominoes/lean/GunFamilyClassification.lean), and [all genuine T shapes](/polyominoes/lean/TClassification.lean). The [Lean source package](/polyominoes/lean-proofs.zip) contains every dependency, and the [rebuild guide](/polyominoes/lean-guide.md) states the exact proof scope and commands. The proofs use ordinary whole-cell tilings, arbitrary integer translations, and all rotations and reflections. Rep-tiling here uses a natural linear enlargement factor at least two. Final theorem reports contain only Lean's standard axioms; there are no admitted proofs or trusted solver answers.

The research log keeps failed conjectures, counterexamples, proof revisions, and independent attacks. There is no claim of novelty merely because a construction was independently rediscovered during this investigation. The classification has no remaining proof gaps under the tiling conventions stated above.

## Proofs, source files, and the earlier papers

The [full proof appendix](/polyominoes/proofs/) supplies the coordinate cases, lattice residue partitions, corner propagation, and precise formalization boundaries. It is also available as [a Markdown download](/polyominoes/proofs.md). The [research archive](/polyominoes/research.zip) contains the manuscript, log, exact tile coordinates, finite and symbolic proof trees, independent checkers, and Lean sources, with a file-integrity manifest.

The earlier results are documented in Raychev's [2021 L-polyomino paper](/polyominoes/raychev-2021-l-quadrant.pdf) and [2021 half-plane paper](/polyominoes/raychev-2021-l-half-plane.pdf), both in Bulgarian. The present write-up uses arm lengths, so bounding dimensions $m\times n$ become arms $m-1,n-1$.

One dimensional correction emerged from reconstructing the second paper's figure: its $4\times5$ L construction is a strip of width eight and period eight, although page four calls the width six. The exact eight-tile motif was checked cell by cell. This leaves the classification theorem unchanged.

<figure>
<img src="/polyominoes/l-4x5-strip.svg" alt="Three periods of the verified width-eight strip made of L shapes with bounding dimensions four by five." />
<figcaption>The reconstructed 4-by-5 L strip. Its eight-cell width can be counted directly.</figcaption>
</figure>
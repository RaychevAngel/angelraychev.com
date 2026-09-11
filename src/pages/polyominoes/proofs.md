---
layout: "../../layouts/Post.astro"
title: "Four-arm polyominoes: proof appendix"
description: "Full constructions, impossibility arguments, and exact verification boundaries."
updated: 2026-09-11
---

This appendix records the mathematical arguments and precise certificate boundaries. The [companion article](/four-arm-polyominoes/) provides the classification table and illustrations; the research log preserves conjectures, unsuccessful approaches, and independent attacks.

We identify cells with integer coordinates and use

$$
P(a,b,c,d)=\{(x,0):-c\le x\le a\}\cup\{(0,y):-d\le y\le b\}.
$$

All parameters are nonnegative integers. Every placement is an integer translate of a D4 rotation or reflection. Exact tiling means every region cell is covered exactly once and no tile has a cell outside that region. Here N={0,1,2,...}. A rep-tiling uses congruent original tiles to tile an integer enlargement at a natural linear scale at least two.

In the T sections write $T=P(a,b,c,0)$, with $a\ge c\ge1$ and $b\ge1$, unless a construction explicitly allows the reflected order. The crossbar is the horizontal segment of $a+c+1$ cells; the perpendicular stem consists of its $b$ further cells. The cross and L sections state their own normal forms.

Contents:

- [1. Hierarchy implications](#1-hierarchy-implications)
- [2. The finite certificate principle](#2-the-finite-certificate-principle)
- [3. Explicit positive T constructions](#3-explicit-positive-t-constructions)
- [4. T boundary and quadrant obstructions](#4-t-boundary-and-quadrant-obstructions)
- [5. Clean-corner half-strip and rep-tile obstructions](#5-clean-corner-half-strip-and-rep-tile-obstructions)
- [6. Negative T-plane cases](#6-negative-t-plane-cases)
- [7. Cross obstructions and construction](#7-cross-obstructions-and-construction)
- [8. The L classification and its prior proofs](#8-the-l-classification-and-its-prior-proofs)
- [9. Exact rectangle witnesses](#9-exact-rectangle-witnesses)
- [10. Formal verification scope](#10-formal-verification-scope)

## 1. Hierarchy implications

A rectangle tiling can be repeated end-to-end to make a half-strip. A half-strip of width w together with a rotated copy starting above its first w rows tiles a bent strip with both arm widths w. A bent strip B(u,v) tiles the quadrant by translations k(u,v), k>=0: each cell (x,y) belongs to the unique layer k=min(floor(x/u),floor(y/v)).

A bent-strip tiling also implies a full-strip tiling. Move successively farther down one arm and translate the tilings back; on any fixed finite patch only finitely many whole-tile placements are possible. Repeatedly take subsequences agreeing on each larger patch. The resulting consistent assignments give a full-strip tiling. The same finite-choice compactness argument turns quadrant tilings into half-plane tilings, and half-plane tilings into plane tilings. A full strip tiles a half-plane directly by parallel repetition.

If a rectangle of sides r,s is tileable, choose an integer k>1 divisible by both r and s. Each k-by-k cell block is tileable by those rectangles. Replacing every cell of the original polyomino by such a block gives a rep-tiling of its k-fold enlargement. Conversely, a rep-tile tiles a quadrant by compactness at a convex corner of successively iterated enlargements: both adjacent boundary segments grow without bound. We use only these proved implications; the converses for arbitrary polyominoes are not assumed.

## 2. The finite certificate principle

For an ordinary finite obstruction, a node records a finite set of already occupied cells and an uncovered required cell p. Its children list every congruent whole-tile placement through p disjoint from those cells. Adding the chosen tile gives the child's occupied set. A leaf has no legal placement. Induction on the finite tree therefore excludes an exact covering of the required region. Artificial finite-patch boundaries do not prohibit overhanging tiles.

For a symbolic obstruction, the domain is a set of integer arm parameters given by linear inequalities. Every node lists placed tiles with affine integer coordinates and a queried cell. Its hypotheses include the domain and pairwise disjointness of those tiles. It is checked that the cell is unoccupied and that every possible D4 tile, with an arbitrary integer junction, either overlaps the existing tiles or equals a listed child. A child that is geometrically impossible at some parameters is a vacuous branch there. No arm-length or junction-coordinate cutoff is supplied. Finite induction proves that no infinite plane tiling contains the anchor. Any actual plane tiling can be translated and globally rotated or reflected to contain that anchor.

The complete eight-capability classification is checked in Lean for every natural four-tuple, including zero arms, arbitrary D4 copies, and integer-scale rep-tilings. [MainClassification.lean](/polyominoes/lean/MainClassification.lean) states the unconditional theorem; the [proof package](/polyominoes/lean-proofs.zip) and [rebuild guide](/polyominoes/lean-guide.md) supply its dependencies. The T short-stem two-cell-arm component has 300 states and 2,700 arithmetic lemmas, including the whole-tiling geometric replay and normalization. Solver search is used to propose cases; the finite proof principle does not assume a periodic tiling.



## 3. Explicit positive T constructions


### 1. Every b=1 tile covers a strip of width two

**Proved construction.** Put L=a+c+1 and n=L+1. For each integer k place:

* T+(kn+c,0);
* -T+(kn+L,1).

Their union is exactly Z x {0,1}. On row 0, the first type supplies the interval [kn,kn+L-1] and the second its missing singleton kn+L. On row 1, the first supplies singleton kn+c, while the second supplies [kn+c+1,kn+c+L]. Thus each row is partitioned into successive blocks of length n. No cells lie outside the two rows. This proves S and therefore HP and plane, with no assertions concerning a cap or corner.

### 2. Every c=1 tile covers the plane

**Proved construction.** Write n=a+b+2 and let Lambda be generated by (2n,0) and (2,1). Place T and -T+(2a+1,0) at every lattice translate in Lambda.

The residue map phi(x,y)=x-2y mod 2n has kernel Lambda. It suffices to verify that the two tiles together represent every residue exactly once. Their horizontal bars have residues [-1,a] and [a+1,2a+2]. The upward stem has even residues 2a+4,2a+6,...,2n-2. The other stem has odd residues 2a+3,2a+5,...,2n-3. Together these are precisely all 2n residues. In particular there can be neither overlap nor uncovered cells after periodic extension.

Reflection exchanges a and c, so min(a,c)=1 suffices without the normalization a>=c.

### 2a. Every b=c=1 tile covers a bent strip of arm widths two

**Proved construction.** In Construction 1 set c=1 and restrict k to nonnegative integers. With L=a+2 and n=a+3 this tiles exactly the jagged half-strip

H = {(x,0):x>=0} union {(x,1):x>=1}.

Let sigma(x,y)=(y,x). A reflected copy sigma(H)+(0,1) is

H' = {(0,y):y>=1} union {(1,y):y>=2}.

These regions are disjoint and their union is exactly B={(x,y) in N^2: x<2 or y<2}. Thus H and H' provide an exact tiling of the bent strip. The tile list, for each k>=0, is:

1. T+(kn+1,0);
2. -T+(kn+a+2,1);
3. sigma(T)+(0,kn+2);
4. -sigma(T)+(1,kn+a+3).

This proves BS, and hence Q and S, for every a>=1. It applies also to the initially excluded a=4 and a=5; their upper-level obstructions are proved separately below. The construction uses a reflection across the diagonal, which is permitted by D4.

### 3. Every b=2 tile covers the plane

**Proved construction.** Put n=a+c+3 and let Lambda be generated by (n,0),(c+1,2). Place T and -T+(a+1,1) at every lattice translate.

Use representatives (u,j) with j=y mod 2 and u=x-floor(y/2)(c+1) mod n.

* Row j=0: T contributes its horizontal interval [-c,a], plus the upper stem endpoint residue -c-1. The other tile contributes its stem singleton a+1. Hence this row contains the n consecutive residues [-c-1,a+1].
* Row j=1: T contributes its first stem cell at residue 0. The other tile contributes its horizontal interval [1,a+c+1]=[1,n-2], plus the lower stem endpoint at residue n-1. Hence this row also contains every residue exactly once.

These 2n distinct residues give an exact periodic plane tiling.

### 3a. Exceptional four-copy plane family P(a,a+3,2,0)

**Proved construction, independently derived after a finite-patch clue.** Let b=a+3 (a>=2) and T=P(a,b,2,0). Since a+2+1=b, the horizontal bar and the stem each have b cells when the junction is allocated to the bar. Thus |T|=2b.

Let sigma(x,y)=(y,x), and let Lambda be generated by (4,4) and (b,-b). Its index is 8b. The four tiles in a fundamental motif are

1. A=T;
2. B=-sigma(T)+(b-2,-2);
3. C=-T+(b-1,1);
4. D=sigma(T)+(1,3).

Place this motif at every translate in Lambda. To prove this is a tiling, write d=x-y, choose q=floor(d/(2b)), and assign the quotient coordinates

    delta = d-2b*q in {0,...,2b-1},
    eta = y+b*q mod 4.

These coordinates exactly represent Z^2/Lambda. It remains to prove that the four tiles, with a total of 8b cells, represent each pair (delta,eta) once.

Splitting each tile into a horizontal rod and a vertical rod gives the following unnormalized (d,y) descriptions, with both interval endpoints included:

| Rod | d interval | y |
|---|---|---|
| A horizontal | [-2,b-3] | 0 |
| A vertical | [-b,-1] | -d |
| B horizontal | [0,b-1] | -2 |
| B vertical | [b-2,2b-3] | b-2-d |
| C horizontal | [1,b] | 1 |
| C vertical | [b-1,2b-2] | b-1-d |
| D horizontal | [-1,b-2] | 3 |
| D vertical | [1-b,0] | 1-d |

For negative d add (b,-b) to the cell; this adds 2b to d and subtracts b from y. The eight rods then yield the following four eta representatives at each delta:

| delta | four y values before reducing modulo 4 |
|---|---|
| 0 | 0,-2,3,1 |
| 1 through b-3 | 0,-2,1,3 |
| b-2 | -2,1,3,0 |
| b-1 | -2,1,-1,0 |
| b | 1,0,-2,-1 |
| b+1 through 2b-3 | b-delta,b-2-delta,b-1-delta,b+1-delta |
| 2b-2 | -b,2-b,1-b,3-b |
| 2b-1 | -b,3-b,1-b,2-b |

Every row gives all four residues modulo 4 exactly once. The intervals are disjoint and exhaustive when b>=5. This proves exact plane tilability for every a>=2, with no bounded-search assumption. Reflection gives the symmetric family with a=2 and b=c+3.

The initial P(2,5,2,0) pattern was found in an anchored patch. The four-copy HNF search `research/t_construct_four.py` separately found motifs for a=2,...,8; all general motifs above were checked for b=4,...,60. These are supporting checks, not substitutes for the quotient proof.

**Failure recorded:** the broader conjecture b=a+c+1 for arbitrary c was not supported. Four-copy searches failed for c>=3 (e.g. P(3,7,3,0)); this failure itself is not a non-tilability proof.


## 4. T boundary and quadrant obstructions


#### Corner placement lemma

A tile containing the southwest corner of a quadrant must have a crossbar endpoint at that corner, its crossbar along a quadrant boundary, and its stem pointing inward. A stem cell at the corner would force one of the two crossbar arms outside the quadrant. By diagonal reflection assume the first crossbar is `{(x,0):0<=x<=a+c}` and its stem is `{(r,y):1<=y<=b}`, where `r` is either `a` or `c`.

#### No quadrant when both crossbar arms have length at least two

Assume `a>=c>=2`. The tile covering `(0,1)` cannot have a horizontal crossbar: its crossbar would run from `x=0` to `x=a+c` and intersect the first stem. Nor can it cover `(0,1)` by a horizontal stem whose crossbar is at positive x: that vertical crossbar would extend below y=0, since both its downward arm choices are at least two. Thus, if `(0,1)` can be covered at all, the second tile has a vertical crossbar at x=0, running from y=1 to y=a+c+1, and its stem points right.

Now `(1,1)` is impossible. A horizontal crossbar containing it must start at x=1 (the cell `(0,1)` is occupied) and it meets the first stem at `(r,1)`. A vertical crossbar containing it must start at y=1 and meets the second tile's rightward stem. If instead `(1,1)` lies in the perpendicular stem, the crossbar would extend outside the quadrant: a horizontal crossbar through x=1 has an arm of length at least two to the left, and a vertical crossbar through y=1 has an arm of length at least two downward. This exhausts whether the cell lies on a crossbar or stem.

Consequently the four cells of a 2-by-2 corner cannot be covered even allowing arbitrary overhang through the two artificial upper/right edges. In particular no quadrant, bent strip, half strip, rectangle, or strong rep-tile implication through a quadrant is possible.

### Universal half-plane obstruction when c>=2 and b>=2

Put `A=a+c+1`, the number of crossbar cells, and use the half-plane `y>=0`. A tile touching row zero has exactly one of three forms:

1. `H`: its whole horizontal crossbar lies in row zero and its stem points upward.
2. `V`: a vertical crossbar starts in row zero, and its horizontal stem points left or right.
3. `S`: its perpendicular stem has its tip in row zero, points downward, and its horizontal crossbar is at height b.

These are exhaustive because the crossbar has positive arms in both directions. The argument below also proves the S exclusion for every `a>=c>=1,b>=2`.

#### Preliminary V exclusion when b>a

Suppose a boundary V has its crossbar at x=0, spanning y=0 through A-1, and its stem points right at height `r in {a,c}`. Consider boundary cell (1,0). If it belongs to a V, that V's crossbar intersects the original stem at (1,r). If it belongs to an S, its vertical stem does the same because `r<b`. If it belongs to an H, that H's crossbar must start at x=1; its upward stem has x-coordinate `1+s`, `s in {a,c}`. Since `1+s<=a+1<=b` and `r<=a<b`, that stem intersects the original stem. All options fail. Reflection handles a leftward V.

#### No boundary S when b>=2

Reflect horizontally if necessary, so a proposed S has its tip at (0,0), its crossbar at y=b, and its right crossbar arm of length a. Its neighbor (1,0) cannot belong to another S, since the two vertical stems/crossbars intersect. It cannot belong to a V when `b<=A-1`, since the V's crossbar contains (1,b), occupied by the S. When `b>A-1`, the preliminary V exclusion applies because `b>a`.

Thus (1,0) belongs to an H whose crossbar starts at x=1. Its upward stem is at `1+s`, `s in {a,c}`. Avoiding the original S's crossbar at height b requires `1+s>a`; hence its stem is exactly at x=a+1 (also when a=c).

The two tiles now enclose the nonempty rectangle

`{1,...,a} x {1,...,b-1}`.

Its left/right barriers are the two vertical stems, its bottom barrier the H crossbar, and its top barrier the S crossbar. Any other tile intersecting this finite component must lie wholly within it. No orientation fits: a horizontal-crossbar tile requires width A>a, while a vertical-crossbar tile would require both `b+1<=a` and `A<=b-1`, which are incompatible. Contradiction.

#### No boundary V when c>=2 and b>=2

If `b>=A-1`, then `b>a` and the preliminary exclusion applies. Assume instead `b<=A-2`. Put a proposed rightward V's crossbar at x=0, from y=0 to A-1, with its junction at height `r in {a,c}`. Since S is excluded and another V at (1,0) would intersect its right stem, (1,0) belongs to an H with crossbar x=1 through A and stem at `j=1+s`, `s in {a,c}`. If these already overlap there is nothing to prove; otherwise consider (1,1), which is vacant because `r>=2` and `j>=3`.

- A horizontal crossbar through (1,1) must start at x=1, since (0,1) is occupied. Its length A makes it intersect the existing H stem at (j,1).
- A vertical crossbar through (1,1) must start at y=1, since (1,0) is occupied. It intersects the proposed V's stem at (1,r).
- If (1,1) lies on a vertical perpendicular stem, its horizontal crossbar can only be at height 0 or at a height between 2 and b+1. Height 0 overlaps the boundary H; at any other possible height its left arm, of length at least two, crosses x=0 within the original V's crossbar, because `b+1<=A-1`.
- If (1,1) lies on a horizontal perpendicular stem, its vertical crossbar is centered at y=1 and extends below y=0, since both crossbar arms are at least two.

All cases fail. Leftward V tiles are excluded by reflection.

#### An unavoidable gap above the boundary

Only H tiles can now touch row zero. Their length-A crossbars partition the boundary into consecutive intervals. Index their junction offsets by `r_k in {a,c}`. The number of vacant row-one cells between consecutive upward stems is

`g_k=A-1+r_(k+1)-r_k`,

so `g_k>=2c>=4`. At least one has `g_k<=A-1`: otherwise every consecutive offset would strictly increase, impossible for the two-element set {a,c}. Fix such a gap of width `4<=g<A`.

Every tile covering a vacant row-one cell is new and has its lowest row at y=1, because row zero is already entirely occupied. Its horizontal crossbar cannot be in row one: it would have to fit inside the gap, whose width is less than A. Thus each of the g consecutive cells is the bottom of either a V crossbar or an S stem. A V supplies a vertical segment through rows 1,...,A, with a horizontal stem at height `1+r<=a+1<=A`. An S supplies a vertical segment through rows 1,...,b+1 and a horizontal crossbar at height b+1.

- If `b+1<=A`, any S's crossbar intersects the vertical segment of its neighboring gap tile. Every gap tile has at least one such neighbor because g>=4. Hence all gap tiles would be V. An adjacent V pair can be disjoint only if their stems point away from one another; three consecutive V tiles are impossible.
- If `b+1>A`, take any V in the gap. At its stem's height, every adjacent gap tile has a vertical segment, and either outer boundary stem is also present because its height b is at least A. Therefore the first cell of the V's stem overlaps its neighbor, whatever direction it points. There can be no V. All gap tiles would be S, but adjacent S crossbars intersect.

Both cases contradict coverage. Therefore **P(a,b,c,0) cannot tile a half-plane whenever a>=c>=2 and b>=2**. Consequently it cannot tile a strip, quadrant, bent strip, half strip, or rectangle. Plane tileability remains a separate question.

### Completing the half-plane obstruction for c=1

In this section `A=a+2`.

#### Local blocked-row lemma

Assume `b<=A-1`. Suppose a row y=h has a run of g cells that are not covered by some already placed tiles, with every cell immediately below the run occupied, and both immediate horizontal neighbors of the run occupied. If `3<=g<A`, the partial placement cannot be extended to a tiling.

A horizontal crossbar covering a run cell would have to fit wholly within the run, since crossing either end intersects an occupied cell; its length A makes this impossible. A horizontal perpendicular stem covering a run cell has its junction in the run (otherwise it crosses an occupied end). Its vertical crossbar has a positive downward arm, which intersects the occupied floor immediately below the junction. This is also impossible.

Consequently every run cell must be the bottom of a vertical crossbar V, or the bottom tip of a vertical perpendicular stem S. The occupied floor ensures it is the bottom: extending its vertical segment even one cell lower would overlap that floor. The V segments run from h to h+A-1; the S segments run from h to h+b. An S crossbar at h+b intersects the vertical segment of either neighboring run tile because `b<=A-1`. Every cell in a run of length at least three has at least one run neighbor. Thus there are no S tiles. But three adjacent V tiles cannot be disjoint: every adjacent pair would require its stems to point away from each other. Contradiction.

The same adjacency argument shows that any consecutive run of V/S starters at one level has length at most two whenever `b<=A-1`, even when a larger surrounding row contains H crossbars as well.

#### The range b>a

The preliminary boundary-V lemma and universal boundary-S lemma leave only H tiles on the boundary. Their junction offsets are 1 or a, so at least one gap above row zero has width `2<=g<=A-1`.

If `b=a+1=A-1`, an S in that gap intersects its neighboring starter. All gap tiles would be V. Three V tiles are impossible, and if g=2 their stems must point outward; their junction heights are at most `a+1=b`, so both outward stems hit the original H stems bounding the gap. If `b>=A`, every V stem hits either a neighboring starter's vertical segment or one of those boundary H stems, because its junction height is at most a+1<=b. Then all gap tiles would be S, and adjacent S tiles overlap. Thus no half-plane tiling exists when b>a.

#### Necessary form of a boundary V when 2<=b<=a

Suppose a boundary V has its vertical crossbar at x=0, y=0,...,A-1 and its stem pointing right at height `r in {1,a}`. Boundary cell (1,0) is neither S nor V, by the previous lemmas, so it belongs to an H with crossbar x=1,...,A and stem at `1+s`, `s in {1,a}`.

If r=a, cell (1,1) is vacant and impossible:

- A horizontal crossbar through it must start at x=1 and hits the neighboring H's stem.
- A vertical crossbar through it must start at y=1 and hits the proposed V's stem at height a.
- A vertical perpendicular stem through it has its horizontal crossbar at height 0 or at some height at most b+1<=a+1=A-1. Height 0 overlaps the boundary H; at every other possible height the crossbar reaches x=0 and overlaps the original V's crossbar.
- A horizontal perpendicular stem through it has its vertical crossbar centered at height 1. A downward crossbar arm of length a leaves the half-plane. With downward arm 1, its crossbar reaches row zero. Its junction cannot be at x<=0 because its connecting horizontal stem would cross the occupied cell (0,1). A junction to its right has x<=b+1<=a+1 and hence overlaps the boundary H in row zero.

Therefore r=1. If s=1, the two original stems overlap at (2,1), since b>=2. Hence s=a. Up to reflection, **every possible boundary V has the following forced neighbor**:

- `V0`: crossbar x=0, y=0,...,a+1; stem y=1, x=1,...,b.
- `H0`: crossbar y=0, x=1,...,a+2; stem x=a+1, y=1,...,b.

The assertions below use only these two tiles and forced tiles in their gap; no artificial side boundary is imposed on the half-plane.

#### Excluding this V configuration when a-b>=3

Row one has an uncovered run x=b+1,...,a of length a-b, with occupied floor H0, left end V0 at (b,1), and right end H0 at (a+1,1). Its length lies between 3 and A-1. The blocked-row lemma applies.

#### Excluding this V configuration when a-b is 0, 1, or 2 and b>=3

In every case we obtain a blocked row of width b, which satisfies `3<=b<A`.

- **a=b.** Row two, x=1,...,b, has floor V0's stem in row one and side walls V0 at x=0 and H0 at x=b+1. These cells are not covered by V0 or H0. Apply the blocked-row lemma.

- **a=b+1.** Row one's sole gap cell x=b+1 starts a V or an S tile G: an H crossbar cannot fit between its two occupied neighbors. If G is an S, its crossbar is at height b+1>=4, and its vertical segment provides a wall at x=b+1 in row two. If G is a V with the long lower crossbar arm, its horizontal stem is at height a+1=b+2>3, so it supplies the same wall without filling the interior in rows two or three. In these cases use the width-b gap x=1,...,b in row two, with floor V0's stem and walls V0 and G.

  The remaining possibility is a V with lower crossbar arm 1 and stem at height two. It cannot point right, because its first stem cell meets H0's stem at x=b+2, y=2. It therefore points left, filling exactly x=1,...,b in row two. Use the width-b gap in row three instead; its floor is this new stem, its left wall V0 reaches height a+1=b+2>=5, and its right wall G reaches height A=b+3. No part of the forced tiles occupies the interior of that row-three gap.

- **a=b+2.** Row one's gap consists of x=b+1,b+2. Its two cells start V/S tiles. An S's crossbar would intersect the neighboring starter, so both are V, with their stems pointing outward. Call the left one G. The right V cannot have its stem at height two: a rightward stem there meets H0 at x=b+3, y=2. Its stem is therefore at height a+1=b+3>3 and does not affect the interior gaps used below.

  If G has its stem at height a+1, use the width-b gap x=1,...,b in row two. Its floor is V0's stem, and its walls are V0 and G. If G has its stem at height two, that leftward stem fills exactly x=1,...,b in row two; use row three instead. V0 reaches height a+1=b+3 and G's vertical crossbar reaches height A=b+4, so both side walls remain present. In either case the chosen width-b run is otherwise untouched by the forced tiles, and the blocked-row lemma applies.

This excludes every boundary V for b>=3 with b<=a. For b=2 the same argument already excludes a>=5; the three smaller possibilities fall within the finite reduction below.

#### No all-H boundary when a>=7 and 2<=b<=a

For a>=7 a boundary V is impossible by the preceding cases: either a-b>=3 or b>=a-2>=5. Boundary S is also impossible, so row zero is partitioned by H crossbars.

Their junction offsets are 1 or a. Two consecutive equal offsets would create a width-(a+1) gap in row one, forbidden by the blocked-row lemma because `3<=a+1<A=a+2`. Thus the offsets alternate, producing alternating gaps of widths 2 and 2a.

Take a width-2a gap. Every covering tile has lowest row one, since all of row zero is occupied. It contributes either an H crossbar of A=a+2 cells, or a single V/S starter. There is room for at most one H crossbar. If there is no H crossbar, a V/S run of length 2a>=3 is impossible by the starter adjacency argument. If there is one H crossbar, the two runs of starters at its ends have total length

`2a-(a+2)=a-2`.

Each run has length at most two, again by the starter adjacency argument. Hence a-2<=4, or a<=6, contradiction.

#### Fifteen finite remaining cases and independently checked certificates

The human arguments leave only `c=1, 2<=a<=6, 2<=b<=a`, exactly fifteen parameter triples. For each, a rectangle of required cells of width `3(a+2)` and height 3 cannot be covered by pairwise disjoint complete tiles lying in y>=0, **with arbitrary overhang past the finite patch's left, right, and upper edges**. Each such obstruction therefore excludes a complete half-plane tiling.

Explicit exhaustive branching DAGs are supplied in `results/t_hpcert_{a}_{b}_1.json` (with the displayed parameter values substituted). Their node counts range from 693 to 1832. The first independent checker regenerates placements separately from the solver. A second checker was independently implemented in `src/t_boundary_verify_finite.py`, without importing the search engine, its orientation code, or its first checker. It:

1. Regenerates D4 shapes by four rotations of the original and its reflection.
2. Enumerates every complete translated tile containing any required cell and lying in y>=0.
3. Verifies that the certificate lists exactly this placement universe.
4. At each DAG node, uses explicit occupied-cell sets to verify that its selected cell is uncovered and its branches exhaust every nonoverlapping tile covering that cell.
5. Verifies every child is the exact enlarged occupied set. Strict enlargement prevents circular proofs. A leaf is accepted only when no legal covering tile exists.

Reproduction: `python3 src/t_boundary_verify_finite.py`. All fifteen passed in approximately 0.6 seconds. The separate readback is `results/t_boundary_finite_second_check.json`.

#### Resulting T boundary classification

The combined, independently reviewed proof establishes **no half-plane tiling for any T with b>=2**. Together with the separate two-row strip construction for b=1, this gives **half-plane tileability exactly when b=1**. The earlier c>=2 corner obstruction and the separate bent-strip construction for b=c=1 then give **quadrant tileability exactly when b=c=1**.

Plane tileability and the half-strip/rectangle distinction are addressed by the separate proofs in this appendix.


## 5. Clean-corner half-strip and rep-tile obstructions


### Why the two exceptions cannot tile a half-strip

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

### Full no-rep-tile theorem, including a=4

The following argument uses the full vertical-wall height to include the sharp case `a=4`.

**Theorem.** For every integer `a>=4`, `P(a,1,1,0)` is not a rep-tile.

The exact corner potentials above are nonnegative. The wall heights of alpha,
beta, gamma, transposed beta, transposed gamma are respectively `4,5,5,6,6`.
Every query has relative x coordinate at most 7. Therefore every whole tile
chosen to cover a query has rightmost relative coordinate at most `a+8`:
the largest possible difference of two tile-cell x coordinates is `a+1`.
`verify_rep_ratio` checks all transition inequalities and query bounds by exact
integer arithmetic; its receipt is `results/t_rep_ratio_verified.json`. For
the universal affine edges it checks the nonnegative slope of each slack and
its nonnegative value at `a=6`, which proves the inequality for all `a>=6`.

Suppose a nontrivial rep-tiling exists. Its enlargement factor is an integer
`k>=2`: the enlarged polygon has boundary segments corresponding to unit-length
edges of the original polyomino, and every boundary segment of a union of
lattice tiles has integral length. Iteration provides arbitrarily large integer
scales, so choose one with `k>=a+2`.

Reflect the enlarged T horizontally and put the origin at the lower-right end
of its long arm. In cell coordinates the enlarged region is

```text
{0 <= X < (a+2)k, 0 <= Y < k}
  union {ak <= X < (a+1)k, k <= Y < 2k}.
```

The part `X<ak` is a rectangle of height `k`; the stem starts at `X=ak`.
Start the verified alpha certificate at `(0,0)`. Its initial artificial walls
have height 4, below `k`. Every local query has x at most 7, and every whole tile
chosen through it has x at most `a+8<ak`. Hence each actual chosen tile stays
before the stem. Its cells have height below `k`, so the certificate's supported
query rule never asks for a cell outside the enlarged T. The first successor
strictly increases both coordinates; its walls and floor are now actual tile
cells, rather than initial exterior boundary cells.

Inductively let a current corner have origin `(X,Y)`, type `s`, and vertical
wall height `w`, and suppose `X<ak`. Since the wall lies at x=`X-1<ak`, all its
cells are in the height-`k` rectangular arm. Thus `Y+w<=k`. The potential
invariant `X-4Y<=-h(s)` gives

```text
ak-X >= (a-4)k + 4w + h(s).
```

This lower bound strictly exceeds `a+8`. Indeed the difference is exactly

```text
(a-4)(k-1) + 4(w-4) + h(s) + 4,
```

which is at least 4 for `a>=4`, `k>=1`, `w>=4`, and `h(s)>=0`.
Consequently every whole tile used in the next local certificate again lies
strictly before the stem. Its actual cells have height below `k`; all supported
queries are valid cells of the rectangular arm. All known cells in this local
certificate have x below `ak`, so the successor floor, which includes a cell
at its new origin's x coordinate, forces the new origin also to satisfy `X'<ak`.
This closes the induction without making any query across the concave boundary.

The verified transition graph forces the corner heights to grow without bound,
but every corner wall remains within the rectangular arm of height `k`. This
contradiction proves the theorem for every `a>=4`, including the sharp case
`a=4`. The inference is separate from, and stronger than merely invoking, the
no-half-strip theorem.


## 6. Negative T-plane cases


### Human proof: all c>=3 and 3<=b<A

This proof has been independently audited and accepted. Let A=a+c+1. Use the local blocked-row lemma: a run of g available cells with occupied floor and both immediate ends is impossible for 3<=g<A, provided b<=A-1. Rotations are allowed. Every use below has a full occupied floor, including its two end cells, supplied by specified placed tiles.

**Concave-corner reduction.** Put an upright tile O at (0,0). At (1,1) the occupied neighbors (0,1),(1,0) force any covering tile to end an arm there. A junction or an interior arm cell would hit at least one neighbor. There are six geometric types, allowing either a or c as the relevant crossbar arm:

1. Horizontal crossbar begins at (1,1), with junction (1+r,1), r in {a,c}. If its stem points up, row two between its stem and O's stem is a blocked run of length r. Thus the stem points down; disjointness then requires its junction beyond O's east tip.
2. Vertical crossbar begins at (1,1), with junction (1,1+r). If its stem points right, column two between O's crossbar and the new stem is a rotated blocked run of length r. Thus the stem points left, and its junction must lie above O's north tip.
3. A perpendicular horizontal stem ending at (1,1) has junction (b+1,1). Row two between O's stem and its vertical crossbar is a blocked run of length b.
4. A perpendicular vertical stem ending at (1,1) has junction (1,b+1). Column two between O's crossbar and its horizontal crossbar is a rotated blocked run of length b.

The same argument applies at (-1,1). Both corners cannot be vertical-crossbar tips with junctions above O: their vertical segments start in row one at x=-1 and x=1, and the horizontal stem at the lower of their junction heights reaches the other column because b>=3. Thus at least one corner is covered by a horizontal crossbar whose stem points down.

Reflect horizontally so it is (-1,1). Denote its covering tile by U. Its horizontal crossbar is exactly x=-A,...,-1 in row one, and its stem points down. This assertion does not require either crossbar arm to match O's adjacent arm; the full bar length fixes the interval.

**First cell above this floor.** Consider p=(-1,2), whose lower and right neighbors belong to U and O. Every covering tile ends an arm at p.

- A horizontal crossbar ending at p has junction (-1-r,2), r in {a,c}. A downward stem hits U's row-one bar. An upward stem creates a blocked row in row three, between that stem and O's stem, of length r.
- A horizontal perpendicular stem ending at p has junction (-1-b,2); since b<=A-1 this junction lies above U's bar and its downward crossbar arm hits U.
- A downward perpendicular-stem tip at p has horizontal crossbar at y=b+2. Column x=-2 between U's row-one bar and that new crossbar is a blocked vertical run of length b.
- A vertical crossbar starting at p has junction (-1,2+r). A leftward stem creates a blocked vertical run of length r in column -2, between U's bar and that stem.

Therefore p can only start a vertical crossbar with a rightward stem. Call this tile V. Its vertical bar is the entire column x=-1, rows 2,...,A+1. Disjointness from O additionally implies its stem lies above y=b, but this inequality is not needed below.

**Next cell.** Consider q=(-2,2), with occupied floor U and immediate right neighbor V.

- A horizontal crossbar ending at q has junction (-2-r,2). A downward stem hits U, and an upward stem creates a blocked row of length r in row three between itself and V.
- A vertical crossbar starting at q with leftward stem creates a blocked vertical run of length r in column -3. A rightward stem hits V: its height 2+r is at most A+1.
- A downward perpendicular-stem tip at q has crossbar at y=b+2<=A+1, which hits V.
- A horizontal perpendicular stem ending at q has junction (-2-b,2). If b<=A-2, its downward crossbar arm hits U's floor.

Only b=A-1 leaves one possible case: a rightward perpendicular stem with junction (-A-1,2), ending at q. Its row-two stem fills x=-A,...,-2. Row three above it now has a blocked run of length A-1=b between its own vertical crossbar at x=-A-1 and V's column at x=-1. This contradicts the blocked-row lemma.

Thus the argument proves non-tilability whenever c>=3 and 3<=b<=a+c.

### Extension to every b>=A when c>=3

This extension has been independently audited and accepted. The tile types H,V,S refer to their lowest occupied row: H has a horizontal crossbar, V a vertical crossbar, and S its perpendicular-stem tip. The run cells in the following lemmas are disjoint from the specified supporting tiles. Thus any tile covering the run is distinct from its floor/end supports.

**Long-stem small-gap lemma.** Assume b>=A and 3<=g<A. Consider g consecutive unfilled cells in row h with occupied floor immediately below them and occupied immediate endpoints. If g=3, additionally suppose one endpoint wall is occupied at both heights h+a and h+c. Then the gap is impossible.

Indeed, no H bar fits. No horizontal perpendicular stem can cover it: a junction inside would have its downward crossbar arm hit the floor, and a junction outside would cross an occupied endpoint. Every cell therefore starts a V or an S. A V's stem occurs at h+a or h+c, within both a neighboring V's height A-1 and a neighboring S's height b. It must point out of the run and can occur only at an end. Adjacent S tiles overlap at the height h+b. If g>=4, the two middle starters are therefore impossible. If g=3, the tall wall prohibits a V at one end, so that end and the middle are adjacent S tiles.

**Long-stem length-b gap lemma.** Assume b>=A, c>=3. Consider a run of b cells in row h, with occupied floor and immediate endpoint walls. The supporting tiles leave the run clear. Suppose the left endpoint wall also occupies its cell in row h+1 and its tile does not occupy any interior run coordinate in row h+1. Then the gap is impossible. In all uses below both walls are straight at these two rows, so the asymmetric hypothesis holds in either direction.

If an H bar covers part of the run, choose the leftmost H bar. It points its stem up, because a downward stem hits the floor. If its bar begins at x=L and its junction is x=L+r, r in {a,c}, the r cells immediately above its left arm are a small gap in row h+1. Their floor is this bar. Their right wall is its long upward stem. Their left wall is either the original endpoint, or a V/S starter immediately preceding the first H bar. Such a starter has no horizontal cells in row h+1 because c>=3 and b>=A. All these gap cells are clear of the floor and wall tiles. The right wall reaches h+1+a, since b>=a+1. The small-gap lemma excludes this configuration. Consequently there is no H bar anywhere in the length-b run. All cells are V/S starters; only its two end cells could be V, and at least b-2>=A-2>=5 consecutive interior S tiles remain. Adjacent S tiles overlap.

#### Extending the corner reduction

For the concave corner (1,1) of upright O, the two away-pointing crossbar cases yield the same small gaps of length r in {a,c} as before. The H-up case has tall walls provided by upward stems. The V-right case has one tall wall provided by the new rightward stem, so the rotated small-gap lemma applies even if r=3. More precisely, that stem reaches x=b+1>=a+2, covering both possible starter-junction coordinates x=2+a and x=2+c.

The horizontal perpendicular-stem-tip case yields a length-b gap in row two between O's stem and the new vertical crossbar, above the new horizontal stem. Its walls continue straight through row three because b>=A and c>=3. The vertical perpendicular-stem-tip case yields the rotated length-b gap in column two, between O's horizontal bar and the new horizontal crossbar, next to the new vertical stem. Its walls continue through column three because both relevant horizontal arms have length at least three. Thus both perpendicular-stem cases are impossible by the length-b gap lemma.

The remaining corner cases, and the exclusion of both corners choosing vertical crossbars, are exactly as in the short-stem proof. Hence some antiparallel pair again exists, normalized as O upright at zero and U downward with row-one bar x=-A,...,-1.

#### Extending the two-cell contradiction

At p=(-1,2), a horizontal crossbar pointing up produces the earlier length-r small gap in row three; O's wall reaches all required heights because b>=A>=a+4. A downward stem still hits U's floor. A vertical crossbar whose stem points left produces a rotated length-r small gap whose tall wall is that new long stem.

The horizontal perpendicular-stem case now has junction (-b-1,2), outside U's floor. Its horizontal stem fills x=-b,...,-1 in row two. Row three above this stem is a length-b gap, between its vertical crossbar at x=-b-1 and O's stem at x=0. Both walls continue through row four (c>=3, b>=A), so the length-b gap lemma excludes it.

The vertical perpendicular-stem case at p has junction (-1,b+2). Column -2 contains a length-b gap y=2,...,b+1, with floor to its right supplied by that vertical stem, and endpoints supplied by U's row-one bar and the new bar at y=b+2. Both endpoint bars continue through column -3. Apply the rotated length-b gap lemma.

Thus p still forces V, a vertical crossbar x=-1, y=2,...,A+1 with rightward stem.

But this forced V is already impossible. Its rightward stem contains (0,2+r), r in {a,c}, and 2+r<=a+2<A<=b. This cell lies in O's original upward stem. The long-stem proof therefore stops at p, and the two reviewed regimes together prove **every c>=3,b>=3 T is non-tileable in the plane**.

### Checked universal certificate for c=2 and 3<=b<a+3

The symbolic branch tree `results/t_plane_negative_corners_two_short_d10.json` is complete: 300 nodes, 208 terminal contradictions, and at most seven additional tiles beyond the anchored original. Its hypotheses are a>=2, c=2, d=0, and 3<=b<a+3, with no upper bound on a or b.

An independent checker, `src/t_plane_negative_verify_symbolic.py`, represents every tile as the union of two Cartesian rectangles and checks separation by the four rectangle-pair tests. This differs from the search's specialized cross-intersection formulas. At every branch it permits an arbitrary next integer junction and any of the eight D4 orientations; it does not assume the cell is an arm tip. All 2,218 queries were UNSAT, including tile-orientation validity, selected-cell emptiness, child coverage, and exhaustive alternatives. The finite tree's ancestry and acyclicity are checked separately. Standalone formulas and the readback are in `results/t_plane_negative_certificate_two_short/`.

This is a checked unbounded-parameter obstruction certificate, rather than a bounded parameter survey. Its independent arithmetic validation uses Z3, and the full geometric replay also compiles in Lean, as recorded below. The geometric reduction to impossibility is: normalize one tile of a hypothetical whole-plane tiling as the root; its selected uncovered cell must be covered by one exhaustive child; follow the finite tree until its terminal cell admits no disjoint cover. The certificate uses complete unbounded tiles and imposes no artificial rectangle boundary.

Reproduce the independent audit with `python3 src/t_plane_negative_verify_symbolic.py results/t_plane_negative_corners_two_short_d10.json`.

### Human proof for c=2, b>A=a+3

The following geometric proof has passed three independent reviews. Its arbitrary-width gap lemma covers every parameter in this domain.

Throughout, a>=2, c=2 and b>A=a+3. Reflecting a placed tile may put its long horizontal arm on either side; below we only assume both horizontal arms have length at least two. This avoids assuming the forced corner lies on the long-arm side.

#### Deep-wall gap lemma, with arbitrary width

Let g>=3 consecutive run cells in row h be unoccupied by specified supporting tiles. Suppose their immediate lower neighbors and their immediate horizontal endpoints are occupied by those supporting tiles. Suppose the left endpoint wall is also occupied at every height from h through h+1+a, and its tile has no cells in the interior run coordinates in row h+1. The right wall need only occupy its endpoint cell in row h. Assume b>=A and c=2. Then this configuration is impossible. The reflected and rotated forms hold as well.

To prove the lemma, first note two short-run facts. For 2<=q<A, a run with a full occupied floor and both endpoint walls reaching heights h+2 and h+a is impossible: no H crossbar fits, a horizontal perpendicular stem either crosses an endpoint or has its vertical crossbar hit the floor, and thus every cell starts V or S. A V's stem at height h+2 or h+a intersects the next starter in its direction, unless it points outward at an end; the tall endpoint walls prohibit those end V tiles too. All starters would be S, and adjacent S crossbars overlap at height h+b. Also, for a run of three cells with only one such tall wall, the V at that end is excluded, the middle cannot be V, and two adjacent S tiles remain. For q>=4 and q<A, even without tall walls the two interior starters must be adjacent S tiles.

Now prove the arbitrary-width assertion. If any H bar covers part of the run, choose the leftmost one. It points its stem upward because the occupied floor prohibits a downward stem. Write its first cell as x=L and its junction as x=L+r, r in {2,a}. The r cells just above its left arm, in row h+1, have this H bar as floor and its upward stem as right wall. Their left wall is either the original deep endpoint wall, or the immediately preceding V/S starter. Such a preceding starter exists if L is not the first run cell, since this was the leftmost H bar. It has no lateral cells in row h+1: V's earliest junction is at h+2, and S's junction is at h+b. Its vertical segment reaches h+1+a, since its length beyond its bottom is A-1=a+2 for V, and b for S. The new H stem likewise reaches h+1+a because b>=a+1. Both short-gap walls are therefore tall enough, and the r cells are clear of the floor and wall tiles. Since 2<=r<A, the short-run fact excludes this H bar.

There is consequently no H bar in the original run. Every cell starts V or S. V can occur only at an end; adjacent S starters overlap. If g>=4, its two interior positions are already an impossible adjacent S pair. If g=3, the deep wall prohibits V at the left end, again leaving adjacent S tiles. This proves the lemma for every g>=3, with no upper bound on g.

#### No antiparallel horizontal-crossbar concave pair

Place O upright with junction (0,0), and suppose a downward-stem tile U covers the left concave corner (-1,1) with its horizontal crossbar. U's bar is exactly x=-A,...,-1 in row one. We show p=(-1,2) has no cover. Its occupied lower and right neighbors force any covering T to have an arm tip at p.

1. A horizontal crossbar ending at p has junction (-1-r,2), r in {2,a}. Its downward stem hits U's floor. Its upward stem makes a row-three gap of length r between itself and O's upward stem. Both walls reach height 3+a because b>=a+4; use the two-deep-wall short-run fact above.
2. A vertical crossbar starting at p has junction (-1,2+r). A rightward stem hits O at (0,2+r), since 2+r<=a+2<b. A leftward stem makes the rotated short gap of length r in column -2, between U's bar at y=1 and the new horizontal stem at y=2+r. Both walls are deep: U extends to x=-A=-a-3, beyond the required coordinate -2-a, and the new stem extends to x=-b-1.
3. A horizontal perpendicular stem ending at p has junction (-b-1,2). Above its row-two stem, row three has a length-b run x=-b,...,-1. The right wall is O's stem, which reaches height 3+1+a=a+4<=b and is straight in row four. The left endpoint is the new vertical crossbar. Apply the reflected deep-wall gap lemma.
4. A vertical perpendicular stem ending at p has junction (-1,b+2). Column -2 has a length-b run y=2,...,b+1, with occupied floor to its right and endpoint bars supplied by U and the new tile. Its lower endpoint wall U reaches the required column -3-a=-A exactly. At column -3 U has no cells in the run interior: even if this is U's own junction column, its stem points downward from row one. Apply the rotated deep-wall gap lemma.

All arm-tip types are excluded. Thus such an antiparallel pair is impossible, regardless of which horizontal arm of O is long.

#### What may cover a concave corner

At a concave corner, a covering tile must have an arm endpoint there because one horizontal and one vertical neighbor are already occupied.

At (1,1) of an upright tile O:

- An upward-stem horizontal crossbar starting at x=1 creates a gap of length 2 or a in row two. Both side stems reach all required heights 2+a; the two-deep-wall short-run fact excludes it.
- A downward-stem horizontal crossbar is the forbidden antiparallel pair just proved, after reflection.
- A horizontal perpendicular-stem tip creates a length-b gap in row two between O's upward stem and the new vertical crossbar, with its horizontal stem as floor. O's wall reaches 2+1+a=a+3<=b and is straight in row three. The deep-wall gap lemma excludes it.
- A vertical crossbar whose horizontal stem points toward O hits O's stem at height 1+r<=a+1<b.
- A vertical crossbar whose horizontal stem points away from O creates a rotated gap of length r in column two. If r=a>=3, the one-tall-wall short-run fact excludes it: the outward new stem reaches every required coordinate 2+a. Consequently only r=2 is possible (including a=2).

The only remaining alternatives are therefore an away-pointing vertical crossbar with lower arm 2, or a vertical perpendicular-stem tip whose junction lies at height b+1. At the two concave corners of one upright T, both covers cannot be perpendicular-stem tips: their horizontal crossbars would share row b+1 at junctions distance two apart, and their arms have length at least two.

Thus some tile has an away-crossbar corner. Reflect horizontally so this is its right concave corner. Let its upright junction be (0,0); its east arm can be a or 2. Its forced corner tile U has junction (1,3), arms (b,a,0,2), and vertical bar x=1, y=1,...,A.

#### Forced R, W, Z and a finite boundary interval

Column two has the two-cell run y=1,2, with occupied floor on the left from U's vertical bar, lower endpoint supplied by O's crossbar at (2,0), and upper endpoint supplied by U's rightward stem at (2,3). The upper wall continues far enough right to prohibit an outward V starter there. Both starters can only be V or S in the rotated sense. Adjacent S starters overlap; an internal-pointing V intersects its neighbor. Therefore the lower cell starts a horizontal crossbar R pointing its stem down, and the upper cell is a horizontal perpendicular-stem tip W.

R's horizontal bar is exactly row one, x=2,...,A+1. Its junction offset may be 2 or a; no uniqueness is claimed. W's junction is (b+2,2), its perpendicular stem points left, and its horizontal segment fills x=2,...,b+2 in row two. Its vertical arm order can be (a,2) or (2,a); neither is assumed.

At W's upper-left concave corner (b+1,3), the covering tile is U, whose rightmost perpendicular-stem tip is precisely this cell. The two concave corners of W cannot both have perpendicular-stem covers, so its lower-left concave corner (b+1,1) must have the away-crossbar cover with near arm 2. This forces Z to have junction (b-1,1), arms (2,0,a,b), and horizontal bar x=b-a-1,...,b+1 in row one.

Consider the b cells in row one, x=2,...,b+1, immediately below W's long stem. Its endpoint cells are covered by H-down bars R and Z. R and Z are distinct because their right endpoints A+1 and b+1 differ when b>A. If they overlap, the contradiction is already complete; otherwise they cover the two ends of this finite boundary interval. Its outside endpoint cells at x=1 and x=b+2 are occupied by U and W, respectively.

Every other tile covering a cell of this interval is, in the downward direction, H, V, or S. A horizontal perpendicular stem would either have its junction inside the interval and hit W's ceiling with its upward crossbar arm, or cross an occupied outside endpoint.

There is no V. Every V is strictly inside the interval because its endpoint cells already belong to R and Z. Its neighbor in its horizontal-stem direction is therefore inside the interval. If the neighbor is V or S, the old V stem hits its vertical segment because its junction depth is at most a<b. If it is H, that bar begins at the next cell, and its downward stem is at horizontal distance at most a+1<b and reaches the old V's junction depth. The two stems intersect.

There is no S either. An S is likewise strictly interior. Choose the direction of its length-a horizontal crossbar arm. Its next boundary cell in that direction is inside the interval. It cannot be S, since their crossbars at depth b would intersect, and it cannot be V. It is thus H. Avoiding the old S's crossbar forces this H's junction to be distance a+1 away. (For a=2 both possible arm names give the same distance; for a>=3 the other possible distance 3 is at most a and would intersect.) Between the old S's vertical stem, the new H's vertical stem, its boundary crossbar, and the old S's depth-b crossbar, an a-by-(b-1) rectangle is enclosed. The support tiles do not occupy its interior. No T fits inside it: the horizontal-crossbar orientation has width A>a, and the vertical-crossbar orientation has width b+1>a. The enclosure is impossible.

Thus the entire interval consists of contiguous H-down bars. Since b>A, it contains at least two bars. Take two consecutive bars, with junction offsets r,s in {2,a} from their respective first cells. The cells immediately below their shared boundary row and strictly between their junctions form a run of length

    g=A-1+s-r >= A-1+2-a = 4.

Its entire ceiling is occupied by the two bars, and its side walls are their downward stems. They are straight in the next row and extend to depth b, beyond the required depth a+2. The rotated deep-wall gap lemma applies to this run of arbitrary width g>=4. Contradiction.

This proves **every c=2, b>a+3 T is a non-tiler**, and completes the negative T-plane classification together with the reviewed c>=3 theorem and the Lean-certified c=2 short-domain theorem.

The c=2 short-domain certificate has now been replayed in Lean 4.33.1. `TPlane.two_short_no_anchored_plane` quantifies over arbitrary infinite placed-tile sets, all D4 orientations, full integer-cell coverage, and ordinary cellwise disjointness. Its 2,700 arithmetic lemmas are proved by `omega`; no Z3 result is trusted by the kernel. The compiled theorem uses only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, with no `sorry` or added axiom. `TilingSymmetry.lean` proves normalization of an arbitrary tiling; `PolyominoFormal.short_stem_two_arm_no_plane` in `PlaneObstructions.lean` supplies the unconditional wrapper. Sources, compile instructions, and exact scope are in `lean/TPlaneREADME.md`; hashes and logs are in `research/TPlane_verified_manifest.json` and `research/TPlane_*_compile.log`.

### Lean formalization progress: subsequent complete-world theorems

`lean/TPlaneShort.lean` now compiles `TPlaneShort.no_plane` for every
`a>=c>=3` and `3<=b<=a+c`. This is an actual `¬Tiles a b c 0 Plane`
statement, including kernel-checked selection and D4 normalization of an
arbitrary initial tile. Its proof is the local concave-corner reduction,
the antiparallel pair, and the two forced cells described above. All
supporting gaps are applications of `THalfPlaneStarters.blocked_short_run`
to arbitrary infinite tilings and unions of whole supporting tiles.
The only reported axioms are `propext`, `Classical.choice`, `Quot.sound`.

`lean/TPlaneLong.lean` now compiles the entire long-stem proof and
`TPlaneLong.three_arms_no_plane` for every `a>=c>=3,b>=3`, combining both
stem regimes. The two rotated length-b cases use the independently
formalized `TPlaneDeep.weak_left_run`. The long proof simplifies the
human route further: after excluding the antiparallel and perpendicular
stem cases, the inward vertical crossbar at a single concave corner
already intersects the original tile because `1+r<=a+1<b`. No pair of
concave corners is needed in this regime. The final actual unanchored
no-plane theorem reports only the three standard axioms.

`lean/PlaneObstructions.lean` now also supplies the compiled unanchored
wrapper `short_stem_two_arm_no_plane` for the earlier c=2 short symbolic
certificate. Thus the earlier note's English-only global normalization
boundary has been superseded for that certificate.


The final c=2 long proof is now also compiled by the source/construction
agent in `TPlaneTwoLong.lean`, using our independently implemented
`TPlaneTwoLongBridge.finite_bridge_impossible`. The bridge's inputs are
exactly the four normalized U/W/R/Z whole tiles. It excludes finite-boundary
V tiles with the existing long-neighbor arithmetic theorem; after forcing
a horizontal neighbor, each S creates a short gap between two tall stems,
so `blocked_deep_run` replaces the longer enclosed-rectangle argument.
All boundary cells are therefore H bars, and their first consecutive pair
contradicts the arbitrary-width deep-wall theorem. Both actual-world
statements compile with only standard axioms. No T-plane negative domain
remains outside Lean.


## 7. Cross obstructions and construction


### Crosses cannot touch a straight infinite boundary

**Theorem.** No collection of crosses whose four arms are positive can tile a half-plane. The crosses need not even have the same arm lengths.

Suppose such a tiling covers $y\ge0$. A tile meeting the boundary must do so at the tip of its downward arm. If its horizontal bar met the boundary, its downward arm would leave the region.

The tiles covering $(0,0)$ and $(1,0)$ therefore have junctions $(0,r)$ and $(1,s)$, with $r,s\ge1$. If $r\le s$, the first tile's right arm contains $(1,r)$, which is already on the second tile's vertical arm. If $s\le r$, the second tile's left arm intersects the first. Both alternatives are impossible.

This entire statement, with arbitrary infinite indexed families, is checked in Lean. It immediately excludes every region above HP in the hierarchy for a genuine four-arm cross.

### Opposite unit arms tile the plane

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

### Four long arms cannot tile the plane

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

### Completing the cross classification

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

## Symbolic case tables for the cross obstruction

Every listed state assumes pairwise disjointness of its crosses. The arm parameters have no upper bound. Each selected cell must be covered; its next-tile alternatives are exhaustive. Each final row has no possible covering cross. Exact inequalities and kernel-checked arithmetic proofs are retained beside these tables.

A placement is written `(x,y; E,N,W,S)`. A selected cell is written `(x,y)`.

### Adjacent units

Domain: `a=b=1, 2≤c≤d`.

Start with the prototile at `(0,0)` and cover `(-1,-1)`.

| State | First added cross | Next required cell | Alternatives |
|---|---|---|---|
| 1 | `(-1, -1 - c; 1, c, d, 1)` | `(-2, -c)` | 4 |
| 6 | `(-1 - c, -1; c, d, 1, 1)` | `(-c, -2)` | 8 |
| 15 | `(-1, -1 - d; c, d, 1, 1)` | `(-2, -d)` | 8 |
| 24 | `(-1 - d, -1; d, 1, 1, c)` | `(-d, -2)` | 4 |
| 29 | `(-1 - d, -1; d, c, 1, 1)` | `(-d, -2)` | 8 |
| 38 | `(-1, -1 - c; d, c, 1, 1)` | `(-2, -c)` | 8 |
| 47 | `(-1 - c, -1; c, 1, 1, d)` | `(-c, -2)` | 4 |
| 52 | `(-1, -1 - d; 1, d, c, 1)` | `(-2, -d)` | 4 |

The second added cross leads immediately to the uncovered cell listed below. A copy in any orientation covering that cell would overlap one of the three placed crosses.

| First state | Second cross | Uncoverable cell |
|---|---|---|
| 1 | `(-2 - c, -c; c, d, 1, 1)` | `(-c, 1 - c)` |
| 1 | `(-2 - d, -c; d, 1, 1, c)` | `(-d, 1 - c)` |
| 1 | `(-2 - d, -c; d, c, 1, 1)` | `(-d, 1 - c)` |
| 1 | `(-2 - c, -c; c, 1, 1, d)` | `(-c, 1 - c)` |
| 6 | `(-c, -3; 1, 1, c, d)` | `(1 - c, -2)` |
| 6 | `(-c, -2 - c; 1, c, d, 1)` | `(1 - c, -c)` |
| 6 | `(-c, -2 - d; c, d, 1, 1)` | `(1 - c, -d)` |
| 6 | `(-c, -3; d, 1, 1, c)` | `(1 - c, -2)` |
| 6 | `(-c, -2 - c; d, c, 1, 1)` | `(1 - c, -c)` |
| 6 | `(-c, -3; c, 1, 1, d)` | `(1 - c, -2)` |
| 6 | `(-c, -3; 1, 1, d, c)` | `(1 - c, -2)` |
| 6 | `(-c, -2 - d; 1, d, c, 1)` | `(1 - c, -d)` |
| 15 | `(-3, -d; 1, 1, c, d)` | `(-2, 1 - d)` |
| 15 | `(-3, -d; 1, c, d, 1)` | `(-2, 1 - d)` |
| 15 | `(-2 - c, -d; c, d, 1, 1)` | `(-c, 1 - d)` |
| 15 | `(-2 - d, -d; d, 1, 1, c)` | `(-2, 1 - d)` |
| 15 | `(-2 - d, -d; d, c, 1, 1)` | `(-2, 1 - d)` |
| 15 | `(-2 - c, -d; c, 1, 1, d)` | `(-2, 1 - d)` |
| 15 | `(-3, -d; 1, 1, d, c)` | `(-2, 1 - d)` |
| 15 | `(-3, -d; 1, d, c, 1)` | `(-2, 1 - d)` |
| 24 | `(-d, -2 - c; 1, c, d, 1)` | `(1 - d, -2)` |
| 24 | `(-d, -2 - d; c, d, 1, 1)` | `(1 - d, -2)` |
| 24 | `(-d, -2 - c; d, c, 1, 1)` | `(1 - d, -c)` |
| 24 | `(-d, -2 - d; 1, d, c, 1)` | `(1 - d, -2)` |
| 29 | `(-d, -3; 1, 1, c, d)` | `(1 - d, -2)` |
| 29 | `(-d, -2 - c; 1, c, d, 1)` | `(1 - d, -2)` |
| 29 | `(-d, -2 - d; c, d, 1, 1)` | `(1 - d, -2)` |
| 29 | `(-d, -3; d, 1, 1, c)` | `(1 - d, -2)` |
| 29 | `(-d, -2 - c; d, c, 1, 1)` | `(1 - d, -c)` |
| 29 | `(-d, -3; c, 1, 1, d)` | `(1 - d, -2)` |
| 29 | `(-d, -3; 1, 1, d, c)` | `(1 - d, -2)` |
| 29 | `(-d, -2 - d; 1, d, c, 1)` | `(1 - d, -2)` |
| 38 | `(-3, -c; 1, 1, c, d)` | `(-2, 1 - c)` |
| 38 | `(-3, -c; 1, c, d, 1)` | `(-2, 1 - c)` |
| 38 | `(-2 - c, -c; c, d, 1, 1)` | `(-c, 1 - c)` |
| 38 | `(-2 - d, -c; d, 1, 1, c)` | `(-d, 1 - c)` |
| 38 | `(-2 - d, -c; d, c, 1, 1)` | `(-d, 1 - c)` |
| 38 | `(-2 - c, -c; c, 1, 1, d)` | `(-c, 1 - c)` |
| 38 | `(-3, -c; 1, 1, d, c)` | `(-2, 1 - c)` |
| 38 | `(-3, -c; 1, d, c, 1)` | `(-2, 1 - c)` |
| 47 | `(-c, -2 - c; 1, c, d, 1)` | `(1 - c, -c)` |
| 47 | `(-c, -2 - d; c, d, 1, 1)` | `(1 - c, -d)` |
| 47 | `(-c, -2 - c; d, c, 1, 1)` | `(1 - c, -c)` |
| 47 | `(-c, -2 - d; 1, d, c, 1)` | `(1 - c, -d)` |
| 52 | `(-2 - c, -d; c, d, 1, 1)` | `(-c, 1 - d)` |
| 52 | `(-2 - d, -d; d, 1, 1, c)` | `(-2, 1 - d)` |
| 52 | `(-2 - d, -d; d, c, 1, 1)` | `(-2, 1 - d)` |
| 52 | `(-2 - c, -d; c, 1, 1, d)` | `(-2, 1 - d)` |

### One units

Domain: `b=1, 2≤a≤c, d≥2`.

Start with the prototile at `(0,0)` and cover `(-1,-1)`.

| State | First added cross | Next required cell | Alternatives |
|---|---|---|---|
| 1 | `(-1 - a, -1; a, 1, c, d)` | `(-a, -2)` | 6 |
| 8 | `(-1, -1 - c; 1, c, d, a)` | `(-2, -c)` | 6 |
| 15 | `(-1 - c, -1; c, d, a, 1)` | `(-c, -2)` | 8 |
| 24 | `(-1, -1 - d; c, d, a, 1)` | `(-2, -d)` | 6 |
| 31 | `(-1 - d, -1; d, a, 1, c)` | `(-d, -2)` | 6 |
| 38 | `(-1, -1 - a; d, a, 1, c)` | `(1, -2)` | 6 |
| 45 | `(-1 - d, -1; d, c, 1, a)` | `(-d, -2)` | 6 |
| 52 | `(-1, -1 - c; d, c, 1, a)` | `(1, -2)` | 6 |
| 59 | `(-1 - c, -1; c, 1, a, d)` | `(-c, -2)` | 6 |
| 66 | `(-1, -1 - a; 1, a, d, c)` | `(-2, -a)` | 6 |
| 73 | `(-1 - a, -1; a, d, c, 1)` | `(-a, -2)` | 8 |
| 82 | `(-1, -1 - d; a, d, c, 1)` | `(-2, -d)` | 6 |

The second added cross leads immediately to the uncovered cell listed below. A copy in any orientation covering that cell would overlap one of the three placed crosses.

| First state | Second cross | Uncoverable cell |
|---|---|---|
| 1 | `(-a, -2 - c; 1, c, d, a)` | `(1 - a, -2)` |
| 1 | `(-a, -2 - d; c, d, a, 1)` | `(1 - a, -d)` |
| 1 | `(-a, -2 - a; d, a, 1, c)` | `(1 - a, -2)` |
| 1 | `(-a, -2 - c; d, c, 1, a)` | `(1 - a, -2)` |
| 1 | `(-a, -2 - a; 1, a, d, c)` | `(1 - a, -2)` |
| 1 | `(-a, -2 - d; a, d, c, 1)` | `(1 - a, -d)` |
| 8 | `(-2 - a, -c; a, 1, c, d)` | `(-a, 1 - c)` |
| 8 | `(-2 - c, -c; c, d, a, 1)` | `(-2, 1 - c)` |
| 8 | `(-2 - d, -c; d, a, 1, c)` | `(-2, 1 - c)` |
| 8 | `(-2 - d, -c; d, c, 1, a)` | `(-d, 1 - c)` |
| 8 | `(-2 - c, -c; c, 1, a, d)` | `(-2, 1 - c)` |
| 8 | `(-2 - a, -c; a, d, c, 1)` | `(-a, 1 - c)` |
| 15 | `(-c, -3; a, 1, c, d)` | `(1 - c, -2)` |
| 15 | `(-c, -2 - c; 1, c, d, a)` | `(1 - c, -2)` |
| 15 | `(-c, -2 - d; c, d, a, 1)` | `(1 - c, -d)` |
| 15 | `(-c, -2 - a; d, a, 1, c)` | `(1 - c, -2)` |
| 15 | `(-c, -2 - c; d, c, 1, a)` | `(1 - c, -2)` |
| 15 | `(-c, -3; c, 1, a, d)` | `(1 - c, -2)` |
| 15 | `(-c, -2 - a; 1, a, d, c)` | `(1 - c, -2)` |
| 15 | `(-c, -2 - d; a, d, c, 1)` | `(1 - c, -2)` |
| 24 | `(-2 - a, -d; a, 1, c, d)` | `(-2, 1 - d)` |
| 24 | `(-2 - c, -d; c, d, a, 1)` | `(-c, 1 - d)` |
| 24 | `(-2 - d, -d; d, a, 1, c)` | `(-2, 1 - d)` |
| 24 | `(-2 - d, -d; d, c, 1, a)` | `(-2, 1 - d)` |
| 24 | `(-2 - c, -d; c, 1, a, d)` | `(-2, 1 - d)` |
| 24 | `(-2 - a, -d; a, d, c, 1)` | `(-a, 1 - d)` |
| 31 | `(-d, -2 - c; 1, c, d, a)` | `(1 - d, -2)` |
| 31 | `(-d, -2 - d; c, d, a, 1)` | `(1 - d, -2)` |
| 31 | `(-d, -2 - a; d, a, 1, c)` | `(1 - d, -a)` |
| 31 | `(-d, -2 - c; d, c, 1, a)` | `(1 - d, -c)` |
| 31 | `(-d, -2 - a; 1, a, d, c)` | `(1 - d, -2)` |
| 31 | `(-d, -2 - d; a, d, c, 1)` | `(1 - d, -2)` |
| 38 | `(1 + c, -2; a, 1, c, d)` | `(2, -1)` |
| 38 | `(1 + d, -2; 1, c, d, a)` | `(d, -1)` |
| 38 | `(1 + a, -2; c, d, a, 1)` | `(a, -1)` |
| 38 | `(1 + a, -2; c, 1, a, d)` | `(a, -1)` |
| 38 | `(1 + d, -2; 1, a, d, c)` | `(d, -1)` |
| 38 | `(1 + c, -2; a, d, c, 1)` | `(2, -1)` |
| 45 | `(-d, -2 - c; 1, c, d, a)` | `(1 - d, -2)` |
| 45 | `(-d, -2 - d; c, d, a, 1)` | `(1 - d, -2)` |
| 45 | `(-d, -2 - a; d, a, 1, c)` | `(1 - d, -a)` |
| 45 | `(-d, -2 - c; d, c, 1, a)` | `(1 - d, -c)` |
| 45 | `(-d, -2 - a; 1, a, d, c)` | `(1 - d, -2)` |
| 45 | `(-d, -2 - d; a, d, c, 1)` | `(1 - d, -2)` |
| 52 | `(1 + c, -2; a, 1, c, d)` | `(2, -1)` |
| 52 | `(1 + d, -2; 1, c, d, a)` | `(2, -1)` |
| 52 | `(1 + a, -2; c, d, a, 1)` | `(a, -1)` |
| 52 | `(1 + a, -2; c, 1, a, d)` | `(a, -1)` |
| 52 | `(1 + d, -2; 1, a, d, c)` | `(2, -1)` |
| 52 | `(1 + c, -2; a, d, c, 1)` | `(2, -1)` |
| 59 | `(-c, -2 - c; 1, c, d, a)` | `(1 - c, -2)` |
| 59 | `(-c, -2 - d; c, d, a, 1)` | `(1 - c, -d)` |
| 59 | `(-c, -2 - a; d, a, 1, c)` | `(1 - c, -2)` |
| 59 | `(-c, -2 - c; d, c, 1, a)` | `(1 - c, -2)` |
| 59 | `(-c, -2 - a; 1, a, d, c)` | `(1 - c, -2)` |
| 59 | `(-c, -2 - d; a, d, c, 1)` | `(1 - c, -2)` |
| 66 | `(-2 - a, -a; a, 1, c, d)` | `(-a, 1 - a)` |
| 66 | `(-2 - c, -a; c, d, a, 1)` | `(-2, 1 - a)` |
| 66 | `(-2 - d, -a; d, a, 1, c)` | `(-d, 1 - a)` |
| 66 | `(-2 - d, -a; d, c, 1, a)` | `(-d, 1 - a)` |
| 66 | `(-2 - c, -a; c, 1, a, d)` | `(-2, 1 - a)` |
| 66 | `(-2 - a, -a; a, d, c, 1)` | `(-a, 1 - a)` |
| 73 | `(-a, -3; a, 1, c, d)` | `(1 - a, -2)` |
| 73 | `(-a, -2 - c; 1, c, d, a)` | `(1 - a, -2)` |
| 73 | `(-a, -2 - d; c, d, a, 1)` | `(1 - a, -d)` |
| 73 | `(-a, -2 - a; d, a, 1, c)` | `(1 - a, -2)` |
| 73 | `(-a, -2 - c; d, c, 1, a)` | `(1 - a, -2)` |
| 73 | `(-a, -3; c, 1, a, d)` | `(1 - a, -2)` |
| 73 | `(-a, -2 - a; 1, a, d, c)` | `(1 - a, -2)` |
| 73 | `(-a, -2 - d; a, d, c, 1)` | `(1 - a, -d)` |
| 82 | `(-2 - a, -d; a, 1, c, d)` | `(-2, 1 - d)` |
| 82 | `(-2 - c, -d; c, d, a, 1)` | `(-c, 1 - d)` |
| 82 | `(-2 - d, -d; d, a, 1, c)` | `(-2, 1 - d)` |
| 82 | `(-2 - d, -d; d, c, 1, a)` | `(-2, 1 - d)` |
| 82 | `(-2 - c, -d; c, 1, a, d)` | `(-2, 1 - d)` |
| 82 | `(-2 - a, -d; a, d, c, 1)` | `(-a, 1 - d)` |


## 8. The L classification and its prior proofs


## L shapes: translation of the prior classification and explicit constructions

Let L=P(a,b,0,0), a>=b>=1. Its bounding dimensions are (a+1) by (b+1); its area is a+b+1. All rotations and reflections are permitted.

### Classification inherited from Raychev's 2021 papers

The two supplied papers establish the following classification:

| Arm lengths | Strongest region capabilities |
|---|---|
| b=1 | Rectangle |
| b=2 | Strip, but no quadrant |
| (a,b)=(4,3) | Strip, but no quadrant |
| b>=3, (a,b)!=(4,3) | Plane, but no half-plane |

All long L shapes (a,b>=2) fail to tile a quadrant. Consequently they also fail rectangle, half-strip, bent-strip, and rep-tile conditions. The half-plane paper states its theorem in bounding dimensions: exactly 2-by-n, 3-by-n, and 4-by-5 tile a half-plane. The constructions for all these families actually give strips or rectangles, so there is no separate half-plane-only L family.

Sources supplied by the author:

1. *L Polyominoes*, Student Conference 2021 ([supplied PDF](/polyominoes/raychev-2021-l-quadrant.pdf)), especially pp. 9–16. The displayed Theorem 9 is phrased as a rectangle obstruction. Its proof is entirely local at one corner and a boundary: the diagrams use no opposite rectangle edge. It therefore also excludes a quadrant. The later paper explicitly states the quadrant result as the preceding work's conclusion.
2. *Tiling the Half-Plane with L Polyominoes*, Spring Conference 2021 ([supplied PDF](/polyominoes/raychev-2021-l-half-plane.pdf)), Theorem 1, pp. 3–13.

The first proof separates equal arms, bounding dimensions 4-by-3 and 5-by-3, the family n-by-3 for n>=6, and n-by-m for n>m>=4. It first excludes endpoint-only boundary contacts. The remaining corner configurations force either an uncovered cell or a closed rectangle shorter than a required arm. In the final n>m>=4 case, the interior boundary run is divided according to whether one long arm occupies n of its cells; the two end counts restrict that case to m=4, and both remaining placements fail. These are the original finite geometric case analyses. The current Lean re-verification scope is stated below.

The second proof excludes boundary-tip contacts and then boundary contacts by the short leg. The remaining long-leg contacts produce impossible neighboring interior runs; the 4-by-6 case is treated separately. No opposite boundary or bounded search width is used.

### Rectangle construction for b=1

Put L=P(a,1,0,0), n=a+2. The copies L and -L+(a+1,1) partition the rectangle {0,...,a+1} by {0,1}: row zero contains the first bar and the second stem tip; row one contains the first stem tip and the second bar.

### Plane construction for every L

Put n=a+b+1. Under the residue map x-y modulo n, L's horizontal arm gives 0,...,a and its positive vertical arm gives -1,...,-b. These are precisely n consecutive residues. Therefore translates by the lattice generated by (n,0) and (1,1) partition the plane exactly.

### Six-copy strip construction for b=2

This formula was reconstructed independently from exact witnesses. It gives a strip of height a+3 and horizontal period six for every a>=2. For each row of the following table, place a tile consisting of the given vertical bar and horizontal foot; then repeat the six tiles by translations (6k,0), k an arbitrary integer. The junction belongs to both listed segments but is a single cell.

| Tile | Vertical bar | Horizontal foot |
|---|---|---|
| A | x=0, 0<=y<=a | y=0, 0<=x<=2 |
| B | x=1, 1<=y<=a+1 | y=a+1, -1<=x<=1 |
| C | x=2, 2<=y<=a+2 | y=a+2, 0<=x<=2 |
| D | x=3, 2<=y<=a+2 | y=a+2, 3<=x<=5 |
| E | x=4, 1<=y<=a+1 | y=1, 2<=x<=4 |
| F | x=5, 0<=y<=a | y=0, 3<=x<=5 |

Each tile has one leg of length a+1 and one of length three, meeting at an endpoint, hence is a D4 copy of L. On every row 2 through a the six vertical bars provide columns 0 through 5. On row zero, A and F give the two three-cell feet. Row one has A at column zero, B at column one, E at columns two through four, and F at column five. Row a+1 has B's foot at residues 5,0,1 together with C,D,E at 2,3,4. Row a+2 has C and D's three-cell feet. These disjoint lists cover each row residue exactly once, and no tile leaves the strip.

The remaining positive L case, bounding dimensions 4-by-5, has an explicit width-eight, period-eight strip witness in `results/l_4x5_strip.json`; exact cell checking is independent of the search that found it. The original negative results are credited to the author's supplied papers. Their current Lean scope is stated below.

### Dimensional correction to the supplied half-plane paper

The width-six statement on page 4 does not match its page 3 drawing. Reconstructing the drawing gives eight columns, vertical period eight, and eight 8-cell L tiles per period. The 64-cell residue cover is recorded and independently verified in `results/l_4x5_strip.json`. The classification theorem is unaffected: a finite-width strip exists. This correction does not assert that every other width-six construction is impossible.

### Current Lean verification scope

The positive constructions compile in `PositiveLPlane`, `PositiveLStrip`, `PositiveLSpecial`, and the rectangle modules. `LQuadrantSmall` and `LQuadrantShortLong` supply all b=2 corner obstructions and the (4,3) corner obstruction. `LHalfPlaneEqual` excludes half-plane tilings for equal arms at least three. `LHalfPlaneFiveThree.no_halfplane` supplies the complete exceptional (5,3) half-plane obstruction, with 421 short-bar and 539 alternating-eight-bar states independently checked and replayed in Lean.

The universal unequal half-plane obstruction a>b>=3,a>=5 now compiles as `PolyominoFormal.LHalfPlaneUnequal.no_halfplane`. Its proof combines the boundary-tip and short-leg exclusions, extraction of alternating long bars, the count forcing a=b+2, and the final mixed-motif obstruction. `sorted_L_classified` in `MainClassification.lean` supplies the unconditional all-L theorem; `all_tuples_classified` includes these profiles in the complete eight-capability classification for all natural four-tuples. The earlier conditional helper `sorted_L_classified_of_unequal` is an internal assembly lemma, with its premise discharged by the final theorem. This Lean reconstruction retains the supplied 2021 papers' prior credit. The detailed argument is in `research/l_unequal_halfplane_proof.md`.

## Unequal long L shapes: proof map

The statement is that P(a,b,0,0) does not tile the half-plane when
a>b>=3 and a>=5. Arms count added cells, so the bounding box is
(a+1)-by-(b+1). This is a formal reconstruction of the negative L result
in Angel Raychev's supplied 2021 half-plane paper, not a novelty claim.

The complete arithmetic and geometric replay is checked in Lean 4.33.1.
`PolyominoFormal.LHalfPlaneUnequal.no_halfplane` proves the universal
statement for ordinary exact half-plane tilings.
[MainClassification.lean](/polyominoes/lean/MainClassification.lean) uses it
in the unconditional eight-capability theorem for all natural four-tuples;
the [proof package](/polyominoes/lean-proofs.zip) and
[rebuild guide](/polyominoes/lean-guide.md) provide the complete sources.

### From an infinite tiling to the finite configuration

Assume an exact half-plane tiling by whole congruent L shapes. First rule
out a tile touching the boundary only at its vertical tip. This is done
for both possible vertical arm lengths. Thus every boundary cell belongs
to a horizontal leg.

Next exclude a short horizontal boundary leg. Translate and, if necessary,
reflect its tile to O=(0,0;b,a,0,0), where a placement is written
(junction x, junction y; east, north, west, south). The cell (1,1) must
be covered. Disjointness and the eight orientations give exactly these
seven candidates:

| Junction | Arms (E,N,W,S) |
|---|---|
| (1,1) | (a,b,0,0) |
| (1,a+1) | (b,0,0,a) |
| (b+1,1) | (0,a,b,0) |
| (1,a+1) | (0,0,b,a) |
| (a+1,1) | (0,b,a,0) |
| (1,1) | (b,a,0,0) |
| (1,b+1) | (a,0,0,b) |

Six alternatives have separate finite obstructions. The fourth can be
excluded more economically after those six: the tile covering the cell
just left of O has four possible boundary forms. The two short forms
contradict the already established short-bar consequences; the two long
forms give independently checked three-tile obstructions. This order
avoids assuming the short-bar theorem in its own proof.

Now every boundary contact is a long leg. Two consecutive long legs with
stems on the same side have a finite obstruction. Consequently their
orientations alternate. Repeatedly cover the immediately adjacent boundary
cell to obtain eight consecutive alternating long legs. This is a local
consequence of coverage and exclusion; no periodicity assumption is made.

### Counting the next row

Four central legs have junctions -1, 0, 2a+1, 2a+2 at height zero. Their
stems bound the first-row interval 1 through 2a. Boundary and corner
obstructions exclude vertical-tip coverage in that interval, so it must
be covered by horizontal legs. Successor and endpoint arguments count
those legs. Away from a=b+2, the remaining pair of outward-stem short
legs has a finite obstruction, separately proved for a=b+1 and a>=b+3.
Therefore the assumed tiling forces a=b+2.

At arm difference two, the same endpoint argument forces one of two
reflected mixed patterns. In the first, the row contains
U=(1,1;a,b,0,0) and S=(2a,1;0,a,b,0). The other is its reflection in
x=(2a+1)/2. The final finite obstruction uses these two tiles and the
four central boundary tiles. It starts at cell (2,2) and checks every
covering placement. The original (5,3) case has a separate complete
eight-boundary-bar obstruction. Reflection of the actual tiling reduces
the second pattern to the first.

![The mixed first-row L configuration above four alternating boundary bars.](/polyominoes/l-mixed-motif.svg)

The drawing displays the mixed configuration used by the final obstruction;
the proof quantifies over the entire unbounded parameter domain.

### What closes a certificate branch

Some leaves have no legal tile through their queried cell. Others use a
short empty run with a completely occupied floor and both endpoints
occupied by already selected whole tiles. If the run has g cells with
1<=g<=b, a horizontal leg cannot fit. The following sufficient conditions
exclude the remaining vertical starters:

| Run length | Extra occupied cap cells above the endpoints |
|---|---|
| g>=5 | None |
| g>=4 | At least one endpoint at height b above the run |
| g>=3 | Both endpoints at height b |
| g=2 | Both at height b, and at least one at height a |
| g>=1 | Both at height b and both at height a |

These are proved as lemmas about a tiling and a union of whole selected
tiles. They do not assume an arbitrary painted obstacle is a legal tile.
Upward, downward, and both lateral versions explicitly check that the
queried run lies in the original half-plane.

For each non-leaf node the independent checker tests all eight
orientations with an arbitrary integer junction, under the exact unbounded
parameter domain. Lean then proves the emitted arithmetic implications
and replays the tree using an actual tiling's cover and disjointness
axioms. Solver success is not an axiom in the final theorem.

### Formal entry points

- `LHalfPlaneShortbarAssembly.inner_forms`: exhaustive seven-way corner list.
- `LHalfPlaneShortbarAssembly.no_shortbars`: complete boundary exclusion.
- `LHalfPlaneAssembly`: extraction of eight alternating boundary legs.
- `LHalfPlaneAlternating.delta_two`: counting forces a=b+2.
- `LHalfPlaneMixedMotif.mixed_impossible`: the final mixed configuration.
- `LHalfPlaneUnequal.no_halfplane`: the assembled universal statement.
- `PolyominoFormal.all_tuples_classified` in `MainClassification.lean`: normalization and complete
  eight-capability classification, including degenerate tuples.


## 9. Exact rectangle witnesses


### Rectangle for P(1,1,1,0)

Each letter is one tile. This 4-by-4 cell partition can be checked directly:

```text
BCCC
BBCD
BADD
AAAD
```

### Rectangle for P(2,1,1,0)

Each letter is one tile. This 10-by-5 cell partition can be checked directly:

```text
BBBBEHHHHJ
ABEEEEHGJJ
ADDDDGGGGJ
AACDFFFFIJ
ACCCCFIIII
```

### 4a. Exact historical rectangle certificate for P(3,1,1,0)

The Y hexomino P(3,1,1,0) has a 24-by-23 rectangle tiling by 92 copies. Source: [Michael Reid's Y-hexomino page](https://sicherman.net/mikereid/y6_rect.html), attributing its independent discovery to Karl A. Dahlke and T. W. Marlow. Original image: https://sicherman.net/mikereid/Images/y6_23x24.gif . These sources establish provenance; this run independently verified the geometry.

`research/t_construct_extract_y6.py` extracts the connected white interiors of the source raster, samples its 24-by-23 cells, and verifies that the 92 resulting six-cell sets are all exact D4 copies of P(3,1,1,0). It verifies coverage of all 552 cells exactly once. The standalone output `research/t_construct_y6_23x24_certificate.json` contains explicit lattice cells, transformations, translations, and provenance. Optional raster reconstruction requires downloading the linked source image as `research/t_construct_y6_23x24_source.gif`; the image is not distributed in the research archive. The explicit coordinate certificate needs no raster image.

The finite certificate proves rectangle tileability. It does NOT independently establish that 92 is the minimum possible number of tiles; that stronger historical result requires Dahlke's minimality proof.

After downloading that image and installing Pillow, optional raster reconstruction uses:

    python3 research/t_construct_extract_y6.py


## 10. Formal verification scope


## Lean proofs

Lean 4.33.1 checks the statements below for ordinary integer-cell tilings:
all eight rotations/reflections, arbitrary integer translations, whole-tile
containment, exact coverage, and ordinary pairwise disjointness. Infinite
worlds are allowed. No periodicity or tile-count bound is assumed.

### The two disputed cases

`InitialTwoClassification.lean` proves:

```lean
PolyominoFormal.p4_exact_bs : ExactBS 4
PolyominoFormal.p5_exact_bs : ExactBS 5
```

| Capability | P(4,1,1,0) | P(5,1,1,0) |
|---|---|---|
| Rectangle | impossible | impossible |
| Half-strip of any positive integer width | impossible | impossible |
| Bent strip | possible | possible |
| Quadrant | possible | possible |
| Strip | possible | possible |
| Half-plane | possible | possible |
| Plane | possible | possible |
| Integer-scale rep-tiling | impossible | impossible |

The finite corner data have 1,750 nodes for parameter four and 872 nodes
for parameter five. Lean checks every whole-tile alternative, the exact
successor corner, and the well-founded height/state argument. The formal
rep obstruction also covers the small scales two and three.

`GunFamilyClassification.lean` completes the entire family: every natural
n<=3 has the rectangle profile, and every n>=4 has the BS profile above.
The universal n>=6 replay contains 8,309 arithmetic lemmas and five full
geometric transition proofs. There is no upper bound on n.

### Complete classification

The unconditional entry point is `PolyominoFormal.all_tuples_classified`
in [MainClassification.lean](/polyominoes/lean/MainClassification.lean):

```lean
theorem all_tuples_classified (a b c d : Nat) :
    Classified a b c d (classifyTuple a b c d)
```

It proves all eight capabilities: rectangle, half-strip, bent strip,
quadrant, strip, half-plane, plane, and integer-scale rep-tiling. Natural
arms include zero, so bars and degenerate tuples are covered. The theorem
has no remaining geometric or obstruction premise. `TupleNormalization`
proves the exhaustive reduction and the required D4 equivalences.

| Formal result | Scope |
|---|---|
| `MainClassification`: `all_tuples_classified` | All four-tuples and all eight capabilities |
| `MainClassification`: `sorted_L_classified` | Every sorted L shape and its degenerate bars |
| `TClassification`: `normalized_T_classified` | Every genuine T |
| `PositiveCrossClassification`: `classify_positive_cross` | Every four-positive-arm cross |
| `GunFamilyClassification`: `classify_gun` | The full unbounded gun family, including parameters four and five |
| `LHalfPlaneUnequal`: `no_halfplane` | The unequal L obstruction for a>b>=3 and a>=5 |

The L construction and obstruction modules provide a formal reconstruction
of Angel Raychev's supplied 2021 papers, not a claim of a new L classification.
The last unequal-L argument combines boundary exclusions, the proved
alternating-row count, and the mixed-motif obstruction. The public
[source package](/polyominoes/lean-proofs.zip) and
[rebuild guide](/polyominoes/lean-guide.md) include the exact dependencies.

### Definitions and proof map

- `TilingCore.lean`: `Tiling`, `Tiles`, and the seven region definitions.
- `RectangleRep.lean`: the shared `RepTileable` definition. It means a
  dissection into congruent unit-cell copies at a natural enlargement
  factor at least two; it does not mean an unequal-scale dissection.
- `HierarchyProfiles.lean`: all eight capabilities and the executable
  classification `classifyTuple`, proved correct by `all_tuples_classified`.
- `TilingSymmetry.lean`, `HierarchyProfiles.lean`, `TupleNormalization.lean`:
  checked translations, D4 symmetry, and exhaustive tuple reduction.
- `CornerCertificateCore.lean`, `CornerCertificateReplay.lean`, and
  `CornerCertificateFour/Five/Large*.lean`: the gun corner certificates.
- `HalfStripObstruction.lean`, `RepObstruction.lean`, `RepConvention.lean`:
  arbitrary-width and all-scale consequences of the corner theorem.
- `FiniteRectangle.lean`, `SmallTRectangleOne/Two/Three.lean`: exact finite
  rectangle checks, including the 92-piece rectangle for n=3.
- `THalfPlane*.lean`, `HPFinite*.lean`, `TPlane*.lean`: the complete T
  boundary and plane obstructions, including arbitrary-world normalization.
- `LongCrossObstruction.lean`, `CrossClassification.lean`,
  `CoreBoundaryObstructions.lean`: the positive-arm cross obstructions.
- `RepComposition.lean`, `TilingCompactness.lean`, `FiniteCandidates.lean`,
  `RepHierarchy.lean`: actual rep-dissection iteration and a proved
  countable compactness construction yielding quadrant tilings.

The compactness argument stabilizes whole-tile membership along nested
unbounded sets of indices. Coverage follows from an explicit finite list
of every possible tile through a cell; disjointness follows by putting two
eventual tiles in one common sample. These steps are themselves Lean
proofs, not an assumed compactness axiom.

### Trust and reproduction

The final compiled theorem reports contain only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. There are no admitted
proofs, extra axioms, or `native_decide` calls. External search and SMT
solvers propose cases and useful inequalities; Lean's kernel checks the
finite data and the resulting arithmetic and geometric proofs.

From the project root, with Lean 4.33.1 installed:

```sh
python3 src/check_lean.py InitialTwoClassification --jobs 1
python3 src/check_lean.py MainClassification GunFamilyClassification --jobs 1
```

Pass `--lean /absolute/path/to/lean` if it is not on PATH. The build driver
compiles local dependencies in order into an isolated `.build/lean`
directory. It uses no pre-existing research `.olean` files and needs no
SMT solver. Subsequent builds reuse only artifacts whose source, imports,
compiler version, and artifact hashes match recorded receipts. Use a new
`--output` directory for a fresh rebuild. The generated finite cases can
take substantially longer to compile than the short final statements.

The research archive includes all Lean sources and generation/checking
scripts, but excludes the Lean runtime and compiled objects. Compiler
logs, transitive hashes, failed approaches, and independent semantic
audits are retained under `research/`; `RESEARCH_LOG.md` records the proof
boundaries and progress.
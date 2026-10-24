# Lean verification: guaranteed indirect delivery

Pinned toolchain: **Lean 4.33.1**, with **Std only**. The exact replayed source
snapshot is identified by `verification.json`. The full extremal classification
is **not yet a Lean theorem**. The results below are unconditional Lean theorems
unless a supplied hypothesis is explicitly stated. Module counts are not a
measure of how much of the classification has been proved.


## Exact maxima with explicit attaining constructions

- **Complete dense region, every order n≥11.**
  `DenseSharpClassification.maximum` proves the exact maximum for every
  `n(n−3)≤m≤n(n−1)`. At `m=n(n−3)` it is `2n`; writing
  `r=m−n(n−3)`, it is `2n−r−ceil(r/2)−1` for `1≤r≤n`; beyond
  `n(n−2)` it is zero. `DenseSharpClassification.attainer` gives a concrete
  adjacency recipe and proves looplessness, the exact arrow budget and score.
  The first staircase step, modular even and odd cores, functional root
  attachments, and complementary-block counts are all instantiated.
- **Adjacent main-interval band, every order n≥16.**
  `DenseEnvelopeClassification.maximum` proves
  `M(n,m)=n(n−1)−m` for `n(n−1)−3n≤m≤n(n−1)−2n`.
  Explicit even and odd formulas, six finite envelopes at 16..21 and four
  odd repairs at 23, 25, 27, 31 supply the whole domain. Every optional subset
  works and delivers within two moves. `PrefixEnvelope` proves that taking
  the first required optional ordered pairs has exactly the requested budget.
  Together these two results classify every budget `m≥n(n−4)` when `n≥16`.
- **Functional endpoint at every order n≥2.**
  `FunctionalEndpoint.maximum_endpoint` proves
  `M(n,n(n−2))=floor((n−2)/2)` with a literal paired-root construction.
  Its proof characterizes exactly which missing pairs succeed in the
  complement of a fixed-point-free function.
- **Zero band at all orders.** `DenseZero.maximum_zero` proves
  `M(n,m)=0` whenever `n(n−2)<m≤n(n−1)`. The attainer is the first `m`
  nonloop ordered pairs in lexicographic order, with its cardinality proved.
- **Twenty-four-arrow maximum at every host order n≥12.**
  `SparseAttainment.maximum_twentyfour` proves `M(n,24)=108`, combining
  the checked twelve-vertex witness, the unrestricted sparse upper bound
  and explicit isolate padding. The original `IsMaximum 12 24 108`
  theorem is retained.
- **Uniform sparse even maxima from support order 85.**
  `SixTypeConstruction.maximum_even` proves
  `M(n,2s)=s(s−3)` for every support order `s≥85` and host order `n≥s`.
  The prescribed six-type cyclic graph has exactly `s` vertices and `2s`
  arrows. All 81 canonical local hole patterns and 552 local rank objectives
  are instantiated, with complete pattern coverage, projection of every
  actual cop reply (including an outside cop), safe transfer, terminal
  delivery, composition and exact counts. Isolate padding gives every larger
  host. `MainSmallSparse.maximum` separately supplies every support12..18
  by reusing main-interval endpoint constructions. The five-type endpoints
  below additionally supply supports 50,55,65,70,75,80. The remaining even
  finite bridge is supports 19..84 excluding those six orders.
- **Complete main interval, every order n≥115.**
  `LowBandConstruction.main_interval` proves `M(n,m)=n(n−1)−m` for
  every `2n≤m≤n(n−3)`. Its lower band supplies all101 local patterns and
  696 strategy objectives, actual cyclic projection of optional cop arrows,
  safe-transfer composition, exact counts and a prescribed optional-edge
  prefix. `attainer_exact` also preserves its stronger envelope endpoint
  `LowBandPrefix.top n`, beyond3n. The upper interval joins at3n.
- **Main interval above three arrows per vertex, every order n≥25.**
  `MainUpperInterval.maximum` proves `M(n,m)=n(n−1)−m` throughout
  `3n≤m≤n(n−3)`, using the counted circle, hub and separated-code
  constructions and their proved overlaps. It also supplies the smaller
  intervals95..304 at order19,100..340 at20,126..378 at21,110..418 at22,
  115..460 at23, and120..504 at24. Every recipe has an exact optional-prefix
  budget; no graph search is used to choose an attaining graph.
- **Complete main intervals at every order12..18.**
  `MainTwelve.maximum` and `MainSmallClassification.maximum` prove the
  missing-pair maximum throughout `2n≤m≤n(n−3)`. At order12, thirty
  asymmetric stages cover24..107 and pair codes supply108. At orders13..18,
  145 literal stages cover the complete intervals. Every optional subset is
  checked against all upper-envelope cop replies, with exact arrow counts.
  These endpoints also prove the sparse even maxima at supports12..18 in
  every larger host, without a second finite catalogue.
- **Uniform odd sparse maxima from support order98.**
  `OddEndpointConstruction.maximum_odd` proves
  `M(n,2s−1)=(s−1)(s−4)+2` for every `n≥s≥98`.
  Its prescribed cyclic adjacency, exact counts, all124 local patterns and
  847 strategy objectives, projection of every cop reply, and global safe
  transfer are instantiated. `OddEndpointFiniteCorollaries` also supplies
  supports88,89,90,94,95,96 using the same catalogue and sharper residue
  thresholds. `SmallOddConstruction.maximum_odd` supplies supports13..18
  using retained signed-rank graphs. All these maxima permit isolate padding.
- **Additional finite five-type main intervals.** The full lower band
  `2n≤m≤3n` is proved at orders65,70,75,80,85,90,95,100,105,110.
  Combined with `MainUpperInterval`, this gives their entire main intervals.
  The short charts also give100..110 at order50 and110..121 at order55.
  `FiveFinite65`, `FiveFinite70`, `FiveFinite75`, `FiveFullRing16`
  through `FiveFullRing22`, `FiveShortRing10` and `FiveShortRing11` specify the graphs and exact optional-prefix budgets.
  Envelope symmetry transports all optional graphs, without assuming that
  an arbitrarily selected optional graph itself has that symmetry.
- **Five-offset circles.** `CircleParameters.maximum` proves
  `M(n,m)=n(n−1)−m` for every `n≥16` divisible by four and every
  `5n≤m≤n(n/2−1)`. Its parameter is prescribed from `n`; modular escape,
  coprime orbit coverage, actual delivery, counts and optional prefixes
  are proved. The guarded construction has a separate exact domain and
  closed arithmetic endpoint in `CircleGuardedConstruction`; its parameter
  conditions remain visible. These results do not establish the entire
  main interval from order twelve.

- **Protected circles at every order n≥25.** `ProtectedParameters.maximum`
  proves the missing-pair maximum for `3n≤m≤n(ceil(n/7)−1)`. An arithmetic
  scan chooses a proved valid parameter; an increasing-residue greedy
  procedure tests six protected differences per existing offset. Lean proves
  the resulting size bound, actual delivery and exact optional-prefix budget.
  This is a specified construction procedure, not a generic graph/game search.

## Sharp small budgets and small host tables

`SmallBudgetsToFive` and `SmallBudgetSix` through `SmallBudgetTen` prove
unrestricted sharp upper bounds at budgets0..10:
0,0,0,0,1,1,2,2,4,5,6. Attainment is proved for0..3 at every admissible
host,4..6 from host4,7..8 from host5, and9..10 from host6. The bounds
include arbitrary sources, sinks and isolates. Actual support reduction,
complete sorted degree-profile coverage and every surviving row choice are
proved, including the fast profile enumeration's completeness theorem.

`TinyOrderClassification`, `FourVertexClassification.maximum` and
`FiveVertexClassification.maximum` supply every admissible budget at every
host order at most5. The four-vertex table is0 at0..3,1 at4..5,2 at6,
1 at7..8 and0 at9..12. The five-vertex table is0 at0..3,1 at4..5,
2 at6..7,4 at8,3 at9..11,2 at12..14,1 at15 and0 at16..20.
Four-vertex adjacency exhaustiveness, actual source/sink deletion and a
complete4818-node five-vertex positive-profile proof establish the upper
bounds; explicit graphs establish all lower bounds.

## Upper bounds and finite certificates

`VertexBound.vertex_upper` proves `I(G)≤n(n−3)` for loopless graphs with
`n≥3`, and zero below three. `DenseStaircase` derives its loss bound from
arbitrary actual graphs: the formerly supplied graph-to-counting premise is
now proved. `DenseCounting` retains the earlier conditional arithmetic lemma.

`SparseParity.even_upper` and `odd_upper` prove, for every loopless finite
graph and every `k≥5`,

- `I(G)≤k(k−3)` when it has `2k` arrows;
- `I(G)≤k(k−3)+2` when it has `2k+1` arrows.

The support counting, source/sink deletion, preservation of retained
strategies, row/column capacities and induction are all proved. Isolated
vertices need no reindexing. The small induction envelope is explicitly an
auxiliary upper bound, not the sharp small-budget table.

`FiniteExclusion.UnrestrictedNine.upper` proves `I(G)≤53` for **every**
loopless nine-vertex graph. Degree rigidity, finite Hall factorization,
canonical permutation cycles, all eight complete branching trees and their
pruning/losing rules are formalized. This strictness result does **not**
by itself prove the sharper two-regular bound30, the separate value
`M_E(18)=33`, or all nine-vertex maxima. Further finite-checker modules prove soundness of
optimistic partial-game pruning, bitset closure and cached loss unions;
those interfaces alone do not establish a concrete exclusion.

`FiniteExclusion.RegularNineSharp.maximum` proves exact maximum30 among
all loopless nine-vertex graphs with in-degree and out-degree two at every
vertex. Hall factorization and normalization cover all eight first-factor
cycle types; the complete sharp exclusion trees and a score30 attainer supply
both directions. The earlier Hamiltonian-factor result is retained as a
subcase. This is a restricted regular family, not the unrestricted value
`M_E(18)=33` or the complete nine-vertex table.

`PositiveFourteen.upper` proves `I(G)≤13` for every loopless graph with
fourteen arrows, at least nine vertices, and positive incoming and outgoing
degree at every vertex. `PositiveFourteenIsolates.upper` permits arbitrary
additional isolates: its actual nonisolated support must have at least nine
vertices and every supported vertex must have positive degree in both
directions. The proof combines complete nine-vertex joint-profile and
row-choice coverage, the ten-vertex profile proof and larger-support counting.
Its nine-vertex benchmark checks160718 DAG nodes across eleven normalized
profiles. It does not establish the unrestricted fourteen-arrow maximum:
smaller supports and sources/sinks still require separate formal exclusions.

`SmallSparseWitnesses.literal` and `padded` verify the exact scores
8,9,11,13,15,19,28,33,40,53,60,79,83 of retained graphs at budgets11..23,
respectively. Each pads to every host at least as large as its stated support;
all supports are at most12. These supply the complete small-budget lower
witness list, not the matching unrestricted upper bounds.

`SignedRankCertificate` and `ExactScoreCertificates` check both winning and
losing pairs. `SparseWitness9`, `SparseWitness10`, and `SparseWitness11`
prove exact graph scores 30, 50, 79 at `(n,m)=(9,18),(10,20),(11,22)`.
These are lower witnesses, not new unrestricted upper bounds. The retained
four-vertex/six-arrow example has exact score two. The eleven-vertex dense
example has 88 arrows and score 22. A separate complete three-vertex pilot
covers all 64 loopless graphs and proves score zero.

## Actual game and construction semantics

Both players may wait. The messenger moves first and receipt precedes
collision. `SemanticCompleteness.guaranteed_iff_actual` proves that finite
winning trees are equivalent, on finite graphs, to one fixed legal messenger
policy that eventually delivers against every permitted initial cop and every
legal history-dependent cop policy. The actual-play definition assumes no
horizon; the proof derives a finite bound. Thus the formal score has the
intended actual-game meaning.

The strategy modules also prove safe branching, camping obstructions,
protected routing, arbitrary-subset envelopes, source and position ranks,
and guide attachment under their displayed premises. `GraphPadding` proves
exact preservation when adding isolates or sinks with at most one predecessor,
including cops starting at or entering a new sink. `ComplementarySum` proves
the displayed two-move block composition and exact missing-pair counts;
it does not claim arbitrary strategy preservation under adding cross arrows.

`LocalArena` treats distinct messenger/cop state spaces and projections of
all actual cop replies. Safe-transfer goals require survival after the cop's
reply; terminal delivery alone waives collision at the recipient. Its local
projection and sequential-composition theorems retain the concrete arena,
projection and certificate premises until those are separately instantiated.
`SixTypeConstruction` now supplies those concrete premises for its entire
uniform even family, rather than only an empty-hole or bounded pilot.

## Remaining classification obligations

The remaining even sparse supports are19..84 excluding50,55,65,70,75,80.
The remaining odd supports are19..97 excluding88,89,90,94,95,96.
Each unclosed support represents all larger hosts through isolate padding.

The exact remaining main-interval domains are:

- order19:38..94; order20:40..99; order21:42..125;
- order22:44..109; order23:46..114; order24:48..119;
- order50:111..149; order55:122..164;
- `2n≤m<3n` at all other orders25..114 except
  65,70,75,80,85,90,95,100,105,110, whose full main intervals are proved.

Unrestricted sharp small-budget upper bounds11..23, the joint tables at
orders6..11, and final quantified formula/constructor assembly remain
unfinished. The complete dense range at every order from11 is covered.
Probabilistic existence, some alternative constructions and stronger
supplementary guarantees retain their ordinary proof boundaries.

No theorem currently states the complete formula for every admissible `(n,m)`.
Checking a graph's ranks does not prove exhaustive coverage of competing graphs.
A checked conditional strategy lemma does not discharge its geometric or
parameter hypotheses. See `research/LEAN_ROADMAP.md` in the research archive
for the dependency-ordered continuation.

## Portable replay and trust boundary

Install the version in `lean-toolchain`, then run from this directory:

```sh
python3 check.py
```

Or use `python3 check.py --lean /path/to/lean`. The checker discovers and
rebuilds **every distributed Lean module** in dependency order, one module at a time,
with two Lean worker threads. It checks reported axioms, rejects proof holes and
native proofs, verifies that sources did not change during the run, and writes
`verification.json` with compiler/source hashes, outputs and elapsed times.
Compiled object files are excluded from the archive and regenerated locally.

The October campaign also uses `src/replay_lean_checkpoint.py` to stage a fresh
bounded parallel replay. It reuses a successful compilation only when the
current campaign's source, transitive dependencies, compiler and object hashes
all match; changed inputs invalidate the affected modules. Its final pass
covers the whole distributed dependency graph. This coordinator does not change
`check.py`'s public sequential default or admit ordinary solver receipts as
kernel evidence.

Finite certificates use ordinary kernel reduction (`decide +kernel`). No
external solver assertion, custom axiom, `sorry`, `admit`, or `native_decide`
is accepted. The reported dependencies are confined to Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. Producers are untrusted and
unnecessary for replay: literal certificate data are already in the sources.
An incorrect move, missing branch, failed rank decrease or invalid losing
region makes the kernel check fail.

## Provenance

The problem and original layered construction come from Alexandra Ignatova's
manuscript, with Angel Raychev as mentor. The approved publication authorship
and contribution statement remain in the paper. The formal development began
in September 2026 and was extended in October 2026 with AI assistance through
Codex. New local proofs become part of a public release only after its
source-pinned replay and artifact checks; the release receipt identifies that
boundary.

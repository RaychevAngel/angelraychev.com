# Lean verification: guaranteed indirect delivery

Pinned toolchain: **Lean 4.33.1**, with **Std only**. The exact replayed source
snapshot is identified by `verification.json`. The full extremal classification
is **not yet a Lean theorem**. The results below are unconditional Lean theorems
unless a supplied hypothesis is explicitly stated. Module counts are not a
measure of how much of the classification has been proved.

## Exact maxima with explicit attaining constructions

- **Complete dense region, every order n≥20.**
  `DenseClassification.maximum` proves the exact maximum for every
  `n(n−3)≤m≤n(n−1)`. At `m=n(n−3)` it is `2n`; writing
  `r=m−n(n−3)`, it is `2n−r−ceil(r/2)−1` for `1≤r≤n`; beyond
  `n(n−2)` it is zero. `DenseClassification.attainer` gives a concrete
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
  Together these two results classify every budget `m≥n(n−4)` when `n≥20`.
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
prove the sharper two-regular bound 30, the separate value `M_E(18)=33`, or
all nine-vertex maxima. Further finite-checker modules prove soundness of
optimistic partial-game pruning, bitset closure and cached loss unions;
those interfaces alone do not establish a concrete exclusion.


`FiniteExclusion.HamiltonianSharp.maximum` proves exact maximum 30 for the
nine-vertex family consisting, up to isomorphism, of a directed Hamiltonian
cycle and a disjoint loopless permutation. All members have eighteen arrows.
The complete normalized upper tree and an explicit isomorphism to the score 30
witness establish both directions. The other seven first-factor cycle types
are not included in this sharper theorem; the full two-regular bound remains
an outstanding finite obligation.

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

## Remaining classification obligations

The sparse infinite attaining families and their full finite bridges, the
remaining main-interval construction chain and its parameter overlap, the
complete staged finite lists, sharp small-order upper exclusions and tables,
and final all-pairs assembly remain unfinished. The sharp dense threshold
from order eleven is not implied by the verified uniform threshold twenty.
Probabilistic existence, some alternative constructions and stronger
supplementary guarantees also retain their ordinary proof boundaries.

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

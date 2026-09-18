# Lean verification: guaranteed indirect delivery

Pinned toolchain: **Lean 4.33.1**. Dependencies: **Std only**, supplied with Lean. No Mathlib, external game library, or assumed graph-game equivalence is required.

## What is proved

| Module | Verified statement |
|---|---|
| `DeliveryGame.lean` | Exact visible alternating game, including both players' waits, messenger-first action, terminal receipt before collision, finite strategy trees, and their interpretation as actual play against every legal history-dependent pursuer. A finite-rank certificate implies actual finite delivery. |
| `SafeBranching.lean` | Two distinct already-winning successors imply a winning source when distinct closed outgoing neighborhoods overlap in at most one vertex. Safe intermediate arrival and the intervening pursuer turn are explicitly handled. Finite bootstrap certificates imply actual delivery. |
| `CampingObstruction.lean` | A pursuer whose closed outgoing neighborhood covers the recipient's predecessor set prevents every indirect delivery by camping. Consequences include no indirect guarantees in undirected graphs or through a unique predecessor. |
| `TwelveVertexCertificate.lean` | An explicit graph on 12 vertices with 24 arcs admits guaranteed delivery for every source/recipient and every allowed initial pursuer position. Every move and strict rank decrease is checked against all legal pursuer replies. The graph has exactly **108 guaranteed indirect pairs**. |
| `DenseCounting.lean` | The staircase arithmetic from explicit cardinality inequalities, the attaining count identity, and complementary-block two-move delivery in the actual game against every legal history-dependent pursuer. The graph-to-counting bridge and existence of blocks remain separate ordinary proofs. |
| `ProtectedRouting.lean` | Safe two-arrow witnesses through a protected vertex set imply universal two-move delivery, preserved under arbitrary changes to arrows wholly outside that set. The actual-play theorem covers every legal history-dependent pursuer. Witness existence, protected-set size, probabilities, and exact arc budgets are explicit boundaries, not formalized conclusions. |
| `RobustTwoMove.lean` | A base/envelope safe-intermediary certificate implies actual two-move delivery for every intermediate graph. The messenger uses only base arrows; the pursuer is granted the full envelope. Direct pairs are handled separately. |
| `RobustLayers.lean` | Strictly decreasing universal-source ranks prove actual finite delivery for every intermediate base/envelope graph. A safe entry into a routing region adds one move, including the intervening pursuer response. This supplies the semantic foundation for the new circle and guide-layer arguments; their concrete modular and code hypotheses remain ordinary proofs. |
| `StagedEnvelopes.lean` | Position-dependent ranks prove actual delivery between a base and an envelope. External staged finite certificates are not automatically instantiated. |
| `GuideAttachment.lean` | Four pursuer cases prove safe entry through antichain guide codes, then compose with a supplied interface strategy. Concrete hub lists, code instances and arrow counts remain premises to establish separately. |
| `ElevenVertexDense.lean` | The explicit dense eleven-vertex graph has 88 arrows and exactly 22 guaranteed indirect pairs; all safe intermediaries and both counts are checked by kernel reduction, with actual delivery against every legal pursuer. |
| `SmallDenseEnvelopes.lean` | Six explicit dense envelopes at orders 16 through 21: every intermediate graph has actual two-move delivery, and the endpoint arrow counts are checked by the kernel. |
| `FiniteGame.lean` | Partial winning-region rank certificates imply actual delivery. Closed losing regions exclude every finite winning tree. `Guaranteed` quantifies every allowed initial cop position. |
| `SemanticCompleteness.lean` | On finite graphs, eventual delivery under arbitrary legal history-dependent policies is equivalent to finite winning trees. One fixed messenger policy works for every permitted initial cop and every legal cop policy. Closed losing regions yield an actual legal pursuer preventing receipt at every horizon. |
| `Extremal.lean` | General guaranteed-missing-pair score, exact-maximum specification including an attainer, score bounded by missing-pair count, zero/full-delivery counting interfaces, and uniqueness of the maximum. |
| `ExactScoreCertificates.lean` | A generic winning/losing classification gives the exact score of a graph. The literal four-vertex, six-arrow graph has exactly two guaranteed missing pairs among six missing pairs. This proves its graph score, not the extremal maximum at that budget. |
| `ExclusionCertificates.lean` | A finite-cover upper-exclusion theorem requires both complete graph coverage and checked leaf bounds. The concrete pilot covers all 64 loopless three-vertex graphs and proves score zero. |
| `VertexBound.lean` | The unrestricted bound `score G ≤ n*(n-3)` for every loopless graph, derived from source camping, two distinct outgoing neighbors for every live source, and row counting. |
| `DenseZero.lean` | One guaranteed missing pair forces a missing nonloop arrow in every row. The resulting actual-graph counting bound proves `score G = 0` whenever `arcCount G > n*(n-2)` for a loopless graph. |
| `ExtremalExamples.lean` | Exact maximum specification `IsMaximum 12 24 108`, using the general upper bound and existing checked attainer; also connects the eleven-vertex dense graph to the general score, giving 22. |
| `Audit.lean` | Reports all logical axioms used by the principal theorems. |

There are 21 Lean source modules, including the axiom-reporting `Audit.lean`. The finite certificates are checked by **kernel reduction** (`decide +kernel`), not native execution or an external solver assertion. The small graphs and all certificate data are explicit in the Lean source. The general vertex bound, complete dense zero band and exact `(12,24)` extremal cell are connected through the same formal score definition, whose equivalence to actual guaranteed eventual delivery is proved.

The generated numbers do not establish their own correctness: `certificate_valid` checks the actual legal arcs, waits, nonterminal capture exclusions, and strict rank decrease for every state and every possible pursuer reply. `rankCertificate_actual_delivery` then proves the semantic interpretation, including termination. The pursuer sees the messenger's move and may depend on the whole observed history. The messenger's selected policy observes the current positions and remaining move budget, never a future pursuer response.

The protected-routing hypothesis supplies, for every distinct source `s` and recipient `t` and every initial pursuer `c≠s`, an intermediary `u` in the protected set with arrows `s→u` and `u→t`, with `u≠c` and no arrow `c→u`. Both incoming and outgoing arrows touching the protected set must agree between the original and modified graphs. `protected_witness_winning` proves that the same witness remains safe; `protected_routing_universal` derives the two-move winning relation; and `protected_routing_actual_delivery` interprets it using the existing concrete game. This includes pursuer waiting, a pursuer initially at the recipient, and receipt before collision. The single-witness theorem is axiom-free.

## Current boundary

The infinite circulant and parabola families, modular arithmetic, all-order parameter choices, sparse arc-budget bounds, the dense staircase graph-to-counting bridge, probabilistic existence arguments, and the complete original-construction count remain ordinary proofs or explicitly labeled computational evidence in the manuscript. Protected-routing witness existence, probability estimates, exact-budget conditioning, and the deterministic construction algorithm also remain ordinary proofs. The numerical staircase implication is formalized, with its cardinality hypotheses exposed. The bootstrap, gluing, guide-attachment and protected-routing theorems assume their displayed structural premises; the current Lean sources do not silently assert those premises or existence of the required blocks or routing sets.

`Guaranteed E s t` is defined using finite `Winning` trees. `SemanticCompleteness.guaranteed_iff_actual` proves that, on finite graphs, it is equivalent to the existence of one fixed legal history-dependent messenger policy that eventually delivers against every permitted initial cop and every legal history-dependent cop policy. No horizon is assumed in the actual-play definition; finite reply sets supply the common bound in the proof. Thus the score and upper/exact-cell theorems have a proved actual-game interpretation. This semantic completeness is separate from completeness of graph enumeration: the three-vertex pilot covers its entire small graph space, while the larger external degree-profile enumerations, symmetry reductions, pruning and finite tables remain unformalized. The mixed four-vertex certificate establishes one graph's exact score and does not establish an unrestricted upper bound. No full-classification theorem is claimed.

The central strategy theorems use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` where reported by `Audit.lean`. There are no `sorry`, `admit`, custom axioms, or `native_decide` proofs. Classical choice extracts a messenger policy from the proved finite strategy-tree relation.

## Portable replay

Install the version named in `lean-toolchain` and put its `lean` executable on PATH. From this directory run:

```sh
python3 check.py
```

Alternatively supply its location:

```sh
python3 check.py --lean /path/to/lean
```

The checker rebuilds each module sequentially, rejects unexpected `sorry` dependencies, runs the axiom audit, and writes `verification.json` with exact source hashes, tool version, elapsed times, and compiler outputs. Compiled object files are excluded from source distribution and are regenerated locally.

`generate_finite_certificate.py` can regenerate the explicit small certificate from the saved research graph and solver. It is not needed for replay, because all data are already in the Lean source. It is outside the proof trust boundary: an incorrect generated certificate fails the kernel-checked theorem.

## Provenance

The underlying problem and original layered construction come from Alexandra Ignatova's manuscript, with Angel Raychev as mentor. These formal sources are September 2026 extensions developed with Astra 6 through the Codex harness. Publication authorship is recorded in the manuscript.

`DenseZero.maximum_zero` proves `IsMaximum n m 0` whenever `n*(n-2) < m ≤ n*(n-1)`. Its explicit attainer takes the first `m` nonloop ordered pairs in lexicographic order; looplessness and its exact arrow count are proved, with no graph-existence premise.

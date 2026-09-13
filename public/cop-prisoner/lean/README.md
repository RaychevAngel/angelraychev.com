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
| `ElevenVertexDense.lean` | The explicit dense eleven-vertex graph has 88 arrows and exactly 22 guaranteed indirect pairs; all safe intermediaries and both counts are checked by kernel reduction, with actual delivery against every legal pursuer. |
| `SmallDenseEnvelopes.lean` | Six explicit dense envelopes at orders 16 through 21: every intermediate graph has actual two-move delivery, and the endpoint arrow counts are checked by the kernel. |
| `Audit.lean` | Reports all logical axioms used by the principal theorems. |

The finite certificates are checked by **kernel reduction** (`decide +kernel`), not native execution or an external solver assertion. The small graphs and all certificate data are explicit in the Lean source. Its construction attains the separately proved ordinary bound `I≤n(n−3)` at n=12; the general extremal counting argument is not currently formalized.

The generated numbers do not establish their own correctness: `certificate_valid` checks the actual legal arcs, waits, nonterminal capture exclusions, and strict rank decrease for every state and every possible pursuer reply. `rankCertificate_actual_delivery` then proves the semantic interpretation, including termination. The pursuer sees the messenger's move and may depend on the whole observed history. The messenger's selected policy observes the current positions and remaining move budget, never a future pursuer response.

The protected-routing hypothesis supplies, for every distinct source `s` and recipient `t` and every initial pursuer `c≠s`, an intermediary `u` in the protected set with arrows `s→u` and `u→t`, with `u≠c` and no arrow `c→u`. Both incoming and outgoing arrows touching the protected set must agree between the original and modified graphs. `protected_witness_winning` proves that the same witness remains safe; `protected_routing_universal` derives the two-move winning relation; and `protected_routing_actual_delivery` interprets it using the existing concrete game. This includes pursuer waiting, a pursuer initially at the recipient, and receipt before collision. The single-witness theorem is axiom-free.

## Current boundary

The infinite circulant and parabola families, modular arithmetic, all-order parameter choices, graph-to-counting inequalities for extremal bounds, arc-budget extremal formulas, probabilistic existence arguments, and the complete original-construction count remain ordinary proofs or explicitly labeled computational evidence in the manuscript. Protected-routing witness existence, probability estimates, exact-budget conditioning, and the deterministic construction algorithm also remain ordinary proofs. The numerical staircase implication is formalized, with its cardinality hypotheses exposed. The bootstrap, gluing, and protected-routing theorems assume their displayed structural premises; the current Lean sources do not silently assert those premises or existence of the required blocks or routing sets.

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

The underlying problem and original layered construction come from Alexandra Ignatova's manuscript, with Angel Raychev as mentor. These formal sources are September 2026 extensions developed with Astra 6 through the Codex harness. They do not resolve publication authorship metadata.


`StagedEnvelopes.lean` proves actual delivery in every graph between a base and an envelope from a rank depending on both positions. Its hypotheses are not automatically instantiated by the external staged finite certificates. The full main-interval classification, concrete circle rules and hub parameters remain ordinary/computer-assisted proofs.

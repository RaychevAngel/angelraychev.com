# Lean verification: guaranteed indirect delivery

Pinned toolchain: **Lean 4.33.1**. Dependencies: **Std only**, supplied with Lean. No Mathlib, external game library, or assumed graph-game equivalence is required.

## What is proved

| Module | Verified statement |
|---|---|
| `DeliveryGame.lean` | Exact visible alternating game, including both players' waits, messenger-first action, terminal receipt before collision, finite strategy trees, and their interpretation as actual play against every legal history-dependent pursuer. A finite-rank certificate implies actual finite delivery. |
| `SafeBranching.lean` | Two distinct already-winning successors imply a winning source when distinct closed outgoing neighborhoods overlap in at most one vertex. Safe intermediate arrival and the intervening pursuer turn are explicitly handled. Finite bootstrap certificates imply actual delivery. |
| `CampingObstruction.lean` | A pursuer whose closed outgoing neighborhood covers the recipient's predecessor set prevents every indirect delivery by camping. Consequences include no indirect guarantees in undirected graphs or through a unique predecessor. |
| `TwelveVertexCertificate.lean` | An explicit graph on 12 vertices with 24 arcs admits guaranteed delivery for every source/recipient and every allowed initial pursuer position. Every move and strict rank decrease is checked against all legal pursuer replies. The graph has exactly **108 guaranteed indirect pairs**. |
| `Audit.lean` | Reports all logical axioms used by the principal theorems. |

The finite certificate is checked by **kernel reduction** (`decide +kernel`), not native execution or an external solver assertion. The small graph and all certificate data are explicit in the Lean source. Its construction attains the separately proved ordinary bound `I≤n(n−3)` at n=12; the general extremal counting argument is not currently formalized.

The generated numbers do not establish their own correctness: `certificate_valid` checks the actual legal arcs, waits, nonterminal capture exclusions, and strict rank decrease for every state and every possible pursuer reply. `rankCertificate_actual_delivery` then proves the semantic interpretation, including termination. The pursuer sees the messenger's move and may depend on the whole observed history. The messenger's selected policy observes the current positions and remaining move budget, never a future pursuer response.

## Current boundary

The infinite circulant family, modular arithmetic, all-order parameter choices, exact extremal upper bounds beyond the finite example, arc-budget extremal formulas, and the complete original-construction count remain ordinary proofs or explicitly labeled computational evidence in the manuscript. The bootstrap theorem assumes its displayed overlap condition; the current Lean sources do not silently assert that condition for all circulants.

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

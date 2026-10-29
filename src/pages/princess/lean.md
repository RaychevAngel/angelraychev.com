---
layout: "../../layouts/Post.astro"
title: "Princess searches: verified proofs"
description: "What Lean verifies, what still has ordinary proofs, and how to reproduce the formal checks."
updated: 2026-10-29
---

[Overview](/princess/) · [Readable proofs](/princess/proofs/) · [Paper](/princess/paper/) · [Parked formal results](/princess/extensions/lean/)

**In the rectangle core, Lean verifies the complete answers for paths and two-row grids.** The other geometric classifications currently have ordinary mathematical proofs. A successful build of the formal archive should not be read as formal verification of every result in the manuscript.

[**Download the Lean sources**](/princess/lean-proofs.zip) · [Verification receipt](/princess/lean-verification.json) · [Artifact guide](/princess/formal-artifact.md)

## What changed on 29 October 2026

The new [PairedCompression.lean](/princess/lean/PairedCompression.lean) proves complement-dual compression and the correct reversed compatibility for time-dependent operators. It explicitly constructs transformed inspections, preserves each daily cap, identifies the resulting states with actual possible-position histories, and proves that the two endpoint envelopes overlap no more than before. Both prefixes may start with full uncertainty.

The theorem requires a supplied valid monotone, cardinality-preserving, neighborhood-compatible compression on a finite undirected graph. **It does not construct such an operator for the unresolved rectangles.** It is a checked proof tool, not a new complete capture-time classification.

The uniform two-day bound, the new all-budget exact large-odd-width range, the paired-boundary geometric constructions and the two improved physical strategies have ordinary proofs and independent internal reviews. They remain outside complete Lean coverage. The previously unverified symbolic comparison has since passed ordinary independent checks; that does not make it a Lean theorem.

The [29 October formal-source audit](/princess/checkpoint-formal-coverage-2026-10-29.json) and [compiler receipt](/princess/lean-verification.json) identify the exact checked sources and dates. The historical compiler receipts remain preserved in the dated source archives.

## Complete physical classifications

| Family | Verified statement | Main source |
| --- | --- | --- |
| A path with any positive number of rooms | Feasibility, the exact minimum number of days, and an explicit strategy for every positive budget | [PathClassification.lean](/princess/lean/PathClassification.lean) |
| Any two-row grid | The exact optimum, interpreted as actual room inspections and arbitrary avoiding walks | [LadderGame.lean](/princess/lean/LadderGame.lean) |

The conclusions concern the physical room graphs. They include the daily inspection budget, movement after each miss, and all legal choices of the princess. They do not assume that she follows a preferred route or that an arbitrary strategy uses a preferred shape of possible-position set.


## Supporting theorems

[BipartiteProfileDuality.lean](/princess/lean/BipartiteProfileDuality.lean) defines the two minimum-neighborhood profiles of an arbitrary finite bipartite graph and proves their complement relation. For parts of sizes $M+1,M$ with no isolated vertices, their maximum neighborhood surpluses differ by exactly one. [ProfileInverse.lean](/princess/lean/ProfileInverse.lean) supplies the inverse arithmetic. This is a complete graph theorem; it does not by itself formalize the geometric nesting needed for its rectangle or parked box applications.

[BeliefSemantics.lean](/princess/lean/BeliefSemantics.lean) proves that a room is possible precisely when a legal walk reaches it while avoiding all previous inspections. [CaptureRecurrence.lean](/princess/lean/CaptureRecurrence.lean) proves the finite winning recurrence and the complementary losing trap.

[ProbeLocalization.lean](/princess/lean/ProbeLocalization.lean) proves an exact localization theorem on arbitrary directed graphs. Compare the final possible-position set of a search with the final set obtained without inspections. Keeping only inspections in the backward reachability region of their difference preserves the search's final set exactly. The geometric argument bounding that region on cylinders is an ordinary proof.

[RootConvolution.lean](/princess/lean/RootConvolution.lean) defines the integer square and pronic roots and proves that a constrained sum of two such roots attains its minimum at one of two explicit candidates. It includes the attaining positions, not only a lower estimate.

[StrategyCompression.lean](/princess/lean/StrategyCompression.lean) verifies the abstract theorem that lets an appropriate geometric compression transform arbitrary strategies without increasing their inspection budget. Constructing such a compression for a new graph remains a separate mathematical obligation.

[SurvivorEnvelope.lean](/princess/lean/SurvivorEnvelope.lean) proves that the fixed-deadline column certificates are equivalent to capture of every actual target walk, including the correspondence between local column costs and the daily inspection budget. The subsequent proof of eventual periodicity uses ordinary mathematics and is not yet formalized.

The five-row proofs have verified scalar inequalities in [FiveRowRankArithmetic.lean](/princess/lean/FiveRowRankArithmetic.lean), [FiveRowOddRankArithmetic.lean](/princess/lean/FiveRowOddRankArithmetic.lean), and [FiveRowDeficitArithmetic.lean](/princess/lean/FiveRowDeficitArithmetic.lean). The four-probe lower bound and its extra-day obstruction have separate checks in [FiveRowFourProbeArithmetic.lean](/princess/lean/FiveRowFourProbeArithmetic.lean) and [FiveRowFourProbeEquality.lean](/princess/lean/FiveRowFourProbeEquality.lean). [FiveRowHighBudgetArithmetic.lean](/princess/lean/FiveRowHighBudgetArithmetic.lean) checks the three finite high-budget bounds. The geometric lemmas connecting these inequalities to arbitrary five-row searches are proved in the manuscript and are **not yet formalized**.

[UniformOddRank.lean](/princess/lean/UniformOddRank.lean) checks the universal scalar inequality behind the odd-rectangle minimum-budget lower bound. The interval-insertion theorem, the eventual periodic time theorem for odd cylinders, and their geometric applications currently have ordinary proofs and independent reviews.

[ConvexCapacityConvolution.lean](/princess/lean/ConvexCapacityConvolution.lean) strengthens the root-specific calculation to arbitrary nondecreasing, unbounded discrete-convex capacities. It constructs least roots, proves the two-candidate minimum, and instantiates every punctured-quadrant capacity $C_h$. This is a complete arithmetic theorem; the geometric capacity formula is not formalized by it.

[ClippedPyramidErosion.lean](/princess/lean/ClippedPyramidErosion.lean) uses actual finite cylinder cells to verify the clipped erosion, neighborhood inclusion, and exact loss of occupied bottom roots. Its distance threshold and the surrounding construction theorem remain ordinary proofs.

[FastestAncestry.lean](/princess/lean/FastestAncestry.lean) verifies the shared-quota recurrence, persistence of low-total states, fastest ancestry after pure resets, and a composed midpoint obstruction. The profile inequalities and secondary-size bounds are explicit hypotheses. Their geometric rectangle instances and the final all-width time law remain ordinary proofs.

## Source separation and verification

There are now **84 canonical Lean modules**. The rectangle package contains 44 and the parked companion 51, with eleven shared dependencies. PairedCompression is the one new module. The [scope manifest](/princess/lean-scope.json) assigns each module and its imports; the source files have one authoritative home, while downloadable packages contain distribution copies.

All 84 canonical modules passed a fresh sequential Lean 4.33.1 compilation on 29 October 2026. The current compiler receipt records each source hash, exit status and axiom report. The complete path and two-row classifications retain their physical-game interpretation. The complete cube classifications remain in the [parked companion](/princess/extensions/lean/) and are not counted as completion of the rectangle theorem.

## Reproduce the check

The project uses **Lean 4.33.1 and its standard library**, with no additional package installation. Extract the archive and run:

```text
python3 src/check_lean.py --lean /path/to/lean
```

The checker compiles dependencies afresh, uses one compiler worker, and records each source hash, exit status, and theorem axiom report. Read `lean/README.md` in the archive for the detailed theorem map. The [release record](/princess/release.json) identifies the PDF and archives by checksum; the [compiler receipt](/princess/lean-verification.json) identifies the exact checked mathematical sources.

There are no admitted proofs, project-specific axioms, or trusted external solver results in the verified development. Where needed, the final theorems use Lean’s standard principles `propext`, `Classical.choice`, and `Quot.sound`. Finite certificates are evaluated by the kernel.

## Work still to formalize

The complete three-row, four-row, and five-row formulas, the general rectangle time formulas, the bounded odd-rectangle evaluator, the geometric interface theorem, and their remaining physical applications still have ordinary proofs. Independent higher-dimensional formalization goals are parked with the companion. The [full proof text](/princess/proofs/) states their hypotheses and arguments. Numerical experiments elsewhere in the research archive are explicitly distinguished from proofs.

The new [MiddleIntervalTransfer.lean](/princess/lean/MiddleIntervalTransfer.lean) proves exact reachability for two bounded counters sharing a daily budget, including a construction of every intermediate allocation. Its physical rectangle application and the new uniform time and neighborhood theorems remain ordinary proofs.

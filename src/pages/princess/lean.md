---
layout: "../../layouts/Post.astro"
title: "Princess searches: verified proofs"
description: "What Lean verifies, what still has ordinary proofs, and how to reproduce the formal checks."
updated: 2026-09-12
---

[Overview](/princess/) · [Readable proofs](/princess/proofs/) · [Paper](/princess/paper/)

**Lean verifies the complete answers for paths, two-row grids, and the $3\times3\times3$ and $4\times4\times4$ boxes.** The other geometric classifications currently have ordinary mathematical proofs. A successful build of the formal archive should not be read as formal verification of every result in the manuscript.

[**Download the Lean sources**](/princess/lean-proofs.zip) · [Verification receipt](/princess/lean-verification.json) · [Artifact guide](/princess/formal-artifact.md)

## Complete physical classifications

| Family | Verified statement | Main source |
| --- | --- | --- |
| A path with any positive number of rooms | Feasibility, the exact minimum number of days, and an explicit strategy for every positive budget | [PathClassification.lean](/princess/lean/PathClassification.lean) |
| Any two-row grid | The exact optimum, interpreted as actual room inspections and arbitrary avoiding walks | [LadderGame.lean](/princess/lean/LadderGame.lean) |
| The $3\times3\times3$ box | Feasibility and the exact minimum number of days for every positive budget | [ThreeCubeTimeClassification.lean](/princess/lean/ThreeCubeTimeClassification.lean) |
| The $4\times4\times4$ box | Feasibility and the exact minimum number of days for every budget, including the forty-day eight-probe result | [FourCubeClassification.lean](/princess/lean/FourCubeClassification.lean) |

The conclusions concern the physical room graphs. They include the daily inspection budget, movement after each miss, and all legal choices of the princess. They do not assume that she follows a preferred route or that an arbitrary strategy uses a preferred shape of possible-position set.

For the four-cube, Lean verifies the geometric compression itself, its effect on arbitrary strategies, the shape-dependent eight-probe lower bound, the remaining budget bounds, and physical schedules attaining every endpoint. The compression is a proved reduction; it is not an assumption restricting the competing searcher.

## Supporting theorems

[BipartiteProfileDuality.lean](/princess/lean/BipartiteProfileDuality.lean) defines the two minimum-neighborhood profiles of an arbitrary finite bipartite graph and proves their complement relation. For parts of sizes $M+1,M$ with no isolated vertices, their maximum neighborhood surpluses differ by exactly one. [ProfileInverse.lean](/princess/lean/ProfileInverse.lean) supplies the inverse arithmetic. This is a complete graph theorem; it does not by itself formalize the geometric nesting needed for the odd-box application.

[BeliefSemantics.lean](/princess/lean/BeliefSemantics.lean) proves that a room is possible precisely when a legal walk reaches it while avoiding all previous inspections. [CaptureRecurrence.lean](/princess/lean/CaptureRecurrence.lean) proves the finite winning recurrence and the complementary losing trap.

[StrategyCompression.lean](/princess/lean/StrategyCompression.lean) verifies the abstract theorem that lets an appropriate geometric compression transform arbitrary strategies without increasing their inspection budget. Constructing such a compression for a new graph remains a separate mathematical obligation.

[SurvivorEnvelope.lean](/princess/lean/SurvivorEnvelope.lean) proves that the fixed-deadline column certificates are equivalent to capture of every actual target walk, including the correspondence between local column costs and the daily inspection budget. The subsequent proof of eventual periodicity uses ordinary mathematics and is not yet formalized.

The five-row proofs have verified scalar inequalities in [FiveRowRankArithmetic.lean](/princess/lean/FiveRowRankArithmetic.lean), [FiveRowOddRankArithmetic.lean](/princess/lean/FiveRowOddRankArithmetic.lean), and [FiveRowDeficitArithmetic.lean](/princess/lean/FiveRowDeficitArithmetic.lean). The four-probe lower bound and its extra-day obstruction have separate checks in [FiveRowFourProbeArithmetic.lean](/princess/lean/FiveRowFourProbeArithmetic.lean) and [FiveRowFourProbeEquality.lean](/princess/lean/FiveRowFourProbeEquality.lean). [FiveRowHighBudgetArithmetic.lean](/princess/lean/FiveRowHighBudgetArithmetic.lean) checks the three finite high-budget bounds. The geometric lemmas connecting these inequalities to arbitrary five-row searches are proved in the manuscript and are **not yet formalized**.

[UniformOddRank.lean](/princess/lean/UniformOddRank.lean) checks the universal scalar inequality behind the odd-rectangle minimum-budget lower bound. The interval-insertion theorem, the eventual periodic time theorem for odd cylinders, and their geometric applications currently have ordinary proofs and independent reviews.

## Reproduce the check

The project uses **Lean 4.33.1 and its standard library**, with no additional package installation. Extract the archive and run:

```text
python3 src/check_lean.py --lean /path/to/lean
```

The checker compiles dependencies afresh, uses one compiler worker, and records each source hash, exit status, and theorem axiom report. Read `lean/README.md` in the archive for the detailed theorem map. The [release record](/princess/release.json) identifies the PDF and archives by checksum; the [compiler receipt](/princess/lean-verification.json) identifies the exact checked mathematical sources.

There are no admitted proofs, project-specific axioms, or trusted external solver results in the verified development. Where needed, the final theorems use Lean’s standard principles `propext`, `Classical.choice`, and `Quot.sound`. Finite certificates are evaluated by the kernel.

## Work still to formalize

The complete three-row, four-row, and five-row formulas, the wider odd-rectangle formula, the all-odd-box isoperimetric theorem, the general application to boxes with a side of length two, and the cylinder constructions and eventual-period theorems still have ordinary proofs. The [full proof text](/princess/proofs/) states their hypotheses and arguments. Numerical experiments elsewhere in the research archive are explicitly distinguished from proofs.

The new [MiddleIntervalTransfer.lean](/princess/lean/MiddleIntervalTransfer.lean) proves exact reachability for two bounded counters sharing a daily budget, including a construction of every intermediate allocation. Its physical rectangle application and the new uniform time and neighborhood theorems remain ordinary proofs.

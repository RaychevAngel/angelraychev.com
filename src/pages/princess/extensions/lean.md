---
layout: "../../../layouts/Post.astro"
title: "Princess extensions: formal coverage"
description: "Preserved cube classifications and shared formal components in the parked extension project."
updated: 2026-09-13
---

[Parked overview](/princess/extensions/) · [Companion proofs](/princess/extensions/proofs/) · [Rectangle Lean coverage](/princess/lean/)

**Parked, with existing verification preserved.** The complete physical $3\times3\times3$ and $4\times4\times4$ classifications remain Lean theorems. This reorganization neither adds nor withdraws a formal result.

[Companion Lean package](/princess/extensions/extensions-lean-proofs.zip) · [Exact source scope](/princess/lean-scope.json) · [Existing compiler receipt](/princess/extensions/lean-verification.json)

The [three-cube theorem](/princess/lean/ThreeCubeTimeClassification.lean) covers every positive daily budget, physical target walks, lower bounds and attaining inspections. The [four-cube theorem](/princess/lean/FourCubeClassification.lean) covers every budget, including forty days at eight inspections and the shape-sensitive reduction needed to prove that minimum. The formal proofs allow arbitrary competing inspection sequences.

Generic strategy compression, finite subset certificates, physical belief semantics and related shared modules support these theorems. Each dependency remains in the canonical source directory and is included where needed in the downloadable package. The module manifest distinguishes shared tools from independent applications. No second authoritative version is maintained.

The general odd-box nesting theorem, the general side-of-length-two application, the $3\times4\times4$ classification, the $3\times3\times n$ families and the broader cylinder laws have ordinary mathematical proofs or finite certificates at their stated boundaries. They are **not** all completely formalized by the cube results or by the aggregate compiler receipt.

The existing source-specific check passed 83 modules in the combined development. This release checks that the distributed sources still match those hashes and that imports are closed. To reproduce a fresh compiler check, extract this package and run `python3 src/check_lean.py --lean /path/to/lean` with Lean 4.33.1. Read the included guide for its exact scope.

The unresolved formalization of independent companion geometry is parked. It is not a condition for completing the main rectangle paper.

The companion package contains 51 modules, including eleven dependencies shared with the 43-module rectangle package. There are 83 canonical modules in total; distribution copies are not separate authoritative proofs.

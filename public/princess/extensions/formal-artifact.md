# Princess searches: formal artifact scopes

Coverage synchronized to the 29 October 2026 research checkpoint. The active project is two-dimensional rectangle capture time with a constant daily inspection budget and full initial uncertainty. Independent extensions remain parked.

Canonical Lean sources remain in `lean/`; `publication/lean-scope.json` records every module and local import. There are 84 canonical modules: 44 in the rectangle package and 51 in the companion, with 11 shared dependencies. Complete rectangle physical classifications remain paths and two-row grids. Complete parked physical classifications remain the 3×3×3 and 4×4×4 boxes.

## New formal theorem

`PairedCompression.lean` proves complement-dual compression, the reversed compatibility of time-dependent neighborhood operators, and contraction of joining overlap. It explicitly constructs transformed inspections, preserves every daily budget, and proves the transformed states equal actual possible-position histories, including two prefixes starting from full uncertainty.

The supplied operator must already satisfy the stated monotonicity, size and neighborhood hypotheses on a finite undirected graph. The module does not construct the missing rectangle compression, prove general boundary arrival, or prove a new capture-time classification.

## Compiler evidence

The release compiler receipt is `research/lean-verification.json`; its source hashes and individual exit codes identify exactly what was checked with Lean 4.33.1. The new module also has an isolated seven-source compilation receipt and an independent semantic review under `research/publication-2026-10-29/`. The September 83-source receipt is preserved as `lean-historical-verification.json` in that directory and in dated archives. The current coverage audit is `research/checkpoint-formal-coverage-2026-10-29.json`.

No admitted proofs, project-specific axioms or trusted external solver outputs are introduced. The standard principles `propext`, `Classical.choice` and `Quot.sound` appear where reported.

## Ordinary proofs, not complete Lean classifications

The whole-domain two-day bound, all-budget exact capture at odd widths at least 8193 and even length, new paired-boundary geometric constructions, improved 285/413-day strategies, and strict-collar arrival obstruction have ordinary proofs, internal independent reviews and exact checks where stated. They are not complete Lean theorems. The formerly unverified 751-profile comparison has since passed ordinary independent checks; it is not a Lean certificate.

Read `lean/README.md` for theorem-level scope. After extracting either Lean package, run `python3 src/check_lean.py --lean /path/to/lean` from its root. The checker uses one compiler worker and the standard library. PDF and source archive hashes are recorded in `release.json`.

Main: https://angelraychev.com/princess/
Formal guide: https://angelraychev.com/princess/lean/
Parked companion: https://angelraychev.com/princess/extensions/
Historical combined release: https://angelraychev.com/princess/archive/2026-09-13-combined/

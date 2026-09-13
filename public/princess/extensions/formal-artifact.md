# Princess searches: formal artifact scopes

The active project is the complete two-dimensional rectangle capture-time
problem with a constant daily inspection budget and full initial uncertainty.
The parked companion preserves independent higher-dimensional and other
extension results. The split changes exposition and package membership,
not mathematical proofs.

Canonical Lean sources remain in `lean/`. `publication/lean-scope.json`
records every module and its local imports: the main package contains 43
modules and the companion 51, sharing 11 source modules. The combined
repository contains 83. Main complete physical classifications: paths
and two-row rectangles. Parked complete physical classifications: the
3×3×3 and 4×4×4 boxes. The newest general rectangle theorems remain ordinary
proofs with separately stated partial formalization.

This release verifies unchanged hashes against the existing Lean 4.33.1
receipt and verifies package import closure. It does not claim a fresh
compilation. Each scoped receipt keeps the original compilation date and
identifies its source receipt; the full receipt is retained separately.
To perform a fresh check after extracting either Lean package, run
`python3 src/check_lean.py --lean /path/to/lean` from its root.
The checker runs sequentially with one worker and no extra packages.

Main: https://angelraychev.com/princess/
Main proof coverage: https://angelraychev.com/princess/lean/
Parked companion: https://angelraychev.com/princess/extensions/
Parked proof coverage: https://angelraychev.com/princess/extensions/lean/
Historical combined release: https://angelraychev.com/princess/archive/2026-09-13-combined/

Read `lean/README.md` for theorem-level scope. Archive and PDF checksums
are recorded in each publication's `release.json`.

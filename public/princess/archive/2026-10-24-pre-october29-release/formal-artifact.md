# Princess searches: formal artifact scopes

Coverage synchronized to the **24 October 2026 research checkpoint**.
The active project is the two-dimensional rectangle capture-time problem
with a constant daily inspection budget and full initial uncertainty.
The parked companion preserves independent higher-dimensional and other
extension results. The split changes exposition and package membership,
not mathematical proofs.

Canonical Lean sources remain in `lean/`. `publication/lean-scope.json`
records every module and its local imports: the main package contains 43
modules and the companion 51, sharing 11 source modules. The combined
repository contains 83. Main complete physical classifications are paths
and two-row rectangles. Parked complete physical classifications are the
3×3×3 and 4×4×4 boxes.

## Evidence at this checkpoint

**Accepted ordinary mathematics, not new complete Lean theorems.** The
uniform whole-domain gap of at most four days, its stated two-day
refinements, the new exact even-width transport families, and the exact
odd-width/even-length gate families with their central-span refinement
have ordinary proofs and the independent reviews identified in the
checkpoint. Their new geometric and phase-history tools are not completely
formalized. Existing reusable Lean lemmas do not discharge the missing
physical-game hypotheses automatically.

**Unverified candidate, excluded from the proved bounds.** The finite
symbolic comparison closure is a discovery certificate. Independent
replay, entrance and primitive-range checks, the stopping rule, and the
physical gate assembly remain outstanding. It is neither an accepted
capture-time theorem nor a Lean result.

**Formal evidence preserved.** The 24 October audit checks all 83 current
source hashes against the successful Lean 4.33.1 compilation receipt dated
13 September 2026, verifies every recorded local import, and checks both
package import closures. It finds no changed formal source. This is not
a fresh compilation or new formalization. The exact audit is
`research/checkpoint-formal-coverage-2026-10-24.json`; the historical
compiler receipt remains `research/lean-verification.json`. Each scoped
receipt retains the original compilation date and its source receipt.

Read `lean/README.md` for the theorem-level scope. To perform a fresh check
after extracting either Lean package, run
`python3 src/check_lean.py --lean /path/to/lean` from its root.
The checker runs sequentially with one worker and no extra packages.
Archive and PDF checksums are recorded in each publication's `release.json`.

Main: https://angelraychev.com/princess/
Main proof coverage: https://angelraychev.com/princess/lean/
Parked companion: https://angelraychev.com/princess/extensions/
Parked proof coverage: https://angelraychev.com/princess/extensions/lean/
Historical combined release: https://angelraychev.com/princess/archive/2026-09-13-combined/

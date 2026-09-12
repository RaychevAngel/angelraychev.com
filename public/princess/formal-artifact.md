# Princess searches: formal artifact

This checkpoint uses Lean 4.33.1 and Std. The source-specific verification
receipt gives the exact files and their SHA-256 hashes. The final physical
classifications cover all paths, all two-row grids, and every budget on the
3×3×3 and 4×4×4 boxes. The ordinary proofs of the other manuscript results are not
presented as complete Lean proofs.

Download `lean-proofs.zip`, extract it, and run
`python3 src/check_lean.py --lean /path/to/lean` from its root. Read
`lean/README.md` for the exact theorem map and partial proof boundaries.
The checker uses one compiler worker and no additional packages.

`release.json` gives archive and PDF checksums for this checkpoint.
`research/lean-verification.json` contains the compiler output and per-source
hashes. Finite kernel-checked certificates do not trust their generating search.

Companion: https://angelraychev.com/princess/
Paper: https://angelraychev.com/princess/paper/
Proofs: https://angelraychev.com/princess/proofs/
Lean: https://angelraychev.com/princess/lean/

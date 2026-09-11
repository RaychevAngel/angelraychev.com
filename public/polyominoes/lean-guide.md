# Verified Lean proofs: T shapes, crosses, and the exceptional L case

This source package contains complete Lean 4.33.1 proofs, using the standard
library only. It includes every local dependency of the entry points
below. No precompiled proof objects or external theorem prover are required.

## Statements

- `InitialTwoClassification.lean`: `PolyominoFormal.p4_exact_bs` and
  `PolyominoFormal.p5_exact_bs`. Both shapes tile bent strips, quadrants,
  strips, half-planes, and the plane. Neither tiles any half-strip,
  rectangle, or integer enlargement of itself.
- `GunFamilyClassification.lean`: `classify_gun` proves the full family
  P(n,1,1,0), for every natural n. The rectangle profile holds exactly for
  n<=3; the bent-strip profile holds for every n>=4.
- `TClassification.lean`: `normalized_T_classified` proves the entire
  eight-capability classification for every a>=c>=1 and b>=1.
- `PositiveCrossClassification.lean`: `classify_positive_cross` proves
  the full classification when all four arms are positive.
- `LHalfPlaneFiveThree.lean`: `LHalfPlaneFiveThree.no_halfplane` excludes
  a half-plane tiling by P(5,3,0,0), the L shape with bounding box 6 by 4.

**The last general L obstruction is still being formalized.** This package
does not claim an unconditional Lean theorem for all four-tuples. The
remaining input is that P(a,b,0,0) cannot tile a half-plane when a>b>=3 and
a>=5. The supplied 2021 L-polyomino paper is the existing mathematical
proof; the exceptional pair (5,3) already has the Lean proof listed above.

## Exact conventions and trust

Arms run east, north, west, south, excluding the shared junction square.
`TilingCore.lean` defines arbitrary infinite sets of whole tiles, all eight
rotations/reflections, integer translations, containment, exact cover, and
pairwise disjointness. No periodicity or finite tile-count assumption is
made. `HierarchyProfiles.lean` spells out each capability. Rep-tiling means
congruent copies of the original tile covering its integer enlargement at
a natural linear scale at least two; unequal-scale dissections and off-grid
placements are outside this statement.

The compiled theorem reports use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no admitted proofs, added axioms, `native_decide`
calls, or trusted solver answers. Search programs helped discover finite
case trees; the included Lean terms check both the arithmetic and their
application to actual tilings. In particular, an arbitrary-width half-strip
obstruction is proved by a well-founded descent, not by testing widths.

## Rebuild

Unzip the archive, enter its `polyominoes` directory, and install Lean
4.33.1. To start with the disputed cases:

```sh
python3 src/check_lean.py InitialTwoClassification --jobs 2
```

To check every packaged entry point:

```sh
python3 src/check_lean.py GunFamilyClassification TClassification PositiveCrossClassification LHalfPlaneFiveThree --jobs 2
```

Use `--lean /absolute/path/to/lean` if needed. The driver compiles the
source dependencies into `.build/lean`, records their hashes and compiler
logs, and reuses only exactly matching results. A new `--output` directory
forces a fresh rebuild. Some finite proof data take appreciably longer to
check than the short final statements. The archive's `MANIFEST.json`
records the exact hash of every included source file.

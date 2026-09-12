# Formal artifact accompanying the four-arm polyomino classification

This note identifies the accepted proof package, its exact mathematical scope, and how to check it. It distinguishes the recorded completed Lean build from the source and packaging checks performed during manuscript preparation.

## Fixed artifact identity

- Archive: `lean-proofs.zip`.
- Exact byte count: **14,670,185**.
- SHA-256: `c2aec8f60dd5e2f4054eda26a947a1a7398f214ba248dee48358fc592b4043a3`.
- Toolchain: **Lean 4.33.1**, using only its standard library in addition to the packaged local sources.
- Local source modules: **538**.
- Entry points: `MainClassification`, `GunFamilyClassification` (the latter is also in the former's transitive dependency closure).
- Existing immutable repository commit: `ec308bfcb092fa71a78cecd991be6e85e5b369b9` in [RaychevAngel/angelraychev.com](https://github.com/RaychevAngel/angelraychev.com/tree/ec308bfcb092fa71a78cecd991be6e85e5b369b9).
- [Commit-pinned artifact](https://raw.githubusercontent.com/RaychevAngel/angelraychev.com/ec308bfcb092fa71a78cecd991be6e85e5b369b9/public/polyominoes/lean-proofs.zip).
- [Convenience download](https://angelraychev.com/polyominoes/lean-proofs.zip), which may point to later versions in future.

The commit-pinned archive is the immutable artifact reference for this manuscript. The manuscript version and the already verified mathematical source package are identified separately. Future release notes should retain the hash and full commit above; a release tag alone is less precise than these identifiers. Any future correction to a formal definition or proof should receive a new artifact identity and a new verification record.

## Exact theorem and semantics

The final declaration is `PolyominoFormal.all_tuples_classified (a b c d : Nat) : Classified a b c d (classifyTuple a b c d)` in `lean/MainClassification.lean`. There are no additional obstruction or family-classification hypotheses.

Arms run east, north, west, south and exclude the shared junction square. All four parameters range over every nonnegative integer, including the all-zero monomino. The classification gives equivalences for rectangle, half-strip, bent strip, quadrant, strip, half-plane, plane, and integer-scale rep-tiling. Five complete profiles occur; this does not assert that Golomb's hierarchy has only five classes in general.

`TilingCore.lean` defines the world as an arbitrary predicate on placed whole tiles. The requirements are D4 congruence, integer junction coordinates, region containment, coverage, and ordinary pairwise cell disjointness. Infinite worlds need not be periodic. For finite regions, every tile has a junction cell inside the region and distinct tiles have distinct junction cells, so the world is automatically finite. Widths and heights in the region-tileability predicates range over all positive integers.

`RectangleRep.lean` defines rep-tiling at a natural linear scale at least two. `CoreBoundaryObstructions.ScaledCross` thickens every original cell into a full square block. `dilation_is_scaled_cross` connects this region with floor-division dilation. Thus the statement is about lattice congruent-copy dissections of integer enlargements, not arbitrary unequal-scale or off-grid Euclidean dissections. Parameter transformations also transform the enlarged target, including the scale-dependent translation needed for reflection.

## Exact theorem-to-file map

All declarations below have prefix `PolyominoFormal.` unless a different full namespace is written. File paths are relative to the extracted `polyominoes` directory.

| Result or interface | Declaration | File |
|---|---|---|
| Complete all-natural-tuple classification | `all_tuples_classified` | `lean/MainClassification.lean` |
| Sorted L classification | `sorted_L_classified` | `lean/MainClassification.lean` |
| General unequal L obstruction: `5 ≤ a`, `3 ≤ b`, `b < a` | `LHalfPlaneUnequal.no_halfplane` | `lean/LHalfPlaneUnequal.lean` |
| Exceptional bounding box 6 by 4, arms `(5,3,0,0)` | `LHalfPlaneFiveThree.no_halfplane` | `lean/LHalfPlaneFiveThree.lean` |
| Complete normalized T profile: `a ≥ c ≥ 1`, `b ≥ 1` | `normalized_T_classified` | `lean/TClassification.lean` |
| T half-plane criterion | `t_halfplane_iff` | `lean/TClassification.lean` |
| T plane criterion | `t_plane_iff` | `lean/TClassification.lean` |
| Exact BS profile of `(4,1,1,0)` | `p4_exact_bs` | `lean/InitialTwoClassification.lean` |
| Exact BS profile of `(5,1,1,0)` | `p5_exact_bs` | `lean/InitialTwoClassification.lean` |
| All `(n,1,1,0)`, with rectangle threshold `n ≤ 3` | `classify_gun` | `lean/GunFamilyClassification.lean` |
| Half-strip threshold for the same family | `gun_half_strip_iff` | `lean/GunFamilyClassification.lean` |
| Rep-tiling threshold for the same family | `gun_rep_iff` | `lean/GunFamilyClassification.lean` |
| Complete four-positive-arm criterion | `classify_positive_cross` | `lean/PositiveCrossClassification.lean` |
| Arbitrary-width half-strip descent | `HalfStripObstruction.no_half_strip` | `lean/HalfStripObstruction.lean` |
| Complete fixed-parameter candidate enumeration | `CornerCertificate.candidate_complete` | `lean/CornerCertificateReplay.lean` |
| Local replay preserving the actual tiling interpretation | `CornerCertificate.replay_step`, `CornerCertificate.replay_leaf` | `lean/CornerCertificateReplay.lean` |
| Parametric replay | `CornerCertificate.replay_affine_step`, `CornerCertificate.replay_affine_leaf` | `lean/CornerCertificateAffineReplay.lean` |

For the normalized T family with stem `b ≥ 2`, the plane criterion is `b = 2` or `c = 1` or `(c = 2 and b = a + 3)`; all these shapes fail half-plane tileability. The source theorem states `b ≤ 2` because its domain includes the separately classified unit-stem branch. For four positive arms, the plane criterion is an opposite unit pair, `(a = 1 and c = 1)` or `(b = 1 and d = 1)`; the other seven capabilities are false.

## Why the finite proof data apply to infinite regions

Finite local certificates are proved as statements about arbitrary exact tiling worlds. Coverage supplies a tile at the chosen query cell; candidate-completeness arguments cover all possible orientations and placements. Disjointness and whole-tile containment justify each elimination. A surviving branch either gives a proved contradiction or produces a successor configuration with its necessary invariants. External search outputs are not assumed.

For the gun family, the corner replay is separated into `n = 4`, `n = 5`, and a symbolic `n ≥ 6` family. The arbitrary-width half-strip argument uses the nonnegative rank `3 * (H - Y) + zeroRank kind`. Every transition decreases that rank, including transitions with no vertical movement. No tested width bound is extrapolated. The L proofs similarly derive boundary configurations from full half-plane worlds before applying their finite obstructions. Tuple normalization and capability assembly are proved within Lean.

## Reproduction

Install Lean **4.33.1**. Extract the ZIP and enter its `polyominoes` directory. Python 3 and Lean are sufficient; the external search solvers, original discovery environment, and local precompiled objects are not needed.

To start with the two formerly unresolved cases:

```sh
python3 src/check_lean.py InitialTwoClassification --jobs 1
```

To verify the entire package:

```sh
python3 src/check_lean.py MainClassification GunFamilyClassification --jobs 1
```

Use `--lean /absolute/path/to/lean` if the required executable is not on the search path. Both compiler concurrency and Lean threads default to one. The last general L components contain substantial generated proof data; compilation is correspondingly resource-intensive. Parallel jobs can increase memory pressure without making verification faster.

The driver creates `.build/lean` and reuses a result only if its source hash, imported compiled-object hashes, compiler-version string, and own compiled-object hash agree with the saved receipt. To force an independent fresh check, specify a previously nonexistent output directory, for example:

```sh
python3 src/check_lean.py MainClassification GunFamilyClassification \
  --jobs 1 --output .build/arxiv-independent
```

A receipt is evidence of a past build, not a substitute for running Lean. The source archive includes no `.olean` proof objects. A successful independent build should conclude `All 538 modules verified.`

## Trust boundary and evidence

The final theorem's recorded axiom report is exactly:

```text
'PolyominoFormal.all_tuples_classified' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

These are standard Lean foundational axioms, so the appropriate claim is **no added axioms or admitted proofs**, not “axiom-free.” The accepted dependency closure contains no `native_decide`, trusted external solver answer, or kernel-bypass mechanism. Arithmetic tactics produce ordinary Lean proof terms. The verification establishes the exact formal predicates; human mathematical review is still responsible for assessing whether those predicates and the exposition express the intended question. It also does not establish priority or novelty in the literature.

The archive includes:

- `MANIFEST.json`: exact source-file hashes and sizes.
- `VERIFICATION.json`: source, compiled-object, dependency, and compiler-version identities from successful isolated builds of the included closure.
- `AXIOMS.txt`: compiler axiom reports, including both declarations in the final entry-point module.
- Root and `lean/` copies of `lean-toolchain`, each pinning Lean 4.33.1.
- `src/check_lean.py`: the dependency build driver.

During manuscript preparation, `research/arxiv_formal_artifact_audit.json` checks the archive's byte hash, source/receipt inventory consistency, selected public theorem declarations and source hashes, pinned toolchains, axiom reports, and the one-worker commands. It deliberately performs no new Lean compilation. The completed accepted build is documented by the packaged receipts and the project's final isolated build log. The broader `research.zip` preserves historical attempts and auxiliary files; it must not be described as if every such file were in the accepted 538-module proof closure.

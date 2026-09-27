# Compact Tate norm limit sequence

Import `ContinuousGroupCohomology.CompactTateNormLimitSequence`
for the full-system compact Hausdorff **additive-group** norm sequence. The
arbitrary-data downstream examples are in
[`CompactTateNormLimitSequenceNative`](../examples/CompactTateNormLimitSequenceNative.lean).
This module builds on this library's finite-row producer
`ContinuousGroupCohomology.CompactFiniteTateNormSequence` and its already
published compact-limit and universal-norm APIs, with direct imports of
`Mathlib.CategoryTheory.Limits.Connected` and
`Mathlib.CategoryTheory.Filtered.Connected`. This destination pins Lean
`v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`
and the official finite-group Tate dependency
`fda003db3d06774f28b47232e8248852ffdbfc0d`.

Fix `{R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}`,
`A : Rep.{u} R G` and `L : LevelCompact A`. Write `J := OpenNormalSubgroup G`,
`I := LevelCompact.group A L (⊤ : OpenSubgroup G)`, `C∞` for
`compactFiniteCoinvariantsLimit A L`, `K∞` for the published
`compactNegativeOneTateLimit A L`, and `Q∞` for the published
`compactZeroTateLimit A L`. An index arrow `S ⟶ T` means `S ≤ T`:
**finer to coarser**. The finite diagrams and natural transformations are
the actual coinvariant, kernel, total-invariant and quotient objects, not
substitute Tate constructions. `fullOpenNormalSubgroup G` explicitly packages
the full group as an open normal subgroup, with
`fullOpenNormalSubgroup_toOpenSubgroup` and `le_fullOpenNormalSubgroup`.
No `Top` instance for `OpenNormalSubgroup G` is assumed or needed; in
particular the implementation does not use a top element of that type.
The full-system carrier is
`universalNormSubmodule A (fullOpenNormalSubgroup G)`.

The compact total-invariant diagram is constant with identity transitions,
but its *limit* is not definitionally `I`.
`compactTotalInvariantsLimitIso A L` is the connected constant-cone iso;
`compactTotalInvariantsLimitIso_hom` records every projection. The induced
maps `compactTateLimitInclusion A L : K∞ ⟶ C∞`,
`compactTateLimitNorm A L : C∞ ⟶ I`, and
`compactTateLimitProjection A L : I ⟶ Q∞` have inspectable component
equations `compactTateLimitInclusion_π`, `compactTateLimitNorm_π` and
`compactTateLimitProjection_π`. Both central pairs are actually exact:
`compactTateLimit_exact_left` and `compactTateLimit_exact_right` transport
the published compact-Hausdorff inverse-limit exactness theorem through
that iso. `compactTateLimitInclusion_injective` and
`compactTateLimitProjection_surjective` supply the endpoints, without a
coinvariant- or kernel-transition surjectivity assumption.

`compactUniversalNormSet A L` intersects the **actual** finite norm ranges
inside `I`. `mem_compactUniversalNormSet_iff` proves equality with membership
in `universalNormSubmodule A (fullOpenNormalSubgroup G)`, using the
finite-coinvariant representative and the relative norm formula, including
the full-open-normal subtype/index comparison.
`compactTateLimitProjection_eq_zero_iff`,
`compactTateLimitProjection_eq_zero_iff_universalNorm` and
`compactTateLimitNorm_range_eq_universalNormSubmodule` identify the limit
kernel and norm range with this universal norm carrier.
`compactUniversalNormClosedSubgroup A L` equips the carrier with precisely
the `L.topology ⊤` topology already used by `I`; its closedness uses the
published universal-norm closedness theorem, not an ambient scalar topology.
`compactUniversalNormClosedSubgroup_eq_ker` records the kernel equality.

`compactTateUniversalNormQuotientIso A L` is an actual
`CompHausAddCommGrp` isomorphism from the quotient of `I` by the closed
universal norms to `Q∞`. Its descended map is continuous, and the compact
quotient-to-Hausdorff continuous bijection supplies a continuous inverse.
`compactTateUniversalNormQuotientIso_mk` states its compatibility on each
quotient representative. `compactZeroTateLimitπ_surjective` makes each
degree-zero limit projection onto.

From a checkout of this library at a reviewed revision, install its pinned
Lean toolchain and fetch the matching precompiled mathlib cache **before**
building the focused producer and the named client target:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build ContinuousGroupCohomology.CompactTateNormLimitSequence
lake build CGCExamples
```

Neither the coefficient ring nor the ambient representation receives a
topology. Coinvariant and kernel transitions **need not be onto**: at
`G = C₂` with trivial `ℤ`-action on `ℤ/2`, the residual coinvariant
deflation from `S = 1` to `T = G` is multiplication by two, hence zero;
at `G = C₄`, `S = 1` and `T = C₂`, the kernel transition likewise vanishes.
Do not apply transition-surjectivity shortcuts to these systems. Restricted
systems (whose top target is `B_top`, not automatically `A^G`), coefficient
naturality, scalar topologies, arithmetic, all-degree Tate theory and source
correspondence are outside this result.

Original design: worker-b Hive Task
`hive-request-c6482d383e26ff324ba537448bc3a3ec237da49a` (UID
`f7a1f3b6-03ae-45da-ab9f-ee553a6d140e`); finite row: worker-b Hive Task
`hive-request-e6d76bdf4dadaad23f990aa082128217880d7321` (UID
`b9bd4a7e-8ee1-4213-9075-d0ebba7ab03e`); full-system implementation:
worker-b Hive Task `hive-request-a3c785c9e3c2568cbdb2e8592ff3c30ed2a0feee`
(UID `8642a473-88cb-463a-beca-1c6e7fc1b695`). This implementation uses
the explicitly packaged full open-normal subgroup, not a generic top-index
shortcut. The destination transfer's review, changed-pin build/private-inclusive
axiom audit, maintainer acceptance and verified release are independent gates;
no source correspondence or coverage follows from this guide.

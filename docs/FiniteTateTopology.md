# Compact exceptional finite Tate stages

Import `ContinuousGroupCohomology` for the whole library, or import
`ContinuousGroupCohomology.FiniteTateTopology`,
`ContinuousGroupCohomology.FiniteCoinvariantDeflation` and
`ContinuousGroupCohomology.ExceptionalTateDeflationTopology` separately.
All declarations below live in `ContinuousGroupCohomology.LevelCompact`.
The [topology client](../examples/FiniteTateTopologyNative.lean),
[coinvariant client](../examples/FiniteCoinvariantDeflationNative.lean) and
[compact deflation client](../examples/ExceptionalTateDeflationTopologyNative.lean)
check direct public imports and representative applications.

## Stages and maps

Let `A : Rep R G`, where `R` is a commutative ring, `G` is a compact
topological group, and `L : LevelCompact A` supplies compact Hausdorff
additive topologies on open-subgroup invariants and continuous transports.
For an open normal `S : OpenNormalSubgroup G`, the continuous
`normFromFiniteCoinvariants A L S` has source
`finiteCoinvariants A (L := L) S` and target the compact additive group
`group A L ⊤` of total invariants. No topology on `R`, finiteness of `A`,
or finiteness of `G` is required for these compact constructions.

| API | Compact Hausdorff additive group / continuous map |
| --- | --- |
| `finiteTateNegOne A L S` | Closed kernel of the finite-coinvariant norm. |
| `finiteTateZero A L S` | Quotient of total invariants by its compact, hence closed, norm range. |
| `finiteTateNegOneι A L S` | Canonical kernel inclusion into finite coinvariants. |
| `finiteTateZeroπ A L S` | Canonical quotient projection from total invariants. |

The public `finiteTateNegOneι_apply`,
`normFromFiniteCoinvariants_finiteTateNegOneι_apply`,
`finiteTateZeroπ_apply` and
`finiteTateZeroπ_normFromFiniteCoinvariants_apply` give the underlying
inclusion, zero norm, quotient representative and zero image of the norm.
For example, with `x : finiteTateNegOne A L S`:

```lean
example : normFromFiniteCoinvariants A L S (finiteTateNegOneι A L S x) = 0 :=
  normFromFiniteCoinvariants_finiteTateNegOneι_apply A L S x
```

## Deflation between levels

For `S ≤ T`, assume
`[Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))]`.
`finiteCoinvariantDeflation A L S T hST` bundles the *actual* algebraic
coinvariant deflation as a continuous compact-group morphism. Its
`finiteCoinvariantDeflation_mk` law evaluates a representative using the
residual `T / S` norm. The common-target norm square is pointwise:

```lean
example (x : finiteCoinvariants A (L := L) S) :
    normFromFiniteCoinvariants A L T
        (finiteCoinvariantDeflation A L S T hST x) =
      normFromFiniteCoinvariants A L S x :=
  normFromFiniteCoinvariants_finiteCoinvariantDeflation A L S T hST x
```

From this square, `finiteTateNegOneDeflation A L S T hST` is the
`CompHausAddCommGrp.kernelMap` and `finiteTateZeroDeflation A L S T hST`
is the `CompHausAddCommGrp.quotientRangeMap`, both with identity on the
total-invariants target. Theorems
`finiteTateNegOneι_finiteTateNegOneDeflation_apply` and
`finiteTateZeroDeflation_finiteTateZeroπ_apply` describe their inclusion
and projection equations. The `*_refl` laws give identity at a level;
`*_comp` gives composition through `S ≤ T ≤ U`, with separate finite
residual-kernel instances for `T / S`, `U / T` and `U / S` (and an equal-level
instance for the reflexive law). This is not an inverse-limit exactness result.

## Additive algebraic comparison

When the ring, group and representation carrier share universe `u` and
`[Fintype (G ⧸ S.toSubgroup)]`, the additive equivalences
`tateCohomologyNegOneAddEquivFiniteTate A L S` and
`tateCohomologyZeroAddEquivFiniteTate A L S` identify algebraic Tate
cohomology of `A.quotientToInvariants S.toSubgroup` in degrees `-1` and `0`
with the two compact **underlying additive groups**. The comparison uses
`algebraicCoinvariantsAddEquivFiniteCoinvariants`,
`finiteNormTargetEquiv`, `finiteNormTargetAddEquivGroup` and the proved
norm-compatibility equation. Public equations for coinvariant representatives,
target values and kernel inclusion enable use without private definitions;
`tateCohomologyZeroAddEquivFiniteTate_cokernelπ` supplies the cokernel
representative equation.

The theorems
`finiteCoinvariantDeflation_algebraicCoinvariantsAddEquivFiniteCoinvariants`,
`tateCohomologyNegOneAddEquivFiniteTate_finiteNegativeOneDeflation` and
`tateCohomologyZeroAddEquivFiniteTate_finiteZeroDeflation` show that the
continuous maps agree under these equivalences with the algebraic finite
coinvariant, degree `-1` and degree `0` deflations, respectively.
The clients include a proper open normal level in a two-element group, a
nonzero representative generator in a finite coefficient example, and
three-level compact-map comparisons. They do not prove nonzero Tate groups.
No topology on the algebraic Tate groups, topological-module identification,
all-degree or completed continuous Tate cohomology is claimed.

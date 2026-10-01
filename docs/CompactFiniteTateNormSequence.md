# Compact finite Tate norm row

Import `ContinuousGroupCohomology.CompactFiniteTateNormSequence`
for a compact Hausdorff additive finite norm row, independent of source
arithmetic. It imports this library's
`ContinuousGroupCohomology.CompactExceptionalTateDiagrams`; its arbitrary-data
client is [`CompactFiniteTateNormSequenceNative`](../examples/CompactFiniteTateNormSequenceNative.lean).
The full-system successor is [CompactTateNormLimitSequence.md](CompactTateNormLimitSequence.md).
The destination checkout pins Lean `v4.34.0-rc2`, mathlib
`e37d88a26f3791ed5a93daa1f949af1021b8d103` and the official
finite-group Tate dependency `fda003db3d06774f28b47232e8248852ffdbfc0d`.

Fix `R : Type u`, `[CommRing R]`, `G : ProfiniteGrp.{u}`,
`A : Rep.{u} R G`, and `L : LevelCompact A`. For an open normal subgroup `S`
put `C_S := finiteCoinvariants A (L := L) S` and
`I := LevelCompact.group A L (⊤ : OpenSubgroup G)`. All groups in this row
carry the **chosen compact Hausdorff additive topology** from `L`, not a new
topology on the ambient coefficient representation or ring. An arrow `S ⟶ T`
means `S ≤ T`, finer to coarser. The map `C_S ⟶ C_T` is the actual continuous
`finiteCoinvariantDeflation A L S T`, induced by the residual `T/S` norm.
The transition on `I` is **identity**, because the norm square has equality
in the same target `I`.

| Diagram or transformation | Declaration | Component at `S` |
| --- | --- | --- |
| Compact coinvariants | `compactFiniteCoinvariantsDiagram A L` | `C_S` |
| Total invariants | `compactTotalInvariantsDiagram A L` | `I` |
| Kernel inclusion | `compactFiniteTateNegOneInclusion A L` | `finiteTateNegOneι A L S` |
| Finite norm | `compactFiniteTateNorm A L` | `normFromFiniteCoinvariants A L S` |
| Quotient projection | `compactFiniteTateZeroProjection A L` | `finiteTateZeroπ A L S` |

The endpoints are **reused**, not redefined:
`compactFiniteNegativeOneDeflationDiagram A L` has the actual compact kernel
`finiteTateNegOne A L S` of the norm as its component, and
`compactFiniteZeroDeflationDiagram A L` has `finiteTateZero A L S`, the
quotient of `I` by the norm's **closed actual range**. Their transitions are
published kernel/quotient deflations. Naturality uses the published kernel
inclusion, norm, and quotient squares; it adds no replacement object or
surjectivity hypothesis.
The five `@[simp]` component equations are
`compactFiniteCoinvariantsDiagram_obj`, `compactTotalInvariantsDiagram_obj`,
`compactFiniteTateNegOneInclusion_app`, `compactFiniteTateNorm_app` and
`compactFiniteTateZeroProjection_app`. They give a downstream client direct
access to the real stage objects and arrows.

For every `S`, `finiteTateNorm_exact_left A L S` proves
`Function.Exact (finiteTateNegOneι A L S)
(normFromFiniteCoinvariants A L S)` from the kernel subtype.
`finiteTateNorm_exact_right A L S` proves
`Function.Exact (normFromFiniteCoinvariants A L S)
(finiteTateZeroπ A L S)` from the quotient by its closed range.
`finiteTateNegOneι_injective A L S` and
`finiteTateZeroπ_surjective A L S` establish the two endpoints.
`finiteTateZeroDeflation_surjective A L S T hST` follows from projection
surjectivity and the published quotient square; **coinvariant and kernel
deflation need not be surjective**. Thus this leaf asserts the stagewise
additive row `0 → K_S → C_S → I → Q_S → 0`; the separately imported
`CompactTateNormLimitSequence` leaf establishes the full-system exact row,
universal-norm kernel and compact quotient. Neither leaf identifies arbitrary
restricted systems or supplies all-degree/completed or arithmetic Tate theory.

From a checkout of this library at a reviewed revision, install its pinned
Lean toolchain and fetch the matching mathlib cache before building:

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
lake build ContinuousGroupCohomology.CompactFiniteTateNormSequence
lake build CGCExamples
```

The exact hypotheses and implementation are in
[`CompactFiniteTateNormSequence.lean`](../ContinuousGroupCohomology/CompactFiniteTateNormSequence.lean).
Contributor origins are summarized in [attribution](attribution.md).

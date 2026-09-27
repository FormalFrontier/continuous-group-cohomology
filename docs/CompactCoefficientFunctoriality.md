# Compact coefficient and restricted-norm functoriality

Import `ContinuousGroupCohomology` for all three leaves, or import
`ContinuousGroupCohomology.CompactExceptionalTateCoefficientMaps`,
`ContinuousGroupCohomology.CompactExceptionalTateLimitFunctoriality` and
`ContinuousGroupCohomology.RestrictedLevelCompactFunctoriality` separately.
The [compact exceptional Tate guide](FiniteTateTopology.md) describes the
underlying stages, diagrams and limits; the APIs here map *those* objects.

## Compact exceptional Tate coefficients

For a compact topological group `G`, a commutative ring `R` and a morphism
`f : A ⟶ B` of `LevelCompactRep R G`, the levelwise topology on each
`openSubgroupInvariants` is supplied by `A.levelCompact` or `B.levelCompact`.
`LevelCompactRep.groupMap f U` is the continuous map of those actual compact
invariant groups. `finiteCoinvariantsMap f S` is the continuous map of the
compact coinvariants of `G ⧸ S`; `finiteTateNegOneMap f S` and
`finiteTateZeroMap f S` map the closed norm kernel and the quotient by its
range. The maps preserve identities and composition.

`mapInvariants_relativeNorm` proves naturality of relative norms, and
`normFromFiniteCoinvariants_naturality_hom` states the compact norm square:
first map finite coinvariants and then take the target norm, or first take
the source norm and then map the total-invariants group. The
`finiteCoinvariantsMap_deflation`, `finiteTateNegOneMap_deflation` and
`finiteTateZeroMap_deflation` equations commute with finite deflation
`S ≤ T` when the residual subgroup is finite. The
[`CompactExceptionalTateCoefficientMapsNative` client](../examples/CompactExceptionalTateCoefficientMapsNative.lean)
tests the generic maps and squares, plus a nonidentity coefficient morphism
on `ZMod 3` at a proper level of a two-element group. No topology on the
ambient coefficients, the scalar ring or algebraic Tate cohomology is assumed.

## Compact exceptional Tate limits

For `G : ProfiniteGrp.{u}`, `LevelCompactRep.compactFiniteNegativeOneDeflationDiagramFunctor`
and `compactFiniteZeroDeflationDiagramFunctor` map coefficients to the published
covariant compact deflation diagrams in degrees `-1` and `0`. Their components
are the stage maps above. Postcomposition with the categorical limit functor
defines `compactNegativeOneTateLimitFunctor` and `compactZeroTateLimitFunctor`
in `CompHausAddCommGrp`. Their `*_map_π` laws follow from `limit.map_π`;
`compactNegativeOneTateLimitFunctor_map_namedπ` and
`compactZeroTateLimitFunctor_map_namedπ` express the same naturality at the
published named stage projections. The
[`CompactExceptionalTateLimitFunctorialityNative` client](../examples/CompactExceptionalTateLimitFunctorialityNative.lean)
exercises continuous limit maps and both projection squares. This reuses the
existing compact limits; it does not assert surjectivity of projections or
inverse-limit exactness.

## Chosen restricted systems

`RestrictedLevelCompactRep R G` pairs a level-compact representation with a
*chosen* `LevelCompact.RestrictedLevelSystem`. A morphism in this category
must preserve the selected subrepresentation at every open normal level;
the faithful `forget` functor retains its underlying level-compact map.
`fullFunctor` and `universalNormFunctor` supply canonical morphisms for every
level-compact coefficient map: universal-norm membership transports via the
relative-norm naturality equation, with no extra preservation hypothesis.

For any genuine preserving morphism, `coefficientMap f U` is linear and
continuous for the selected inherited level topologies. The continuous
`groupMap f U` maps the actual selected compact groups.
`groupMap_relativeNorm` is the compact norm square from the selected
`V` group of the source to the selected `U` group of the target.
`restrictedNormDiagram A` uses the actual `relativeNormHom` transition for
each `V ≤ U`; `restrictedNormDiagramMap f` and
`restrictedNormDiagramFunctor` provide natural transformations and a functor
on the category of selected systems. The
[`RestrictedLevelCompactFunctorialityNative` client](../examples/RestrictedLevelCompactFunctorialityNative.lean)
checks arbitrary preserving maps as well as the full and universal-norm
specializations. These diagrams do not imply a comparison with completed
continuous Tate cohomology or homology.

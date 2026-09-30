# Finite stages for discrete continuous resolutions

SPDX-License-Identifier: Apache-2.0

Import `ContinuousGroupCohomology.FiniteStageResolution`.
The public declarations in `ContinuousCohomology` concern the actual native
`TopRep.resolutionX X i` and `resolutionMap`; direct imports are the CGC
resolution-image criterion and compact/discrete factorization and official
`ContinuousGroupCohomology.TopRepUlift` for `TopRep.JointlyContinuous`.

For a `Ring k` with `[TopologicalSpace k]`, a topological group `G`, and
`X : TopRep.{max v w} k G`:

* `discreteTopology_resolutionX X i` assumes `[CompactSpace G]` and
  `[DiscreteTopology X]` and proves each native resolution level discrete;
  it does **not** require a jointly continuous action.
* `exists_common_stage_refinement X N₀ i S hS` assumes only a finite family
  `S` of resolution elements individually satisfying `StageDescends` at some
  stage. It produces `N ≤ N₀` at which every member descends. No compactness,
  discreteness or joint continuity is needed. The seed `N₀` handles `S = ∅`.
* `exists_openNormal_stage_descends X i a` additionally assumes
  `[CompactSpace G]`, `[DiscreteTopology X]` and
  `[TopRep.JointlyContinuous X]` and supplies `N : OpenNormalSubgroup G` with
  `StageDescends X N i a`.
* `exists_openNormal_resolution_lift X i a` has the same hypotheses and gives
  `N` and `b : TopRep.resolutionX
  (TopRep.quotientInvariants N.toSubgroup X) i` with
  `(resolutionMap (openNormalQuotientHom N)
  (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom b = a`.

The discrete successor level is the compact-open space
`C(G, resolutionX X i)`, discrete by the compact/discrete-map theorem.
At level zero, the orbit map is continuous by joint continuity of the
**original** action. The stabilizer of `a` is clopen (not merely an open
neighborhood), contains 1 and hence contains an open normal subgroup. At each
successor, the outer continuous map has finite range in a discrete target.
The existing factorization theorem produces an outer right-coset stage `N₀`;
finite infima with recursive witnesses for **every range value** refine it.
The predecessor's antitone lemma handles both recursive and outer conditions,
and its image iff produces the native lift. Compactness and openness also make
`G ⧸ N.toSubgroup` finite by mathlib's `Subgroup.quotient_finite_of_isOpen`;
no finite-quotient wrapper is needed. No continuity of the coinduced actions
or global topology instance is assumed.

The ordinary-import
`examples.FiniteStageResolutionNative`
client applies the result over arbitrary `Ring k` and compact `G` at levels
0, 1 and 3 and tests both empty and singleton seeded refinement. Its discrete
integer representation of the finite group `Units ℤ` has genuine sign action:
the orbit cochain takes distinct values at 1 and -1, and its nonzero value at
-1 has an actual quotient-invariant resolution-image witness. The predecessor
client's right-constant nonfixed counterexample remains unchanged. Native
degree-`n` homogeneous cochains use resolution level `n+1`; this leaf does
not package invariant cochains, cocycles, unique lifts, cohomology, torsion,
a uniform stage for all terms, filtered diagrams or source correspondence.

See [attribution](attribution.md) for contributor lineage and rights scope.

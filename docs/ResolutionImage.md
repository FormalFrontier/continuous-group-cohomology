# Images of continuous resolutions over open normal quotients

SPDX-License-Identifier: Apache-2.0

Import `ContinuousGroupCohomology.ResolutionImage`.
For any `Ring k` with a topological space on `k`, any topological group `G`,
`X : TopRep.{max v w} k G`, and `N : OpenNormalSubgroup G`, the namespace
`ContinuousCohomology` provides:

* `openNormalQuotientHom N : G →ₜ* G ⧸ N.toSubgroup`, the continuous quotient map.
* `StageDescends X N i a`: at level zero, `a` belongs to the actual submodule
  `(X.ρ.restrict N.toSubgroup.subtype).invariants`; at every successor level,
  each value recursively descends and the outer map is constant under right
  multiplication by elements of `N`. The simp lemmas `stageDescends_zero` and
  `stageDescends_succ` expose these clauses.
* `stageDescends_antitone X h i a`: when `h : N ≤ M`, an `M`-descending term
  descends for `N`.
* `stageDescends_iff_exists_lift X N i a`: descent is equivalent to the existence
  of `b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) i`
  with `(resolutionMap (openNormalQuotientHom N)
  (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom b = a`. This is an
  actual native image criterion, not a lift to an artificial coefficient subtype.

Direct imports are the CGC quotient-invariants representation, mathlib's
native continuous-cohomology functoriality, and mathlib's open subgroups. No
`CommRing`, compactness, discrete coefficients, separated coefficient space,
jointly continuous action, or splitting of the invariant inclusion is needed.
The proof is inductive: at the bottom lift into the invariant submodule; at
successor levels lift the values at chosen quotient representatives. Equality
of right cosets identifies the chosen value with the original cochain at every
group element. Openness makes `G ⧸ N` discrete, so the chosen map is continuous
even when choosing preimages is not continuous on the original image. This
pointwise argument must not be generalized to nonopen normal subgroups.

The ordinary-import `examples.ResolutionImageNative`
client checks levels 0, 1 and 3, refinement, and a nontrivial action of the
two-element group `Units ℤ` on discrete `ℤ` by signs. Its right-constant level-1
map with constant value `1` does not lift when `N` is the whole group because
that bottom value is not invariant. Right constancy alone is insufficient.
These clients reside in `examples.FiniteStageResolutionNative`; the
`examples.ResolutionImageNative` entrypoint imports that module and the
production API.

This leaf does not assert the existence of an appropriate `N` for a given
cochain; it provides no invariant-cochain or cocycle lift, uniqueness, compact
finite-tree refinement, torsion, transitions, filtered colimits, cohomology
injection, source correspondence or coverage. Native degree-`n` homogeneous
cochains use resolution level `n+1`; that later step is not supplied here.

See [attribution](attribution.md) for contributor lineage and rights scope.

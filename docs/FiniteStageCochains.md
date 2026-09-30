# Homogeneous cochains over one open-normal quotient

Import `ContinuousGroupCohomology.FiniteStageCochains`.
For a `Ring k` with a topology, a compact topological group `G`, and a
representation `X : TopRep.{max v w} k G` whose carrier is discrete and whose
action is jointly continuous, the theorem
`ContinuousCohomology.exists_openNormal_quotient_cochain_lift X n σ`
produces an open normal subgroup `N` and a degree-`n` **native homogeneous
cochain** `τ` for `G ⧸ N` with coefficients in the actual quotient
representation `TopRep.quotientInvariants N.toSubgroup X`. The actual
`cochainsMap` induced by `openNormalQuotientHom N` and
`TopRep.quotientInvariantsIncl N.toSubgroup X` maps `τ` to `σ`.

Degree `n` cochains are invariant elements of `TopRep.resolutionX X (n + 1)`;
the finite-stage resolution theorem provides a lift at exactly that level.
Surjectivity of the quotient map and injectivity of the invariant-subtype
inclusion make the resolution map injective. Equivariance then reflects the
original cochain's invariance to the lifted resolution element. No continuous
inverse or joint continuity on higher coinduced representations is assumed.

If the differential of `σ` in native degree `n + 1` is zero,
`ContinuousCohomology.exists_openNormal_quotient_closed_cochain_lift X n σ hσ`
returns the **same-stage** image witness and proves its differential is zero.
This follows from the existing `cochainsMap_d_eq_zero_iff`; the reflected
differential is in degree `n + 1` and uses resolution level `n + 2`.
The theorem supplies a closed-cochain equation, not a separately packaged
`cocyclesMap` witness.

The ordinary-import client
`examples.FiniteStageCochainsNative`
tests generic degrees zero and two, differential-zero descent and a nonzero,
nonconstant sign-action invariant degree-zero cochain over discrete integers.
Its sign example does not assert the cochain is closed.

Neither result supplies a uniform stage for all cochains, boundary lifting,
injectivity or surjectivity on cohomology classes, torsion, a filtered colimit
description, or source-specific coverage. The previous finite-stage resolution
and injection results remain independent reusable prerequisites.

See [attribution](attribution.md) for contributor lineage and rights scope.

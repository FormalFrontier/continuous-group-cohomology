<!-- SPDX-License-Identifier: Apache-2.0 -->
# Homogeneous cochain lifts below a prescribed open normal subgroup

Import `ContinuousGroupCohomology.SeededCochains`.
For a compact topological group `G`, a discrete `TopRep X` whose action is
jointly continuous, and any topological ring `k`, the theorem
`ContinuousCohomology.exists_quotient_cochain_lift_below X M n σ` finds an open
normal subgroup `N ≤ M` and a homogeneous cochain `τ` on `G ⧸ N` with genuine
`N`-invariant coefficients. The native `cochainsMap` of the quotient homomorphism
and inclusion of the invariant coefficients sends `τ` exactly to `σ`.
The argument works also for `n = 0`; neither the representation, its action,
nor the coefficient ring is required to be nontrivial or finite.

The subgroup `N` depends on the cochain, degree and prescribed `M`. This result
does not provide a single subgroup for all cochains or a class-level lift,
closed-cochain lift, finite-stage transition, or colimit.

The proof refines the existing native `FiniteStageCochains` lift and uses the
quotient-invariant resolution; see [attribution](attribution.md) for contributors.

The original contributors and upstream results are credited in
[attribution](attribution.md).

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.SeededCochains

/-!
# Ordinary-import client for seeded cochain descent

The cochain, its degree and the prescribed open normal subgroup are all arbitrary.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
    [TopRep.JointlyContinuous X]

/-- Refine any stage while preserving the exact native inflation equation. -/
private theorem cochain_descends_below (M : OpenNormalSubgroup G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains X).X n) :
    ∃ (N : OpenNormalSubgroup G), N ≤ M ∧
      ∃ (τ : (TopRep.homogeneousCochains
        (TopRep.quotientInvariants N.toSubgroup X)).X n),
        ((ContinuousCohomology.cochainsMap
          (ContinuousCohomology.openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n) τ = σ :=
  ContinuousCohomology.exists_quotient_cochain_lift_below X M n σ

end CGCExamples.ContinuousCohomology

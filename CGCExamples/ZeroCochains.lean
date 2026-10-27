/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.DegreeOne

/-!
# Degree-zero cochain maps

The continuous linear equivalence and topological-module isomorphism agree on
cochains and on inverse images. Mixed applications satisfy the inverse identities.
-/

@[expose] public section

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w, u, v} k G) [TopRep.JointlyContinuous X]

example (σ : (TopRep.homogeneousCochains.{u, v, w} X).X 0) :
    cochainsZeroEquiv.{u, v, w} X σ = (cochainsZeroIso.{u, v, w} X).hom.hom σ := by
  rw [@cochainsZeroEquiv_apply.{u, v, w} k _ _ G _ _ _ X _ σ,
    @cochainsZeroIso_hom_apply.{u, v, w} k _ _ G _ _ _ X _ σ]

example (x : X) :
    cochainsZeroEquiv.{u, v, w} X ((cochainsZeroIso.{u, v, w} X).inv.hom x) = x ∧
      (cochainsZeroIso.{u, v, w} X).hom.hom ((cochainsZeroEquiv.{u, v, w} X).symm x) = x := by
  constructor <;> simp

example (x : X) (g : G) :
    ((cochainsZeroEquiv.{u, v, w} X).symm x).1 g =
      ((cochainsZeroIso.{u, v, w} X).inv.hom x).1 g := by
  rw [@cochainsZeroEquiv_symm_apply.{u, v, w} k _ _ G _ _ _ X _ x g,
    @cochainsZeroIso_inv_apply.{u, v, w} k _ _ G _ _ _ X _ x g]

end ContinuousCohomology

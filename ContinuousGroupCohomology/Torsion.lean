/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Corestriction
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in continuous cohomology of compact groups in degree one

For a compact topological group acting jointly continuously on a discrete module
over a topologized ring (in particular an integral representation), each degree-one
continuous cohomology class has finite additive order.
The index annihilating a class depends on its crossed-cocycle representative;
neither the coefficients nor the whole cohomology group have a fixed exponent here.
-/

set_option autoImplicit false

public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {G : Type v} [Group G] [TopologicalSpace G]
variable {k : Type u} [Ring k] [TopologicalSpace k]
variable (X : TopRep.{max v w} k G)

/-- A continuous crossed homomorphism vanishes at the identity. -/
@[simp]
theorem continuousCrossedHom_apply_one (f : continuousCrossedHom X) : f.1 (1 : G) = 0 := by
  have hf := f.2 (1 : G) 1
  have hf' : f.1 (1 : G) + 0 = f.1 1 + f.1 1 := by simpa using hf
  exact (add_left_cancel hf').symm

variable [IsTopologicalGroup G] [DiscreteTopology X]

/-- The open subgroup on which a continuous crossed homomorphism vanishes.
It is not required to be normal. -/
def zeroOpenSubgroup (f : continuousCrossedHom X) : OpenSubgroup G where
  carrier := {g | f.1 g = 0}
  one_mem' := continuousCrossedHom_apply_one X f
  mul_mem' := by
    intro g h hg hh
    change f.1 g = 0 at hg
    change f.1 h = 0 at hh
    change f.1 (g * h) = 0
    rw [f.2 g h, hh, map_zero, zero_add, hg]
  inv_mem' := by
    intro g hg
    change f.1 g = 0 at hg
    change f.1 g⁻¹ = 0
    have hf := f.2 g⁻¹ g
    simpa only [inv_mul_cancel, hg, map_zero, zero_add,
      continuousCrossedHom_apply_one X f] using hf.symm
  isOpen' := by
    change IsOpen (f.1 ⁻¹' {0})
    exact (isOpen_discrete {0}).preimage f.1.continuous

/-- The zero-fibre subgroup has finite index when the acting group is compact. -/
theorem zeroOpenSubgroup_finiteIndex [CompactSpace G] (f : continuousCrossedHom X) :
    (zeroOpenSubgroup X f).toSubgroup.FiniteIndex := by
  let H := zeroOpenSubgroup X f
  let _ : Finite (G ⧸ H.toSubgroup) :=
    H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  exact Subgroup.finiteIndex_of_finite_quotient

/-- The index of the zero-fibre subgroup annihilates a crossed-cocycle class. -/
theorem zeroOpenSubgroup_index_nsmul [TopRep.JointlyContinuous X]
    [CompactSpace G] (f : continuousCrossedHom X) :
    (zeroOpenSubgroup X f).toSubgroup.index • (principalCocycles X).mkQ f = 0 := by
  let H := zeroOpenSubgroup X f
  let _ : H.toSubgroup.FiniteIndex := zeroOpenSubgroup_finiteIndex X f
  have hzero : CorestrictionTransversal.crossedRestrict X H f = 0 := by
    ext h
    exact h.2
  have hrestr : CorestrictionTransversal.crossedQuotientRestrict X H
      ((principalCocycles X).mkQ f) = 0 := by
    rw [CorestrictionTransversal.crossedQuotientRestrict_mk, hzero, map_zero]
  have htransfer := CorestrictionTransversal.transferQuotient_comp_restrict
    X H (default : H.toSubgroup.RightTransversal)
  have h := DFunLike.congr_fun htransfer ((principalCocycles X).mkQ f)
  change H.toSubgroup.index • (principalCocycles X).mkQ f = 0
  simpa only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, hrestr, map_zero] using h.symm

/-- Continuous degree-one cohomology of a compact group with discrete coefficients
is torsion, without any torsion assumption on the coefficients or the action. -/
theorem isAddTorsion_degreeOne [TopRep.JointlyContinuous X] [CompactSpace G] :
    IsAddTorsion (continuousCohomology 1 X) := by
  let _ : LocallyCompactSpace G := by
    refine ⟨fun g s hs => ?_⟩
    obtain ⟨t, ht, htclosed, hts⟩ := exists_mem_nhds_isClosed_subset hs
    exact ⟨t, ht, hts, htclosed.isCompact⟩
  intro y
  let z := (degreeOneIso X).inv y
  obtain ⟨f, hf⟩ := (principalCocycles X).mkQ_surjective z
  let H := zeroOpenSubgroup X f
  have hn : 0 < H.toSubgroup.index := Nat.pos_of_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := H.toSubgroup))
  apply (isOfFinAddOrder_iff_nsmul_eq_zero).2
  refine ⟨H.toSubgroup.index, hn, ?_⟩
  have hz := zeroOpenSubgroup_index_nsmul X f
  have hy : (degreeOneIso X).hom ((principalCocycles X).mkQ f) = y := by
    rw [hf]
    change (degreeOneIso X).hom ((degreeOneIso X).inv y) = y
    exact congrArg (fun t => t y) (Iso.inv_hom_id (degreeOneIso X))
  rw [← hy, ← map_nsmul, hz, map_zero]

end ContinuousCohomology

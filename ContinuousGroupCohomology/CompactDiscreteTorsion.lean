module

public import ContinuousGroupCohomology.FiniteStageCochains
public import ContinuousGroupCohomology.FiniteAveraging

set_option warningAsError true

/-!
# Finite-stage classes and positive-degree torsion

Every native continuous-cohomology class of a compact topological group with a
discrete, jointly continuous representation descends from an open-normal quotient
with its genuine invariant coefficient representation. In positive degree, each
class is annihilated by the order of one such finite quotient. The quotient and
its order may depend on the class.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G) [CompactSpace G] [DiscreteTopology X]
  [TopRep.JointlyContinuous X]

/-- Every native cohomology class comes from the actual quotient-invariant
representation at some open-normal stage. The group quotient map goes from `G`
to `G ⧸ N`, while its cohomology map goes from the quotient back to `G`. -/
theorem exists_openNormal_quotient_class_lift (n : ℕ) (a : continuousCohomology n X) :
    ∃ (N : OpenNormalSubgroup G)
      (b : continuousCohomology n (TopRep.quotientInvariants N.toSubgroup X)),
        (map (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom b = a := by
  obtain ⟨z, rfl⟩ := π_surjective X n a
  let C := TopRep.homogeneousCochains X
  let σ : C.X n := (C.iCycles n).hom z
  have hσ : C.d n (n + 1) σ = 0 := by
    change ((C.iCycles n ≫ C.d n (n + 1)).hom z) = 0
    rw [C.iCycles_d]
    rfl
  obtain ⟨N, τ, hτ, hclosed⟩ :=
    exists_openNormal_quotient_closed_cochain_lift X n σ hσ
  let Y := TopRep.quotientInvariants N.toSubgroup X
  let D := TopRep.homogeneousCochains Y
  let f := (D.sc n).g
  let fork := KernelFork.ofι (TopModuleCat.kerι f) (TopModuleCat.kerι_comp f)
  let e : TopModuleCat.ker f ≅ D.cycles n :=
    (D.sc n).isoCyclesOfIsLimit (kf := fork) (TopModuleCat.isLimitKer f)
  have hτf : f τ = 0 := by
    change D.d n ((ComplexShape.up ℕ).next n) τ = 0
    rw [CochainComplex.next ℕ n]
    exact hclosed
  let zτ : cocycles Y n := e.hom.hom
    (⟨τ, hτf⟩ : TopModuleCat.ker f)
  have hzτ : (D.iCycles n).hom zτ = τ := by
    change (e.hom ≫ D.iCycles n).hom
      (⟨τ, hτf⟩ : TopModuleCat.ker f) = τ
    have he : e.hom ≫ D.iCycles n = TopModuleCat.kerι f :=
      (D.sc n).isoCyclesOfIsLimit_hom_iCycles (TopModuleCat.isLimitKer f)
    rw [he]
    rfl
  have hz : (cocyclesMap (openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom zτ = z := by
    let : PreservesLimitsOfShape WalkingCospan (forget (TopModuleCat k)) := by
      rw [← HasForget₂.forget_comp (C := TopModuleCat k) (D := TopCat)]
      infer_instance
    apply (ConcreteCategory.injective_of_mono_of_preservesPullback (C.iCycles n))
    calc
      (C.iCycles n).hom ((cocyclesMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom zτ) =
          ((cochainsMap (openNormalQuotientHom N)
            (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n).hom
            ((D.iCycles n).hom zτ) := by
              have h := HomologicalComplex.cyclesMap_i
                (cochainsMap (openNormalQuotientHom N)
                  (TopRep.quotientInvariantsIncl N.toSubgroup X)) n
              exact congrArg (fun f : cocycles Y n ⟶ C.X n => f.hom zτ) h
      _ = σ := by rw [hzτ]; exact hτ
      _ = (C.iCycles n).hom z := rfl
  refine ⟨N, (π Y n).hom zτ, ?_⟩
  have h := congrArg (fun f : cocycles Y n ⟶ continuousCohomology n X => f.hom zτ)
    (π_map (openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X) n)
  simpa only [ConcreteCategory.comp_apply, hz] using h

/-- Every positive-degree class is killed by the order of a class-dependent
finite open-normal quotient, with arbitrary ring and discrete coefficients. -/
theorem exists_openNormal_quotient_card_nsmul_eq_zero (n : ℕ)
    (a : continuousCohomology (n + 1) X) :
    ∃ N : OpenNormalSubgroup G, Nat.card (G ⧸ N.toSubgroup) • a = 0 := by
  obtain ⟨N, b, hb⟩ := exists_openNormal_quotient_class_lift X (n + 1) a
  have : Finite (G ⧸ N.toSubgroup) :=
    N.toSubgroup.quotient_finite_of_isOpen N.isOpen
  refine ⟨N, ?_⟩
  rw [← hb, ← map_nsmul, finiteGroup_card_nsmul
    (TopRep.quotientInvariants N.toSubgroup X) n b, map_zero]

/-- Positive-degree continuous cohomology with discrete jointly continuous
coefficients over a compact group is additively torsion. -/
theorem compactDiscrete_isAddTorsion (n : ℕ) :
    IsAddTorsion (continuousCohomology (n + 1) X) := by
  intro a
  obtain ⟨N, hN⟩ := exists_openNormal_quotient_card_nsmul_eq_zero X n a
  have : Finite (G ⧸ N.toSubgroup) :=
    N.toSubgroup.quotient_finite_of_isOpen N.isOpen
  exact (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨Nat.card (G ⧸ N.toSubgroup),
    Nat.card_pos, hN⟩

end ContinuousCohomology

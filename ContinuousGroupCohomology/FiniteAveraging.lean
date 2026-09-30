module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite-group averaging in native continuous cohomology

For a finite topological group, summing a coinduced continuous function is an
equivariant continuous linear map. Its unit and naturality equations contract
multiplication by the group order in strictly positive degrees of the native
homogeneous cochain complex. Degree zero is not contracted.
-/

set_option autoImplicit false

public section

open CategoryTheory CategoryTheory.Limits ContRepresentation

universe u v w

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype G]

/-- Sum the values of a coinduced continuous representation over the finite group. -/
def finiteSumCoind (Y : TopRep.{max v w} k G) : TopRep.coind₁ Y ⟶ Y :=
  ofHom {
    toContinuousLinearMap := ∑ t : G, ContinuousMap.evalCLM (R := k) (M := Y) t
    isIntertwining' g := by
      ext f
      simp only [ContinuousLinearMap.comp_apply, sum_apply,
        ContinuousMap.evalCLM_apply]
      change (∑ t : G, Y.ρ g (f (g⁻¹ * t))) = Y.ρ g (∑ t : G, f t)
      rw [← map_sum]
      congr 1
      change (∑ t : G, f ((Equiv.mulLeft g⁻¹) t)) = ∑ t : G, f t
      exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun t : G => f t)
  }

@[simp]
theorem finiteSumCoind_apply (Y : TopRep.{max v w} k G) (f : TopRep.coind₁ Y) :
    (finiteSumCoind Y).hom f = ∑ t : G, f t := by
  change (∑ t : G, ContinuousMap.evalCLM (R := k) (M := Y) t) f = _
  simp

/-- Averaging after constant inclusion is multiplication by the group order. -/
theorem coind₁ι_comp_finiteSumCoind (Y : TopRep.{max v w} k G) :
    ofHom Y.ρ.coind₁ι ≫ finiteSumCoind Y = Fintype.card G • (𝟙 Y) := by
  ext y
  simp only [hom_comp, hom_ofHom, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply]
  change (finiteSumCoind Y).hom (Y.ρ.coind₁ι y) = (Fintype.card G • 𝟙 Y).hom y
  rw [finiteSumCoind_apply]
  change (∑ _t : G, y) = Fintype.card G • y
  simp

/-- Averaging commutes with every equivariant continuous linear map. -/
theorem coind₁Map_comp_finiteSumCoind {Y Z : TopRep.{max v w} k G} (f : Y ⟶ Z) :
    (coind₁Functor k G).map f ≫ finiteSumCoind Z = finiteSumCoind Y ≫ f := by
  ext q
  simp only [hom_comp, ContIntertwiningMap.toContinuousLinearMap_comp,
    ContinuousLinearMap.comp_apply]
  change (finiteSumCoind Z).hom ((coind₁Functor k G).map f |>.hom q) =
    f.hom ((finiteSumCoind Y).hom q)
  rw [finiteSumCoind_apply, finiteSumCoind_apply]
  change (∑ t : G, f.hom (q t)) = f.hom (∑ t : G, q t)
  exact (map_sum f.hom.toContinuousLinearMap _ _).symm

/-- Multiplication by the group order is nullhomotopic on positive resolution terms. -/
theorem finiteSumCoind_d_add_d_finiteSumCoind (X : TopRep.{max v w} k G) (n : ℕ) :
    finiteSumCoind (resolutionX X n) ≫ d X n +
      d X (n + 1) ≫ finiteSumCoind (resolutionX X (n + 1)) =
      Fintype.card G • (𝟙 (resolutionX X (n + 1))) := by
  rw [d_succ, Preadditive.sub_comp,
    coind₁Map_comp_finiteSumCoind, coind₁ι_comp_finiteSumCoind]
  abel

/-- Averaging on the invariant, shifted homogeneous cochain complex. -/
def finiteSumCochain (X : TopRep.{max v w} k G) (n : ℕ) :
    (homogeneousCochains X).X (n + 1) ⟶ (homogeneousCochains X).X n :=
  (invariantsFunctor k G).map (finiteSumCoind (resolutionX X (n + 1)))

/-- The finite-order cochain-homotopy identity, only in strictly positive degree. -/
theorem finiteSumCochain_comp_d_add_d_comp_finiteSumCochain
    (X : TopRep.{max v w} k G) (n : ℕ) :
    finiteSumCochain X n ≫ (homogeneousCochains X).d n (n + 1) +
      (homogeneousCochains X).d (n + 1) (n + 2) ≫ finiteSumCochain X (n + 1) =
      Fintype.card G • (𝟙 ((homogeneousCochains X).X (n + 1))) := by
  rw [finiteSumCochain, finiteSumCochain, homogeneousCochains.d_eq,
    homogeneousCochains.d_eq, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_add, finiteSumCoind_d_add_d_finiteSumCoind,
    Functor.map_nsmul]
  congr 1

end TopRep

namespace TopModuleCat

variable {k : Type u} [Ring k] [TopologicalSpace k]

/-- In topological modules, the homology projection is surjective on underlying
elements: it is an actual cokernel projection followed by an isomorphism.
Categorical epimorphy alone does not imply this assertion. -/
theorem shortComplex_homologyπ_surjective
    (S : ShortComplex (TopModuleCat.{w} k)) :
    Function.Surjective S.homologyπ.hom := by
  let D := S.leftHomologyData
  let e : D.H ≅ TopModuleCat.coker D.f' :=
    IsColimit.coconePointUniqueUpToIso D.hπ' (TopModuleCat.isColimitCoker D.f')
  have heq : D.π ≫ e.hom = TopModuleCat.cokerπ D.f' :=
    IsColimit.comp_coconePointUniqueUpToIso_hom D.hπ'
      (TopModuleCat.isColimitCoker D.f') WalkingParallelPair.one
  have hinj : Function.Injective e.hom.hom :=
    (ConcreteCategory.bijective_of_isIso e.hom).1
  have hD : Function.Surjective D.π.hom := by
    intro a
    obtain ⟨z, hz⟩ := TopModuleCat.cokerπ_surjective D.f' (e.hom.hom a)
    refine ⟨z, hinj ?_⟩
    calc
      e.hom.hom (D.π.hom z) = (D.π ≫ e.hom).hom z := rfl
      _ = (TopModuleCat.cokerπ D.f').hom z := by rw [heq]
      _ = e.hom.hom a := hz
  have hIso : Function.Surjective S.leftHomologyIso.hom.hom :=
    (ConcreteCategory.bijective_of_isIso S.leftHomologyIso.hom).2
  change Function.Surjective S.leftHomologyπ.hom at hD
  intro a
  obtain ⟨b, hb⟩ := hIso a
  obtain ⟨c, hc⟩ := hD b
  refine ⟨c, ?_⟩
  change S.leftHomologyIso.hom.hom (S.leftHomologyπ.hom c) = a
  rw [hc, hb]

end TopModuleCat

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every continuous-cohomology class has a concrete cocycle representative. -/
theorem π_surjective (X : TopRep.{max v w} k G) (n : ℕ) :
    Function.Surjective (π X n).hom :=
  TopModuleCat.shortComplex_homologyπ_surjective ((TopRep.homogeneousCochains X).sc n)

variable [Fintype G]

/-- Multiplication by the group order kills the projection of every positive-degree cocycle. -/
theorem finiteGroup_card_nsmul_π (X : TopRep.{max v w} k G) (n : ℕ) :
    Fintype.card G • π X (n + 1) = 0 := by
  let C := TopRep.homogeneousCochains X
  have hcycle : C.iCycles (n + 1) ≫
      (Fintype.card G • 𝟙 (C.X (n + 1))) =
      (C.iCycles (n + 1) ≫ TopRep.finiteSumCochain X n) ≫
        C.d n (n + 1) := by
    rw [← TopRep.finiteSumCochain_comp_d_add_d_comp_finiteSumCochain X n,
      Preadditive.comp_add]
    change C.iCycles (n + 1) ≫ TopRep.finiteSumCochain X n ≫ C.d n (n + 1) +
        C.iCycles (n + 1) ≫ C.d (n + 1) (n + 2) ≫
          TopRep.finiteSumCochain X (n + 1) =
        (C.iCycles (n + 1) ≫ TopRep.finiteSumCochain X n) ≫ C.d n (n + 1)
    simp only [← Category.assoc, C.iCycles_d, zero_comp, add_zero]
  have hboundary : Fintype.card G • C.iCycles (n + 1) =
      (C.iCycles (n + 1) ≫ TopRep.finiteSumCochain X n) ≫ C.d n (n + 1) := by
    calc
      _ = C.iCycles (n + 1) ≫ (Fintype.card G • 𝟙 (C.X (n + 1))) := by
        rw [Preadditive.comp_nsmul]
        simp
      _ = _ := hcycle
  have hj : (ComplexShape.up ℕ).next (n + 1) = n + 2 := CochainComplex.next ℕ (n + 1)
  have hvanish := C.liftCycles_homologyπ_eq_zero_of_boundary
    (Fintype.card G • C.iCycles (n + 1)) (n + 2) hj
    (C.iCycles (n + 1) ≫ TopRep.finiteSumCochain X n) hboundary
  have hL : C.liftCycles (Fintype.card G • C.iCycles (n + 1)) (n + 2) hj
      (by rw [hboundary, Category.assoc, C.d_comp_d, comp_zero]) =
      Fintype.card G • (𝟙 (C.cycles (n + 1))) := by
    apply (cancel_mono (C.iCycles (n + 1))).mp
    rw [C.liftCycles_i, Preadditive.nsmul_comp]
    simp
  change Fintype.card G • C.homologyπ (n + 1) = 0
  calc
    Fintype.card G • C.homologyπ (n + 1) =
        (Fintype.card G • (𝟙 (C.cycles (n + 1)))) ≫ C.homologyπ (n + 1) := by
      simp
    _ = 0 := by
      rw [← hL]
      exact hvanish

/-- Positive-degree native continuous cohomology of a finite topological group
is annihilated by the order of the group, with arbitrary topological coefficients. -/
theorem fintype_card_nsmul (X : TopRep.{max v w} k G) (n : ℕ)
    (a : continuousCohomology (n + 1) X) : Fintype.card G • a = 0 := by
  obtain ⟨z, rfl⟩ := π_surjective X (n + 1) a
  have h := congrArg
    (fun f : cocycles X (n + 1) ⟶ continuousCohomology (n + 1) X => f.hom z)
    (finiteGroup_card_nsmul_π X n)
  simpa using h

end ContinuousCohomology

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]

/-- For any finite topological group, its order annihilates every positive-degree
continuous cohomology class, with no separation or coefficient restrictions. -/
theorem finiteGroup_card_nsmul (X : TopRep.{max v w} k G) (n : ℕ)
    (a : continuousCohomology (n + 1) X) : Nat.card G • a = 0 :=
  letI : Fintype G := Fintype.ofFinite G
  by simpa only [Nat.card_eq_fintype_card] using fintype_card_nsmul X n a

/-- Positive-degree continuous cohomology of a finite topological group is
additively torsion, without a torsion condition on its coefficients. -/
theorem finiteGroup_isAddTorsion (X : TopRep.{max v w} k G) (n : ℕ) :
    IsAddTorsion (continuousCohomology (n + 1) X) := by
  intro a
  apply (isOfFinAddOrder_iff_nsmul_eq_zero).2
  exact ⟨Nat.card G, Nat.card_pos, finiteGroup_card_nsmul X n a⟩

end ContinuousCohomology

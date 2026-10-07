/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CochainExactness
public import ContinuousGroupCohomology.LowDegreeExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Algebraic long exact sequence of continuous cohomology

For discrete coefficients over a locally compact topological group, a short exact
coefficient sequence induces a degreewise short exact sequence of continuous
homogeneous cochains. Forgetting the topology puts this sequence in the abelian
category of modules. The connecting homomorphism and the three recurring
exactness statements are formulated for the *underlying modules* of the existing
`continuousCohomology` objects. No continuity of the connecting homomorphism is
asserted: continuous cochains and a continuous map on their cohomology are
distinct requirements.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3 and Exercise 1.
* Mathlib's continuous homogeneous cochains, preserved homology, and
  `HomologicalComplex.HomologySequence`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : TopRep.{max v w} k G}

/-- Forgetting topology from the existing complex of continuous homogeneous cochains. -/
noncomputable abbrev moduleCochains (X : TopRep.{max v w} k G) :
    CochainComplex (ModuleCat.{max v w} k) ℕ :=
  ((forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (homogeneousCochains X)

/-- Preservation of homology by the topology-forgetting functor identifies the
homology of the algebraic complex with the underlying module of the existing
continuous cohomology. -/
noncomputable def moduleCohomologyIso (X : TopRep.{max v w} k G) (n : ℕ) :
    (moduleCochains X).homology n ≅
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology n X) :=
  ((homogeneousCochains X).sc n).mapHomologyIso
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k))

/-- The algebraic homology comparison commutes with the existing continuous
cohomology maps. This is the comparison used to transport Mathlib's long exact
sequence to the previously defined continuous cohomology. -/
theorem moduleCohomologyIso_naturality (f : A ⟶ B) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
          (ComplexShape.up ℕ)).map (cochainsMap (ContinuousMonoidHom.id G) f)) n ≫
      (moduleCohomologyIso B n).hom =
    (moduleCohomologyIso A n).hom ≫
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (map (ContinuousMonoidHom.id G) f n) := by
  exact ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ _ n).map
      (cochainsMap (ContinuousMonoidHom.id G) f))
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k))

/-- The coefficient maps induce an algebraic short complex of the original
continuous-cochain complexes, without introducing a second cohomology model. -/
noncomputable def moduleCochainsSequence (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    ShortComplex (CochainComplex (ModuleCat.{max v w} k) ℕ) :=
  let forgetComplex :=
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)
  ShortComplex.mk (forgetComplex.map (cochainsMap (ContinuousMonoidHom.id G) i))
    (forgetComplex.map (cochainsMap (ContinuousMonoidHom.id G) p)) (by
        ext n : 1
        change (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
              ((cochainsMap (ContinuousMonoidHom.id G) i).f n) ≫
            (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
              ((cochainsMap (ContinuousMonoidHom.id G) p).f n) = 0
        rw [← Functor.map_comp, cochainsMap_comp_zero i p hexact n,
          Functor.map_zero])

@[simp]
theorem moduleCochainsSequence_f (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    (moduleCochainsSequence i p hexact).f =
      ((forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (cochainsMap (ContinuousMonoidHom.id G) i) := rfl

@[simp]
theorem moduleCochainsSequence_g (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    (moduleCochainsSequence i p hexact).g =
      ((forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (cochainsMap (ContinuousMonoidHom.id G) p) := rfl

@[simp]
theorem moduleCochainsSequence_X₁ (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    (moduleCochainsSequence i p hexact).X₁ = moduleCochains A := rfl

@[simp]
theorem moduleCochainsSequence_X₃ (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) :
    (moduleCochainsSequence i p hexact).X₃ = moduleCochains C := rfl

/-- Degreewise exactness of the algebraic sequence is precisely the released
continuous-cochain exactness, interpreted in `ModuleCat`. -/
theorem moduleCochainsSequence_shortExact [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (moduleCochainsSequence i p hexact).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have h := cochainsMap_shortExact i p hi hexact hp n
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact ((cochainsMap (ContinuousMonoidHom.id G) i).f n)
        ((cochainsMap (ContinuousMonoidHom.id G) p).f n)
    exact h.2.1
  · change Function.Injective ((cochainsMap (ContinuousMonoidHom.id G) i).f n)
    exact h.1
  · change Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) p).f n)
    exact h.2.2

/-- The algebraic connecting homomorphism for all natural degrees, transported
from Mathlib's short-exact-complex boundary to the underlying modules of the
*existing* continuous cohomology. Its orientation is fixed by `connecting_apply`.
It is not asserted to be a continuous map of topological modules. -/
noncomputable def connecting [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology n C) ⟶
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology (n + 1) A) :=
  (moduleCohomologyIso C n).inv ≫
    (moduleCochainsSequence_shortExact i p hi hexact hp).δ n (n + 1) rfl ≫
      (moduleCohomologyIso A (n + 1)).hom

set_option backward.isDefEq.respectTransparency false in
/-- Computing the new connector through the canonical comparison with the
algebraic cochain complex recovers Mathlib's homology boundary. -/
theorem moduleCohomologyIso_connecting [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    (moduleCohomologyIso C n).hom ≫ connecting i p hi hexact hp n =
      (moduleCochainsSequence_shortExact i p hi hexact hp).δ n (n + 1) rfl ≫
        (moduleCohomologyIso A (n + 1)).hom := by
  simp only [connecting, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- A cocycle class maps to the class of the unique preimage under `i` of the
differential of any cochain lift along `p`; the sign agrees with Mathlib's
`ShortComplex.ShortExact.δ_eq`. In particular no negative is inserted. -/
theorem connecting_apply [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ)
    {T : ModuleCat.{max v w} k} (z : T ⟶ (moduleCochains C).X n)
    (hz : z ≫ (moduleCochains C).d n (n + 1) = 0)
    (b : T ⟶ (moduleCochains B).X n)
    (hb : b ≫ (moduleCochainsSequence i p hexact).g.f n = z)
    (a : T ⟶ (moduleCochains A).X (n + 1))
    (ha : a ≫ (moduleCochainsSequence i p hexact).f.f (n + 1) =
      b ≫ (moduleCochains B).d n (n + 1)) :
    (moduleCochains C).liftCycles z (n + 1) (CochainComplex.next ℕ n) hz ≫
        (moduleCochains C).homologyπ n ≫ (moduleCohomologyIso C n).hom ≫
        connecting i p hi hexact hp n =
      (moduleCochains A).liftCycles a (n + 2)
        ((CochainComplex.next ℕ (n + 1)).trans (by omega)) (by
        have := (moduleCochainsSequence_shortExact i p hi hexact hp).mono_f
        apply (cancel_mono ((moduleCochainsSequence i p hexact).f.f (n + 2))).1
        rw [Category.assoc, ← HomologicalComplex.Hom.comm, ← Category.assoc, ha]
        simp only [zero_comp]
        change (b ≫ (moduleCochains B).d n (n + 1)) ≫
          (moduleCochains B).d (n + 1) (n + 2) = 0
        rw [Category.assoc, (moduleCochains B).d_comp_d, comp_zero]) ≫
        (moduleCochains A).homologyπ (n + 1) ≫
          (moduleCohomologyIso A (n + 1)).hom := by
  have hδ := (moduleCochainsSequence_shortExact i p hi hexact hp).δ_eq
    n (n + 1) rfl z hz b hb a ha (n + 2)
      ((CochainComplex.next ℕ (n + 1)).trans (by omega))
  have hδ' := congrArg
    (fun t : T ⟶ (moduleCochains A).homology (n + 1) =>
      t ≫ (moduleCohomologyIso A (n + 1)).hom) hδ
  simpa only [Category.assoc, moduleCohomologyIso_connecting,
    moduleCochainsSequence_X₁, moduleCochainsSequence_X₃] using hδ'

/-- Exactness at the middle coefficient's cohomology in each degree. -/
theorem exact_map_map [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Exact (map (ContinuousMonoidHom.id G) i n).hom
      (map (ContinuousMonoidHom.id G) p n).hom := by
  let S := moduleCochainsSequence i p hexact
  have hS := moduleCochainsSequence_shortExact i p hi hexact hp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (HomologicalComplex.homologyMap S.f n).hom)
    (f₂₃ := (HomologicalComplex.homologyMap S.g n).hom)
    (g₁₂ := (map (ContinuousMonoidHom.id G) i n).hom.toLinearMap)
    (g₂₃ := (map (ContinuousMonoidHom.id G) p n).hom.toLinearMap)
    (e₁ := (moduleCohomologyIso A n).toLinearEquiv)
    (e₂ := (moduleCohomologyIso B n).toLinearEquiv)
    (e₃ := (moduleCohomologyIso C n).toLinearEquiv)
  · exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_naturality i n).symm
  · exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_naturality p n).symm
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₂ n)

/-- Exactness at the quotient coefficient's cohomology in each degree. -/
theorem exact_map_connecting [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Exact (map (ContinuousMonoidHom.id G) p n).hom
      (connecting i p hi hexact hp n).hom := by
  let S := moduleCochainsSequence i p hexact
  have hS := moduleCochainsSequence_shortExact i p hi hexact hp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (HomologicalComplex.homologyMap S.g n).hom)
    (f₂₃ := (hS.δ n (n + 1) rfl).hom)
    (g₁₂ := (map (ContinuousMonoidHom.id G) p n).hom.toLinearMap)
    (g₂₃ := (connecting i p hi hexact hp n).hom)
    (e₁ := (moduleCohomologyIso B n).toLinearEquiv)
    (e₂ := (moduleCohomologyIso C n).toLinearEquiv)
    (e₃ := (moduleCohomologyIso A (n + 1)).toLinearEquiv)
  · exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_naturality p n).symm
  · change ModuleCat.Hom.hom ((moduleCohomologyIso C n).hom ≫
      connecting i p hi hexact hp n) =
        ModuleCat.Hom.hom (hS.δ n (n + 1) rfl ≫ (moduleCohomologyIso A (n + 1)).hom)
    exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_connecting i p hi hexact hp n)
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₃ n (n + 1) rfl)

/-- Exactness at the kernel coefficient's cohomology one degree higher. -/
theorem exact_connecting_map [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Exact (connecting i p hi hexact hp n).hom
      (map (ContinuousMonoidHom.id G) i (n + 1)).hom := by
  let S := moduleCochainsSequence i p hexact
  have hS := moduleCochainsSequence_shortExact i p hi hexact hp
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (hS.δ n (n + 1) rfl).hom)
    (f₂₃ := (HomologicalComplex.homologyMap S.f (n + 1)).hom)
    (g₁₂ := (connecting i p hi hexact hp n).hom)
    (g₂₃ := (map (ContinuousMonoidHom.id G) i (n + 1)).hom.toLinearMap)
    (e₁ := (moduleCohomologyIso C n).toLinearEquiv)
    (e₂ := (moduleCohomologyIso A (n + 1)).toLinearEquiv)
    (e₃ := (moduleCohomologyIso B (n + 1)).toLinearEquiv)
  · change ModuleCat.Hom.hom ((moduleCohomologyIso C n).hom ≫
      connecting i p hi hexact hp n) =
        ModuleCat.Hom.hom (hS.δ n (n + 1) rfl ≫ (moduleCohomologyIso A (n + 1)).hom)
    exact congrArg ModuleCat.Hom.hom (moduleCohomologyIso_connecting i p hi hexact hp n)
  · exact congrArg ModuleCat.Hom.hom
      (moduleCohomologyIso_naturality i (n + 1)).symm
  · exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (hS.homology_exact₁ n (n + 1) rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem moduleCohomologyIso_homologyπ
    (X : TopRep.{max v w} k G) (n : ℕ) :
    (moduleCochains X).homologyπ n ≫ (moduleCohomologyIso X n).hom =
      (((homogeneousCochains X).sc n).mapCyclesIso
        (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k))).hom ≫
        (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
          ((homogeneousCochains X).homologyπ n) := by
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  let S := (homogeneousCochains X).sc n
  let h := S.homologyData.left
  change (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, (h.map F).homologyπ_comp_homologyIso_hom]
  change (h.map F).cyclesIso.hom ≫ (h.map F).π ≫ F.map h.homologyIso.inv =
    (h.map F).cyclesIso.hom ≫ F.map h.cyclesIso.inv ≫ F.map S.homologyπ
  rw [h.map_π]
  simp only [← F.map_comp, h.π_comp_homologyIso_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem moduleCohomologyIso_liftCycles
    (X : TopRep.{max v w} k G) (n : ℕ)
    {T : TopModuleCat.{max v w} k}
    (z : T ⟶ (homogeneousCochains X).cycles n) :
    (moduleCochains X).liftCycles
        ((forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
          (z ≫ (homogeneousCochains X).iCycles n)) (n + 1) (by simp) (by
        change (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
          (z ≫ (homogeneousCochains X).iCycles n) ≫
            (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
              ((homogeneousCochains X).d n (n + 1)) = 0
        rw [← Functor.map_comp, Category.assoc,
          HomologicalComplex.iCycles_d, comp_zero, Functor.map_zero]) ≫
        (moduleCochains X).homologyπ n ≫ (moduleCohomologyIso X n).hom =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (z ≫ (homogeneousCochains X).homologyπ n) := by
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  let K := homogeneousCochains X
  have hcycle : F.map (z ≫ K.iCycles n) ≫ (moduleCochains X).d n (n + 1) = 0 := by
    change F.map (z ≫ K.iCycles n) ≫ F.map (K.d n (n + 1)) = 0
    rw [← F.map_comp, Category.assoc, HomologicalComplex.iCycles_d,
      comp_zero, Functor.map_zero]
  have hlift : (moduleCochains X).liftCycles (F.map (z ≫ K.iCycles n)) (n + 1)
      (by simp) hcycle ≫ ((K.sc n).mapCyclesIso F).hom = F.map z := by
    apply (cancel_mono (F.map (K.iCycles n))).1
    have hi : ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n) =
        (moduleCochains X).iCycles n :=
      ShortComplex.mapCyclesIso_hom_iCycles (K.sc n) F
    calc
      _ = (moduleCochains X).liftCycles (F.map (z ≫ K.iCycles n)) (n + 1)
          (by simp) hcycle ≫
          (((K.sc n).mapCyclesIso F).hom ≫ F.map (K.iCycles n)) := by
            simp only [Category.assoc]
      _ = (moduleCochains X).liftCycles (F.map (z ≫ K.iCycles n)) (n + 1)
          (by simp) hcycle ≫ (moduleCochains X).iCycles n := by rw [hi]
      _ = F.map (z ≫ K.iCycles n) :=
        (moduleCochains X).liftCycles_i (F.map (z ≫ K.iCycles n)) (n + 1)
          (by simp) hcycle
  have hπ := congrArg
    (fun f => (moduleCochains X).liftCycles (F.map (z ≫ K.iCycles n)) (n + 1)
      (by simp) hcycle ≫ f) (moduleCohomologyIso_homologyπ X n)
  calc
    _ = ((moduleCochains X).liftCycles (F.map (z ≫ K.iCycles n)) (n + 1)
        (by simp) hcycle ≫ ((K.sc n).mapCyclesIso F).hom) ≫
          F.map (K.homologyπ n) := by simpa only [Category.assoc] using hπ
    _ = F.map z ≫ F.map (K.homologyπ n) := by rw [hlift]
    _ = F.map (z ≫ K.homologyπ n) := (F.map_comp _ _).symm

omit [IsTopologicalGroup G] in
private theorem jointlyContinuous_of_surjective_discrete
    [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (p : B ⟶ C) (hp : Function.Surjective p.hom) :
    TopRep.JointlyContinuous C := by
  constructor
  rw [continuous_prod_of_discrete_right]
  intro c
  obtain ⟨b, rfl⟩ := hp c
  have hb : Continuous (fun g : G => B.ρ g b) :=
    (TopRep.JointlyContinuous.continuous_action (X := B)).comp
      (continuous_id.prodMk continuous_const)
  exact (p.hom.continuous.comp hb).congr
    (fun g => TopRep.hom_comm_apply p g b)

set_option backward.isDefEq.respectTransparency false in
private theorem cochainsZeroIso_inv_naturality
    [TopRep.JointlyContinuous B] [TopRep.JointlyContinuous C]
    (p : B ⟶ C) :
    (cochainsZeroIso B).inv ≫ (cochainsMap (ContinuousMonoidHom.id G) p).f 0 =
      TopModuleCat.ofHom p.hom.toContinuousLinearMap ≫ (cochainsZeroIso C).inv := by
  apply (cancel_epi (cochainsZeroIso B).hom).1
  apply (cancel_mono (cochainsZeroIso C).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  ext σ
  have hmap := cochainsMap_resolutionEval p 0 σ (fun _ => (1 : G))
  change (cochainsZeroIso C).hom.hom
    ((cochainsMap (ContinuousMonoidHom.id G) p).f 0 σ) =
      p.hom ((cochainsZeroIso B).hom.hom σ)
  rw [cochainsZeroIso_hom_apply, cochainsZeroIso_hom_apply]
  simpa only [TopRep.resolutionEval_succ, TopRep.resolutionEval_zero] using hmap

set_option backward.isDefEq.respectTransparency false in
private theorem zeroIso_inv_iCycles_eq_zeroCochain
    (X : TopRep.{max v w} k G) [TopRep.JointlyContinuous X] :
    (zeroIso X).inv ≫ (homogeneousCochains X).isoHomologyπ₀.inv ≫
        (homogeneousCochains X).iCycles 0 =
      TopModuleCat.ofHom (Submodule.subtypeL X.ρ.invariants) ≫
        (cochainsZeroIso X).inv := by
  have hι : (cocycles₀Iso X).hom ≫
      TopModuleCat.kerι ((homogeneousCochains X).d 0 1) =
        (homogeneousCochains X).iCycles 0 := by
    ext σ
    rfl
  rw [zeroIso, Iso.trans_inv, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← hι]
  simp only [Iso.inv_hom_id_assoc]
  apply (cancel_mono (cochainsZeroIso X).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ext c
  change (cochainsZeroIso X).hom.hom
      (TopModuleCat.kerι ((homogeneousCochains X).d 0 1)
        ((TopModuleCat.ofIso (d₀kerIso X)).inv.hom c)) = (c : X)
  rw [cochainsZeroIso_hom_apply, TopModuleCat.kerι_apply]
  change ((d₀kerIso X).symm c).1.1 1 = (c : X)
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem zeroIso_inv_homologyπ
    (X : TopRep.{max v w} k G) [TopRep.JointlyContinuous X] :
    (zeroIso X).inv ≫ (homogeneousCochains X).isoHomologyπ₀.inv ≫
        (homogeneousCochains X).homologyπ 0 = (zeroIso X).inv := by
  change (zeroIso X).inv ≫ (homogeneousCochains X).isoHomologyπ₀.inv ≫
    (homogeneousCochains X).isoHomologyπ₀.hom = (zeroIso X).inv
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem splitConnecting_cochain_lift [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A]
    (S : TopologicallySplitShortExact A B C) :
    (TopModuleCat.ofHom S.sectionOnInvariants ≫ (cochainsZeroIso B).inv) ≫
        (cochainsMap (ContinuousMonoidHom.id G) S.p).f 0 =
      ((zeroIso C).inv ≫ (homogeneousCochains C).isoHomologyπ₀.inv) ≫
        (homogeneousCochains C).iCycles 0 := by
  letI : TopRep.JointlyContinuous C :=
    jointlyContinuous_of_surjective_discrete S.p S.surjective_p
  simp only [Category.assoc, zeroIso_inv_iCycles_eq_zeroCochain C,
    cochainsZeroIso_inv_naturality S.p]
  simp only [← Category.assoc]
  congr 1
  ext x
  exact S.p_section x

set_option backward.isDefEq.respectTransparency false in
private theorem splitConnecting_cochain_boundary [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A]
    (S : TopologicallySplitShortExact A B C) :
    ((TopModuleCat.ofHom S.connectingCrossed ≫ (cocyclesOneCrossedIso A).inv) ≫
        (homogeneousCochains A).iCycles 1) ≫
        (cochainsMap (ContinuousMonoidHom.id G) S.i).f 1 =
      (TopModuleCat.ofHom S.sectionOnInvariants ≫ (cochainsZeroIso B).inv) ≫
        (homogeneousCochains B).d 0 1 := by
  let aTop : TopModuleCat.of k C.ρ.invariants ⟶
      (homogeneousCochains A).cycles 1 :=
    TopModuleCat.ofHom S.connectingCrossed ≫ (cocyclesOneCrossedIso A).inv
  let bTop : TopModuleCat.of k C.ρ.invariants ⟶
      (homogeneousCochains B).X 0 :=
    TopModuleCat.ofHom S.sectionOnInvariants ≫ (cochainsZeroIso B).inv
  have hcross : TopModuleCat.ofHom S.connectingCrossed ≫
      TopModuleCat.ofHom (crossedMap S.i) =
        TopModuleCat.ofHom S.sectionOnInvariants ≫
          TopModuleCat.ofHom (principalToCrossedL B) := by
    ext x g
    change S.i (S.retract (B.ρ g (S.section_ x) - S.section_ x)) =
      B.ρ g (S.section_ x) - S.section_ x
    exact S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero x g)
  have hcore : aTop ≫ cocyclesMap (ContinuousMonoidHom.id G) S.i 1 =
      bTop ≫ (homogeneousCochains B).toCycles 0 1 := by
    apply (cancel_mono (cocyclesOneCrossedIso B).hom).1
    calc
      (aTop ≫ cocyclesMap (ContinuousMonoidHom.id G) S.i 1) ≫
          (cocyclesOneCrossedIso B).hom =
        TopModuleCat.ofHom S.connectingCrossed ≫
          TopModuleCat.ofHom (crossedMap S.i) := by
            dsimp only [aTop]
            rw [Category.assoc, cocyclesOneCrossedIso_natural]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
      _ = TopModuleCat.ofHom S.sectionOnInvariants ≫
          TopModuleCat.ofHom (principalToCrossedL B) := hcross
      _ = (bTop ≫ (homogeneousCochains B).toCycles 0 1) ≫
          (cocyclesOneCrossedIso B).hom := by
            dsimp only [bTop]
            rw [Category.assoc, toCycles_comp_cocyclesOneCrossedIso]
            simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change (aTop ≫ (homogeneousCochains A).iCycles 1) ≫
      (cochainsMap (ContinuousMonoidHom.id G) S.i).f 1 =
        bTop ≫ (homogeneousCochains B).d 0 1
  calc
    _ = (aTop ≫ cocyclesMap (ContinuousMonoidHom.id G) S.i 1) ≫
        (homogeneousCochains B).iCycles 1 := by
          simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
    _ = (bTop ≫ (homogeneousCochains B).toCycles 0 1) ≫
        (homogeneousCochains B).iCycles 1 := by rw [hcore]
    _ = _ := by rw [Category.assoc, HomologicalComplex.toCycles_i]

set_option backward.isDefEq.respectTransparency false in
private theorem splitConnecting_homology [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A]
    (S : TopologicallySplitShortExact A B C) :
    (TopModuleCat.ofHom S.connectingCrossed ≫ (cocyclesOneCrossedIso A).inv) ≫
        (homogeneousCochains A).homologyπ 1 = S.connectingMap := by
  apply (cancel_mono (homologyQuotientIso A).hom).1
  rw [Category.assoc, Category.assoc, π_comp_homologyQuotientIso]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  change TopModuleCat.ofHom S.connectingCrossed ≫
    TopModuleCat.ofHom (principalCocycles A).mkQL =
      TopModuleCat.ofHom S.connectingQuotient ≫ (degreeOneIso A).hom ≫
        (homologyQuotientIso A).hom
  simp only [degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem connecting_zero_of_representative [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom)
    {T : ModuleCat.{max v w} k} (z : T ⟶ (moduleCochains C).X 0)
    (hz : z ≫ (moduleCochains C).d 0 1 = 0)
    (b : T ⟶ (moduleCochains B).X 0)
    (hb : b ≫ (moduleCochainsSequence i p hexact).g.f 0 = z)
    (a : T ⟶ (moduleCochains A).X 1)
    (ha : a ≫ (moduleCochainsSequence i p hexact).f.f 1 =
      b ≫ (moduleCochains B).d 0 1)
    (haCycle : a ≫ (moduleCochains A).d 1 2 = 0)
    (source : T ⟶ (forget₂ (TopModuleCat.{max v w} k)
      (ModuleCat.{max v w} k)).obj (continuousCohomology 0 C))
    (target : T ⟶ (forget₂ (TopModuleCat.{max v w} k)
      (ModuleCat.{max v w} k)).obj (continuousCohomology 1 A))
    (hq : (moduleCochains C).liftCycles z 1 (by simp) hz ≫
      (moduleCochains C).homologyπ 0 ≫ (moduleCohomologyIso C 0).hom = source)
    (hr : (moduleCochains A).liftCycles a 2 (by simp) haCycle ≫
      (moduleCochains A).homologyπ 1 ≫ (moduleCohomologyIso A 1).hom = target) :
    source ≫ connecting i p hi hexact hp 0 = target := by
  rw [← hq]
  simpa only [Nat.zero_add, Category.assoc, hr] using
    (connecting_apply i p hi hexact hp 0 z hz b hb a ha)

set_option maxHeartbeats 800000 in
-- The split comparison assembles preserved homology and degree-one quotient isomorphisms.
set_option backward.isDefEq.respectTransparency false in
private theorem splitConnecting_map_eq [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A]
    (S : TopologicallySplitShortExact A B C) :
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (zeroIso C).inv ≫
      connecting S.i S.p S.injective_i S.exact S.surjective_p 0 =
        (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
          S.connectingMap := by
  letI : TopRep.JointlyContinuous C :=
    jointlyContinuous_of_surjective_discrete S.p S.surjective_p
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  let Q : TopModuleCat.{max v w} k := TopModuleCat.of k C.ρ.invariants
  let zTop : Q ⟶ (homogeneousCochains C).cycles 0 :=
    (zeroIso C).inv ≫ (homogeneousCochains C).isoHomologyπ₀.inv
  let bTop : Q ⟶ (homogeneousCochains B).X 0 :=
    TopModuleCat.ofHom S.sectionOnInvariants ≫ (cochainsZeroIso B).inv
  let aTop : Q ⟶ (homogeneousCochains A).cycles 1 :=
    TopModuleCat.ofHom S.connectingCrossed ≫ (cocyclesOneCrossedIso A).inv
  have hbTop : bTop ≫ (cochainsMap (ContinuousMonoidHom.id G) S.p).f 0 =
      zTop ≫ (homogeneousCochains C).iCycles 0 :=
    splitConnecting_cochain_lift S
  have haTop : (aTop ≫ (homogeneousCochains A).iCycles 1) ≫
      (cochainsMap (ContinuousMonoidHom.id G) S.i).f 1 =
        bTop ≫ (homogeneousCochains B).d 0 1 :=
    splitConnecting_cochain_boundary S
  let z : F.obj Q ⟶ (moduleCochains C).X 0 :=
    F.map (zTop ≫ (homogeneousCochains C).iCycles 0)
  let b : F.obj Q ⟶ (moduleCochains B).X 0 := F.map bTop
  let a : F.obj Q ⟶ (moduleCochains A).X 1 :=
    F.map (aTop ≫ (homogeneousCochains A).iCycles 1)
  have hz : z ≫ (moduleCochains C).d 0 1 = 0 := by
    change F.map (zTop ≫ (homogeneousCochains C).iCycles 0) ≫
      F.map ((homogeneousCochains C).d 0 1) = 0
    rw [← F.map_comp, Category.assoc, HomologicalComplex.iCycles_d,
      comp_zero, Functor.map_zero]
  have haCycle : a ≫ (moduleCochains A).d 1 2 = 0 := by
    change F.map (aTop ≫ (homogeneousCochains A).iCycles 1) ≫
      F.map ((homogeneousCochains A).d 1 2) = 0
    rw [← F.map_comp, Category.assoc, HomologicalComplex.iCycles_d,
      comp_zero, Functor.map_zero]
  have hb : b ≫ (moduleCochainsSequence S.i S.p S.exact).g.f 0 = z := by
    change F.map bTop ≫ F.map ((cochainsMap (ContinuousMonoidHom.id G) S.p).f 0) =
      F.map (zTop ≫ (homogeneousCochains C).iCycles 0)
    simpa only [← F.map_comp] using congrArg F.map hbTop
  have ha : a ≫ (moduleCochainsSequence S.i S.p S.exact).f.f 1 =
      b ≫ (moduleCochains B).d 0 1 := by
    change F.map (aTop ≫ (homogeneousCochains A).iCycles 1) ≫
      F.map ((cochainsMap (ContinuousMonoidHom.id G) S.i).f 1) =
        F.map bTop ≫ F.map ((homogeneousCochains B).d 0 1)
    simpa only [← F.map_comp] using congrArg F.map haTop
  have hzero : zTop ≫ (homogeneousCochains C).homologyπ 0 = (zeroIso C).inv :=
    zeroIso_inv_homologyπ C
  have hsource : (moduleCochains C).liftCycles z 1 (by simp) hz ≫
      (moduleCochains C).homologyπ 0 ≫ (moduleCohomologyIso C 0).hom =
        F.map (zeroIso C).inv := by
    calc
      _ = F.map (zTop ≫ (homogeneousCochains C).homologyπ 0) :=
        moduleCohomologyIso_liftCycles C 0 zTop
      _ = F.map (zeroIso C).inv := by rw [hzero]
  have hone : aTop ≫ (homogeneousCochains A).homologyπ 1 = S.connectingMap :=
    splitConnecting_homology S
  have htarget : (moduleCochains A).liftCycles a 2 (by simp) haCycle ≫
      (moduleCochains A).homologyπ 1 ≫
        (moduleCohomologyIso A 1).hom = F.map S.connectingMap := by
    calc
      _ = F.map (aTop ≫ (homogeneousCochains A).homologyπ 1) :=
        moduleCohomologyIso_liftCycles A 1 aTop
      _ = F.map S.connectingMap := by rw [hone]
  have hmap : F.map (zeroIso C).inv ≫
      connecting S.i S.p S.injective_i S.exact S.surjective_p 0 =
        F.map S.connectingMap :=
    connecting_zero_of_representative S.i S.p S.injective_i S.exact
      S.surjective_p z hz b hb a ha haCycle
      (F.map (zeroIso C).inv) (F.map S.connectingMap) hsource htarget
  exact hmap

private theorem forgetModule_map_apply {X Y : TopModuleCat.{w} k}
    (f : X ⟶ Y) (x : X) :
    ((forget₂ (TopModuleCat.{w} k) (ModuleCat.{w} k)).map f) x = f x := rfl

set_option backward.isDefEq.respectTransparency false in
/-- On split short exact sequences, the all-degree algebraic connector agrees
with the previously constructed continuous degree-zero connector, after the
canonical identification of invariant coefficients with degree-zero cohomology. -/
theorem connecting_zero_eq_split [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A]
    (S : TopologicallySplitShortExact A B C) (c : C.ρ.invariants) :
    (connecting S.i S.p S.injective_i S.exact S.surjective_p 0).hom
      ((zeroIso C).inv.hom c) = S.connectingMap.hom c := by
  letI : TopRep.JointlyContinuous C :=
    jointlyContinuous_of_surjective_discrete S.p S.surjective_p
  have h := congrArg (fun f => ModuleCat.Hom.hom f c) (splitConnecting_map_eq S)
  simpa only [ModuleCat.comp_apply, forgetModule_map_apply] using h

end ContinuousCohomology

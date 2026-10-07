/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CohomologyExactSequence
public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Initial invariants in the continuous-cohomology exact sequence

The underlying-module sequence starts at zero and passes through invariant
coefficients before reaching degree-one continuous cohomology. Its connecting
arrow is the existing algebraic connecting map in degree zero, composed with
Mathlib's identification of invariant coefficients with degree-zero cohomology.
The initial injection and invariant left exactness do not require topological
splittings. The connector is not asserted to be continuous, and no surjectivity
at the final degree-one term is asserted.

The intended long exact sequence extends the initial display for profinite groups
and discrete integral modules to the stated locally compact, discrete-coefficient
setting and an arbitrary topologized coefficient ring.

The degree-zero invariant identification is natural in coefficient maps.
Exactness at all five internal positions follows from invariant injection,
invariant left exactness, and the algebraic cohomology exact sequence.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, electronic version 2.3, Chapter I, §3, Theorem (1.3.2).
* Mathlib's `TopRep.invariantsFunctor`, `ContinuousCohomology.zeroIso` and
  `ComposableArrows.Exact`; the existing algebraic continuous-cohomology connector.
-/

@[expose] public section

open CategoryTheory TopRep
open scoped ZeroObject

universe u v w

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G]
variable {A B C : TopRep.{max v w} k G}

/-- A coefficient injection restricts to an injection on invariant elements,
without discreteness, local compactness, or a section. -/
theorem mapInvariants_injective (i : A ⟶ B) (hi : Function.Injective i.hom) :
    Function.Injective i.hom.mapInvariants := by
  intro a a' h
  apply Subtype.ext
  apply hi
  exact congrArg Subtype.val h

/-- Invariants preserve exactness at the middle coefficient of an injective,
exact pair of equivariant coefficient maps, without a splitting or surjectivity. -/
theorem exact_mapInvariants (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom) :
    Function.Exact i.hom.mapInvariants p.hom.mapInvariants := by
  apply Function.Exact.of_comp_of_mem_range
  · funext a
    apply Subtype.ext
    exact (hexact (i a)).2 ⟨a, rfl⟩
  · intro b hb
    have hb' : p b = 0 := by
      simpa only [ContIntertwiningMap.mapInvariants_apply, Submodule.coe_zero]
        using congrArg Subtype.val hb
    obtain ⟨a, ha⟩ := (hexact b).1 hb'
    have haInv : a ∈ A.ρ.invariants := by
      intro g
      apply hi
      rw [TopRep.hom_comm_apply, ha, b.2 g, ← ha]
    exact ⟨⟨a, haInv⟩, Subtype.ext ha⟩

end TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G]
variable {A B C : TopRep.{max v w} k G}

@[deprecated (since := "2026-10-07")]
alias mapInvariants_injective := TopRep.mapInvariants_injective

@[deprecated (since := "2026-10-07")]
alias exact_mapInvariants := TopRep.exact_mapInvariants

variable [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of Mathlib's degree-zero cohomology/invariants isomorphism
with respect to a fixed-group coefficient map. -/
theorem zeroIso_naturality (f : A ⟶ B) :
    (zeroIso A).hom ≫ (invariantsFunctor k G).map f =
      map (ContinuousMonoidHom.id G) f 0 ≫ (zeroIso B).hom := by
  apply (cancel_epi (π A 0)).1
  conv_rhs => rw [← Category.assoc]
  erw [π_map]
  simp only [zeroIso, Iso.trans_hom, Iso.symm_hom, π, CochainComplex.isoHomologyπ₀,
    Category.assoc, HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]
  have hker (X : TopRep.{max v w} k G) :
      (cocycles₀Iso X).hom ≫ TopModuleCat.kerι _ =
        (homogeneousCochains X).iCycles 0 := by
    simpa [cocycles₀Iso] using
      (Limits.KernelFork.mapOfIsLimit_ι
        (Limits.KernelFork.ofι ((homogeneousCochains X).iCycles 0)
          ((homogeneousCochains X).iCycles_d 0 1))
        (TopModuleCat.isLimitKer _) (Iso.refl _).hom)
  ext x
  have hA := congrArg (fun morphism => morphism.hom x) (hker A)
  have hB := congrArg (fun morphism => morphism.hom (cocyclesMap
    (ContinuousMonoidHom.id G) f 0 x)) (hker B)
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at hA hB
  change f.hom (((TopModuleCat.kerι _).hom ((cocycles₀Iso A).hom x)).1 1) =
    ((TopModuleCat.kerι _).hom ((cocycles₀Iso B).hom
      (cocyclesMap (ContinuousMonoidHom.id G) f 0 x))).1 1
  rw [hA, hB]
  have hmap := congrArg (fun morphism => morphism.hom x)
    (HomologicalComplex.cyclesMap_i (cochainsMap (ContinuousMonoidHom.id G) f) 0)
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at hmap
  rw [hmap]
  rfl

/-- The first seven objects and six maps of the algebraic long exact sequence:
`0 → Aᴳ → Bᴳ → Cᴳ → H¹(G,A) → H¹(G,B) → H¹(G,C)`.
The invariant maps come from Mathlib's functor, and the boundary is precisely
the existing degree-zero connecting map transported along `zeroIso`. -/
noncomputable def initialInvariantsSequence [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    ComposableArrows (ModuleCat.{max v w} k) 6 :=
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  (ComposableArrows.mk₅
    (F.map ((invariantsFunctor k G).map i))
    (F.map ((invariantsFunctor k G).map p))
    (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0)
    (F.map (map (ContinuousMonoidHom.id G) i 1))
    (F.map (map (ContinuousMonoidHom.id G) p 1))).precomp
      (0 : (0 : ModuleCat.{max v w} k) ⟶ F.obj ((invariantsFunctor k G).obj A))

section ObjectEquations

variable [LocallyCompactSpace G] [DiscreteTopology B] [DiscreteTopology C]
  [TopRep.JointlyContinuous B]
variable (i : A ⟶ B) (p : B ⟶ C)
  (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
  (hp : Function.Surjective p.hom)

@[simp] theorem initialInvariantsSequence_obj_zero :
    (initialInvariantsSequence i p hi hexact hp).obj 0 =
      (0 : ModuleCat.{max v w} k) := rfl

@[simp] theorem initialInvariantsSequence_obj_invariantsA :
    (initialInvariantsSequence i p hi hexact hp).obj 1 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        ((invariantsFunctor k G).obj A) := rfl

@[simp] theorem initialInvariantsSequence_obj_invariantsB :
    (initialInvariantsSequence i p hi hexact hp).obj 2 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        ((invariantsFunctor k G).obj B) := rfl

@[simp] theorem initialInvariantsSequence_obj_invariantsC :
    (initialInvariantsSequence i p hi hexact hp).obj 3 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        ((invariantsFunctor k G).obj C) := rfl

@[simp] theorem initialInvariantsSequence_obj_cohomologyA :
    (initialInvariantsSequence i p hi hexact hp).obj 4 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology 1 A) := rfl

@[simp] theorem initialInvariantsSequence_obj_cohomologyB :
    (initialInvariantsSequence i p hi hexact hp).obj 5 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology 1 B) := rfl

@[simp] theorem initialInvariantsSequence_obj_cohomologyC :
    (initialInvariantsSequence i p hi hexact hp).obj 6 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).obj
        (continuousCohomology 1 C) := rfl

end ObjectEquations

@[simp] theorem initialInvariantsSequence_zero [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 0 1 = 0 := rfl

@[simp] theorem initialInvariantsSequence_inclusion [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 1 2 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        ((invariantsFunctor k G).map i) := rfl

@[simp] theorem initialInvariantsSequence_projection [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 2 3 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        ((invariantsFunctor k G).map p) := rfl

/-- The displayed inclusion applies the coefficient map to invariant elements. -/
@[simp] theorem initialInvariantsSequence_inclusion_apply [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (a : A.ρ.invariants) :
    ((initialInvariantsSequence i p hi hexact hp).map' 1 2).hom a =
      i.hom.mapInvariants a := by
  rw [initialInvariantsSequence_inclusion]
  rfl

@[simp] theorem initialInvariantsSequence_boundary [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 3 4 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (zeroIso C).inv ≫ connecting i p hi hexact hp 0 := rfl

/-- The displayed boundary applies the existing connector to the degree-zero
class corresponding to an invariant quotient coefficient. -/
@[simp] theorem initialInvariantsSequence_boundary_apply [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (c : C.ρ.invariants) :
    ((initialInvariantsSequence i p hi hexact hp).map' 3 4).hom c =
      (connecting i p hi hexact hp 0).hom ((zeroIso C).inv.hom c) := by
  rw [initialInvariantsSequence_boundary]
  rfl

@[simp] theorem initialInvariantsSequence_degreeOneInclusion [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 4 5 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (map (ContinuousMonoidHom.id G) i 1) := rfl

@[simp] theorem initialInvariantsSequence_degreeOneProjection [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).map' 5 6 =
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (map (ContinuousMonoidHom.id G) p 1) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The initial, unsplit exact segment. Exactness holds at `Aᴳ`, `Bᴳ`,
`Cᴳ`, `H¹(G,A)` and `H¹(G,B)`; no terminal surjectivity is claimed. -/
theorem initialInvariantsSequence_exact [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) :
    (initialInvariantsSequence i p hi hexact hp).Exact := by
  let F := forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)
  let S := initialInvariantsSequence i p hi hexact hp
  have h₀ : Function.Exact (S.map' 0 1).hom (S.map' 1 2).hom := by
    change Function.Exact (0 : (0 : ModuleCat.{max v w} k) →ₗ[k] A.ρ.invariants)
      i.hom.mapInvariants.toLinearMap
    exact (LinearMap.exact_zero_iff_injective (0 : ModuleCat.{max v w} k)
      i.hom.mapInvariants.toLinearMap).2 (TopRep.mapInvariants_injective i hi)
  have h₁ : Function.Exact (S.map' 1 2).hom (S.map' 2 3).hom := by
    change Function.Exact i.hom.mapInvariants p.hom.mapInvariants
    exact TopRep.exact_mapInvariants i p hi hexact
  have h₂ : Function.Exact (S.map' 2 3).hom (S.map' 3 4).hom := by
    have h : Function.Exact (F.map ((invariantsFunctor k G).map p)).hom
        (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0).hom := by
      apply Function.Exact.of_ladder_linearEquiv_of_exact
        (f₁₂ := (F.map (map (ContinuousMonoidHom.id G) p 0)).hom)
        (f₂₃ := (connecting i p hi hexact hp 0).hom)
        (g₁₂ := (F.map ((invariantsFunctor k G).map p)).hom)
        (g₂₃ := (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0).hom)
        (e₁ := (F.mapIso (zeroIso B)).toLinearEquiv)
        (e₂ := (F.mapIso (zeroIso C)).toLinearEquiv)
        (e₃ := LinearEquiv.refl k _)
      · change (F.map (zeroIso B).hom ≫ F.map ((invariantsFunctor k G).map p)).hom =
          (F.map (map (ContinuousMonoidHom.id G) p 0) ≫ F.map (zeroIso C).hom).hom
        apply congrArg ModuleCat.Hom.hom
        calc
          F.map (zeroIso B).hom ≫ F.map ((invariantsFunctor k G).map p) =
              F.map ((zeroIso B).hom ≫ (invariantsFunctor k G).map p) :=
            (F.map_comp _ _).symm
          _ = F.map (map (ContinuousMonoidHom.id G) p 0 ≫ (zeroIso C).hom) :=
            congrArg F.map (zeroIso_naturality p)
          _ = F.map (map (ContinuousMonoidHom.id G) p 0) ≫ F.map (zeroIso C).hom :=
            F.map_comp _ _
      · change (F.map (zeroIso C).hom ≫ F.map (zeroIso C).inv ≫
            connecting i p hi hexact hp 0).hom =
          (connecting i p hi hexact hp 0).hom
        simp
      · exact exact_map_connecting i p hi hexact hp 0
    change Function.Exact (F.map ((invariantsFunctor k G).map p)).hom
      (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0).hom
    exact h
  have h₃ : Function.Exact (S.map' 3 4).hom (S.map' 4 5).hom := by
    have h := (LinearEquiv.precomp_exact_iff_exact
      (e := (F.mapIso (zeroIso C)).symm.toLinearEquiv)).2
        (exact_connecting_map i p hi hexact hp 0)
    change Function.Exact (F.map (zeroIso C).inv ≫ connecting i p hi hexact hp 0).hom
      (F.map (map (ContinuousMonoidHom.id G) i 1)).hom
    convert h using 1; simp only [Iso.symm_hom, Functor.mapIso_inv,
      Iso.toLinearMap_toLinearEquiv, ModuleCat.hom_comp]
  have h₄ : Function.Exact (S.map' 4 5).hom (S.map' 5 6).hom := by
    change Function.Exact (map (ContinuousMonoidHom.id G) i 1).hom
      (map (ContinuousMonoidHom.id G) p 1).hom
    exact exact_map_map i p hi hexact hp 1
  have hAt (index : ℕ) (bound : index + 2 ≤ 6) :
      Function.Exact (S.map' index (index + 1)).hom
        (S.map' (index + 1) (index + 2)).hom := by
    have upper : index ≤ 4 := by omega
    interval_cases index
    · exact h₀
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  have hzero (index : ℕ) (bound : index + 2 ≤ 6) :
      S.map' index (index + 1) ≫ S.map' (index + 1) (index + 2) = 0 := by
    apply ModuleCat.hom_ext
    ext x
    exact (hAt index bound ((S.map' index (index + 1)).hom x)).2 ⟨x, rfl⟩
  refine ⟨⟨hzero⟩, ?_⟩
  intro index bound
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
    (hAt index bound)

end ContinuousCohomology

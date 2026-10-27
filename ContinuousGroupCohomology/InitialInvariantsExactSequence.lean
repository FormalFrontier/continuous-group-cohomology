/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CohomologyExactSequence
public import ContinuousGroupCohomology.ContinuousCohomologyFunctor
public import ContinuousGroupCohomology.TopRepMonomorphisms
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

The degree-zero invariant identification is natural in continuous group
homomorphisms and equivariant coefficient maps, extending fixed-group
coefficient-map naturality. An injective coefficient map induces an injection
in degree zero without surjectivity of the group homomorphism. Consequently,
monomorphisms of restricted coefficients induce monomorphisms in degree zero,
and the degree-zero coefficient functor preserves monomorphisms. No analogous
all-degree injectivity is asserted. Exactness at all five internal positions
follows from invariant injection, invariant left exactness, and the algebraic
cohomology exact sequence.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, electronic version 2.3, Chapter I, §3, Theorem (1.3.2).
* Mathlib's `TopRep.invariantsFunctor`, `ContinuousCohomology.zeroIso` and
  `ComposableArrows.Exact`; the existing algebraic continuous-cohomology connector.
* Mathlib's continuous representations and continuous cohomology, by Richard Hill,
  Andrew Yang and Edison Xie, and Beacon's surrounding continuous-cohomology API.

The degree-zero extension was developed with AI assistance.
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

/-- On a degree-zero cocycle, the cohomology/invariants identification is the
kernel/invariants identification after the canonical cocycle/kernel comparison. -/
@[simp] theorem π_zeroIso_hom (X : TopRep.{max v w} k G) :
    π X 0 ≫ (zeroIso X).hom =
      (cocycles₀Iso X).hom ≫ (TopModuleCat.ofIso (d₀kerIso X)).hom := by
  simp only [zeroIso, Iso.trans_hom, Iso.symm_hom, π, CochainComplex.isoHomologyπ₀,
    HomologicalComplex.isoHomologyπ_hom_inv_id_assoc]

/-- The invariant coefficient of a degree-zero cocycle class is the value at the
unit of its image under the canonical inclusion into homogeneous cochains. -/
@[simp] theorem π_zeroIso_hom_apply (X : TopRep.{max v w} k G) (z : cocycles X 0) :
    ((zeroIso X).hom.hom ((π X 0).hom z) : X) =
      (((homogeneousCochains X).iCycles 0).hom z).1 1 := by
  change ((π X 0 ≫ (zeroIso X).hom).hom z : X) = _
  rw [π_zeroIso_hom]
  have hι : (cocycles₀Iso X).hom ≫
      TopModuleCat.kerι ((homogeneousCochains X).d 0 1) =
        (homogeneousCochains X).iCycles 0 := by
    simpa [cocycles₀Iso] using
      (Limits.KernelFork.mapOfIsLimit_ι
        (Limits.KernelFork.ofι ((homogeneousCochains X).iCycles 0)
          ((homogeneousCochains X).iCycles_d 0 1))
        (TopModuleCat.isLimitKer _) (Iso.refl _).hom)
  have hz := congrArg (fun morphism => morphism.hom z) hι
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at hz
  change (((TopModuleCat.kerι _).hom ((cocycles₀Iso X).hom z)).1 1) = _
  exact congrArg (fun σ : (homogeneousCochains X).X 0 => σ.1 1) hz

section GroupMaps

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {X : TopRep.{max v w} k G} {Y : TopRep.{max v w} k H}

/-- Naturality of Mathlib's degree-zero cohomology/invariants isomorphism under
an arbitrary continuous group homomorphism and an equivariant coefficient map.
This extends fixed-group coefficient-map naturality; no surjectivity of the
group homomorphism is required. It extends the invariant interpretation of
degree zero used in Neukirch–Schmidt–Wingberg, Chapter I, §3. -/
theorem zeroIso_naturality_res (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    (zeroIso X).hom ≫ invariantsResMap φ f =
      map φ f 0 ≫ (zeroIso Y).hom := by
  apply (cancel_epi (π X 0)).1
  simp only [← Category.assoc, π_map (X := X) (Y := Y) φ f 0]
  apply ConcreteCategory.ext_apply
  intro z
  apply Subtype.ext
  change f.hom ((zeroIso X).hom.hom ((π X 0).hom z) : X) =
    ((zeroIso Y).hom.hom ((π Y 0).hom
      ((cocyclesMap (X := X) (Y := Y) φ f 0).hom z)) : Y)
  have hX := π_zeroIso_hom_apply X z
  have hY := π_zeroIso_hom_apply Y
    ((cocyclesMap (X := X) (Y := Y) φ f 0).hom z)
  rw [hX, hY]
  have hmap := congrArg
    (fun morphism : cocycles X 0 ⟶ (homogeneousCochains Y).X 0 =>
      morphism.hom z)
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (X := X) (Y := Y) φ f) 0)
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at hmap
  rw [hmap]
  change f.hom ((((homogeneousCochains X).iCycles 0).hom z).1 1) =
    f.hom ((((homogeneousCochains X).iCycles 0).hom z).1 (φ 1))
  rw [_root_.map_one φ]

/-- An injective coefficient map induces an injection on degree-zero continuous
cohomology under any continuous group homomorphism, without surjectivity of that
homomorphism. The conclusion concerns degree zero only and uses the invariant
interpretation of degree zero in Neukirch–Schmidt–Wingberg, Chapter I, §3. -/
theorem map_zero_injective (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (hf : Function.Injective f.hom) :
    Function.Injective (map φ f 0).hom := by
  have hInv : Function.Injective
      (invariantsResMap (k := k) (G := G) (H := H)
        (X := X) (Y := Y) (φ : H →* G) f).hom := by
    intro x y hxy
    have hxy' :
        f.hom.mapInvariants
            (⟨x.1, ContRepresentation.invariants_le_invariants_restrict
              X.ρ (φ : H →* G) x.2⟩ : (res (φ : H →* G) X).ρ.invariants) =
          f.hom.mapInvariants
            (⟨y.1, ContRepresentation.invariants_le_invariants_restrict
              X.ρ (φ : H →* G) y.2⟩ : (res (φ : H →* G) X).ρ.invariants) := by
      apply Subtype.ext
      exact congrArg Subtype.val hxy
    exact Subtype.ext (congrArg
      (fun z : (res (φ : H →* G) X).ρ.invariants => z.1)
      ((TopRep.mapInvariants_injective (k := k) (G := H)
        (A := res (φ : H →* G) X) (B := Y) f hf) hxy'))
  intro a b hab
  apply (zeroIso X).toContinuousLinearEquiv.injective
  apply hInv
  have ha := congrArg (fun morphism => morphism.hom a)
    (zeroIso_naturality_res (k := k) (G := G) (H := H) (X := X) (Y := Y) φ f)
  have hb := congrArg (fun morphism => morphism.hom b)
    (zeroIso_naturality_res (k := k) (G := G) (H := H) (X := X) (Y := Y) φ f)
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply] at ha hb
  exact ha.trans ((congrArg (zeroIso Y).hom.hom hab).trans hb.symm)

/-- A monomorphism of restricted coefficients induces a monomorphism on
degree-zero continuous cohomology for any continuous group homomorphism.
No surjectivity of the group homomorphism is required. -/
theorem map_zero_mono (φ : H →ₜ* G) (f : res φ X ⟶ Y) [Mono f] :
    Mono (map φ f 0) :=
  ConcreteCategory.mono_of_injective _
    (map_zero_injective φ f ((TopRep.mono_iff_injective f).1 inferInstance))

end GroupMaps

/-- Degree-zero continuous cohomology preserves monomorphisms in the
coefficient representation. -/
instance coefficientFunctor_zero_preservesMonomorphisms :
    (coefficientFunctor (k := k) (G := G) 0 :
      TopRep.{max v w} k G ⥤ TopModuleCat.{max v w} k).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    exact @map_zero_mono.{u, v, w} k _ _ G _ _ _ G _ _ _ X Y
      (ContinuousMonoidHom.id G) f hf

/-- Naturality of Mathlib's degree-zero cohomology/invariants isomorphism
with respect to a fixed-group coefficient map. -/
theorem zeroIso_naturality (f : A ⟶ B) :
    (zeroIso A).hom ≫ (invariantsFunctor k G).map f =
      map (ContinuousMonoidHom.id G) f 0 ≫ (zeroIso B).hom := by
  exact zeroIso_naturality_res (ContinuousMonoidHom.id G) f

/-- Degree-zero continuous cohomology is naturally isomorphic to the functor
of invariant coefficients. -/
noncomputable def zeroNatIso :
    coefficientFunctor.{u, v, w} (k := k) (G := G) 0 ≅
      (TopRep.invariantsFunctor k G :
        TopRep.{max v w} k G ⥤ TopModuleCat.{max v w} k) := by
  refine NatIso.ofComponents (fun X => zeroIso X) ?_
  intro X Y f
  dsimp only [coefficientFunctor_obj, coefficientFunctor_map]
  exact (zeroIso_naturality f).symm

/-- The forward component of the natural degree-zero identification is `zeroIso`. -/
@[simp] theorem zeroNatIso_hom_app (X : TopRep.{max v w} k G) :
    (zeroNatIso (k := k) (G := G)).hom.app X = (zeroIso X).hom := by
  rfl

/-- The inverse component of the natural degree-zero identification is `zeroIso` inverse. -/
@[simp] theorem zeroNatIso_inv_app (X : TopRep.{max v w} k G) :
    (zeroNatIso (k := k) (G := G)).inv.app X = (zeroIso X).inv := by
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
@[simp↓] theorem initialInvariantsSequence_inclusion_apply [LocallyCompactSpace G]
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

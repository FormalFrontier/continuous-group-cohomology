/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CochainInjectivity
public import ContinuousGroupCohomology.CoinducedAcyclic
public import ContinuousGroupCohomology.DegreeOne
public import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# Exactness of continuous homogeneous cochains with discrete coefficients

The maps are the existing `ContinuousCohomology.cochainsMap` for the identity group map.
The coefficient sequence is exact on underlying modules; no splitting, projectivity or
cohomological vanishing is part of the contract. Injectivity needs only injectivity of
the coefficient map. Exactness in the middle needs a discrete middle coefficient
space (the injective left-hand coefficient is then discrete as well). Surjectivity
uses a locally compact acting group, a discrete target and
joint continuity of the action on the middle coefficient space. In particular the
joint continuity of the action does not follow merely from membership in `TopRep`.

These results concern cochain objects, not cocycles, invariant coefficients or
cohomology: none of those generally preserve surjections.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, §3
  (cochain exactness preceding Theorem 1.3.2).
* Mathlib's `ContRepresentation.coind₁`, `TopRep.homogeneousCochains`,
  `ContinuousCohomology.cochainsMap` and the compact-open mapping-space API.
* Formal Frontier's `ContinuousCohomology.cochainsMap_injective`,
  `TopRep.resolutionEval_map` and `ContinuousCohomology.cochainsZeroEquiv`.
-/

@[expose] public section

universe u v w

open CategoryTheory ContRepresentation TopRep
open scoped Topology

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The recursive coinduced resolution has a jointly continuous action when the
original representation does and the group is locally compact. -/
theorem jointlyContinuous_resolutionX [LocallyCompactSpace G]
    (X : TopRep.{max v w} k G) [JointlyContinuous X] (n : ℕ) :
    JointlyContinuous (resolutionX X n) := by
  induction n with
  | zero => infer_instance
  | succ n ih =>
    let : JointlyContinuous (resolutionX X n) := ih
    exact jointlyContinuous_coind₁ (resolutionX X n)

end TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C : TopRep.{max v w} k G}

/-- Evaluation of an identity-group cochain map applies the coefficient morphism
after all the successive evaluations of the homogeneous cochain. -/
theorem cochainsMap_resolutionEval (f : A ⟶ B) (n : ℕ)
    (σ : (homogeneousCochains A).X n) (hs : Fin (n + 1) → G) :
    resolutionEval B (n + 1) ((cochainsMap (ContinuousMonoidHom.id G) f).f n σ).1 hs =
      f.hom (resolutionEval A (n + 1) σ.1 hs) := by
  exact resolutionEval_map f (n + 1) σ.1 hs

/-- Identity-group resolution maps commute pointwise with the group action. -/
theorem resolutionMap_id_apply_action (f : A ⟶ B) (n : ℕ) (g : G)
    (a : resolutionX A n) :
    (resolutionMap (ContinuousMonoidHom.id G) f n).hom ((resolutionX A n).ρ g a) =
      (resolutionX B n).ρ g
        ((resolutionMap (ContinuousMonoidHom.id G) f n).hom a) := by
  exact (resolutionMap (ContinuousMonoidHom.id G) f n).hom.isIntertwining g a

private def resolutionLift (X Y : TopRep.{max v w} k G) (lift : C(X, Y)) :
    (n : ℕ) → C(resolutionX X n, resolutionX Y n)
  | 0 => lift
  | n + 1 => ⟨fun f => (resolutionLift X Y lift n).comp f,
      ContinuousMap.continuous_postcomp (resolutionLift X Y lift n)⟩

private theorem resolutionLift_left_inverse
    (i : A ⟶ B) (p : B ⟶ C) (lift : C(B, A))
    (hlift : ∀ b, p.hom b = 0 → i.hom (lift b) = b) :
    ∀ (n : ℕ) (b : resolutionX B n),
      (resolutionMap (ContinuousMonoidHom.id G) p n).hom b = 0 →
        (resolutionMap (ContinuousMonoidHom.id G) i n).hom
          (resolutionLift B A lift n b) = b := by
  intro n
  induction n with
  | zero =>
    intro b hb
    exact hlift b hb
  | succ n ih =>
    intro b hb
    ext g
    apply ih
    have h := congrArg (fun f : resolutionX C (n + 1) => f g) hb
    change (resolutionMap (ContinuousMonoidHom.id G) p n).hom (b g) = 0 at h
    exact h

private theorem resolutionLift_right_inverse
    (p : B ⟶ C) (lift : C(C, B))
    (hlift : ∀ c, p.hom (lift c) = c) :
    ∀ (n : ℕ) (c : resolutionX C n),
      (resolutionMap (ContinuousMonoidHom.id G) p n).hom
        (resolutionLift C B lift n c) = c := by
  intro n
  induction n with
  | zero => exact hlift
  | succ n ih =>
    intro c
    ext g
    exact ih (c g)

private theorem resolutionEval_zero_term (Y : TopRep.{max v w} k G) :
    ∀ (n : ℕ) (hs : Fin n → G),
      resolutionEval Y n (0 : resolutionX Y n) hs = 0 := by
  intro n
  induction n with
  | zero => intro hs; rfl
  | succ n ih =>
    intro hs
    simpa only [resolutionEval_succ, ContinuousMap.zero_apply] using ih (Fin.tail hs)

/-- Composing the two induced cochain maps is zero whenever the coefficient
sequence is exact, without any discreteness hypothesis. -/
theorem cochainsMap_comp_zero (i : A ⟶ B) (p : B ⟶ C)
    (hexact : Function.Exact i.hom p.hom) (n : ℕ) :
    (cochainsMap (ContinuousMonoidHom.id G) i).f n ≫
      (cochainsMap (ContinuousMonoidHom.id G) p).f n = 0 := by
  ext τ
  change ((cochainsMap (ContinuousMonoidHom.id G) p).f n)
    (((cochainsMap (ContinuousMonoidHom.id G) i).f n) τ) = 0
  apply Subtype.ext
  apply resolutionEval_ext C (n + 1)
  intro hs
  rw [cochainsMap_resolutionEval, cochainsMap_resolutionEval]
  change p.hom (i.hom (resolutionEval A (n + 1) τ.1 hs)) =
    resolutionEval C (n + 1) (0 : resolutionX C (n + 1)) hs
  rw [resolutionEval_zero_term]
  exact (hexact _).mpr ⟨_, rfl⟩

/-- Exactness in the middle at every cochain degree for discrete middle
coefficients. No group compactness or joint-action continuity is required.
Compare Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter I, §3. -/
theorem cochainsMap_exact [DiscreteTopology B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (n : ℕ) :
    Function.Exact ((cochainsMap (ContinuousMonoidHom.id G) i).f n)
      ((cochainsMap (ContinuousMonoidHom.id G) p).f n) := by
  classical
  let lift : C(B, A) := ⟨fun b =>
    if hb : p.hom b = 0 then Classical.choose ((hexact b).mp hb) else 0,
    continuous_of_discreteTopology⟩
  have hlift (b : B) (hb : p.hom b = 0) : i.hom (lift b) = b := by
    simpa only [lift, ContinuousMap.coe_mk, dite_eq_left hb] using
      Classical.choose_spec ((hexact b).mp hb)
  intro σ
  constructor
  · intro hz
    have hzval : (resolutionMap (ContinuousMonoidHom.id G) p (n + 1)).hom σ.1 = 0 :=
      congrArg Subtype.val hz
    let a : resolutionX A (n + 1) := resolutionLift B A lift (n + 1) σ.1
    have ha : (resolutionMap (ContinuousMonoidHom.id G) i (n + 1)).hom a = σ.1 :=
      resolutionLift_left_inverse i p lift hlift (n + 1) σ.1 hzval
    have hainv : ∀ g : G, (resolutionX A (n + 1)).ρ g a = a := by
      intro g
      apply resolutionMap_injective (ContinuousMonoidHom.id G) i (fun t => ⟨t, rfl⟩)
        hi (n + 1)
      rw [resolutionMap_id_apply_action i (n + 1) g a, ha, σ.2 g]
    refine ⟨⟨a, hainv⟩, ?_⟩
    exact Subtype.ext ha
  · rintro ⟨τ, rfl⟩
    have hzero := congrArg (fun f => f τ) (cochainsMap_comp_zero i p hexact n)
    simpa only [CategoryTheory.comp_apply, TopModuleCat.hom_zero_apply] using hzero

/-- A surjection onto discrete coefficients induces a surjection on every
homogeneous cochain degree for locally compact groups. The middle action must be jointly
continuous; no equivariant or linear section is assumed. Compare
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter I, §3. -/
theorem cochainsMap_surjective [LocallyCompactSpace G] [DiscreteTopology C]
    [TopRep.JointlyContinuous B]
    (p : B ⟶ C) (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) p).f n) := by
  classical
  let lift : C(C, B) := ⟨fun c => Classical.choose (hp c),
    continuous_of_discreteTopology⟩
  have hlift (c : C) : p.hom (lift c) = c := Classical.choose_spec (hp c)
  let : TopRep.JointlyContinuous (resolutionX B n) :=
    jointlyContinuous_resolutionX B n
  intro σ
  let b : resolutionX B n := resolutionLift C B lift n (σ.1 1)
  let τ : (homogeneousCochains B).X n := (cochainsZeroEquiv (resolutionX B n)).symm b
  have hτ (g : G) : τ.1 g = (resolutionX B n).ρ g b :=
    cochainsZeroEquiv_symm_apply (resolutionX B n) b g
  have hs (g : G) : (resolutionX C n).ρ g (σ.1 1) = σ.1 g := by
    have h := congrArg (fun a : resolutionX C (n + 1) => a g) (σ.2 g)
    change (resolutionX C n).ρ g (σ.1 (g⁻¹ * g)) = σ.1 g at h
    simpa only [inv_mul_cancel] using h
  refine ⟨τ, ?_⟩
  apply Subtype.ext
  ext g
  change (resolutionMap (ContinuousMonoidHom.id G) p n).hom (τ.1 g) = σ.1 g
  rw [hτ, resolutionMap_id_apply_action p n g b, ← hs]
  exact congrArg ((resolutionX C n).ρ g) (resolutionLift_right_inverse p lift hlift n _)

/-- A short exact sequence of discrete coefficients with jointly continuous
middle action remains short exact in each degree of homogeneous cochains for
locally compact groups.
This asserts nothing about surjectivity on cocycles or cohomology. See
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter I, §3. -/
theorem cochainsMap_shortExact [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C]
    [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Injective ((cochainsMap (ContinuousMonoidHom.id G) i).f n) ∧
      Function.Exact ((cochainsMap (ContinuousMonoidHom.id G) i).f n)
        ((cochainsMap (ContinuousMonoidHom.id G) p).f n) ∧
      Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) p).f n) := by
  refine ⟨cochainsMap_injective (ContinuousMonoidHom.id G) i
    (fun g => ⟨g, rfl⟩) hi n, ?_, ?_⟩
  · exact cochainsMap_exact i p hi hexact n
  · exact cochainsMap_surjective p hp n

/-- The compact-group version of degreewise short exactness requires no
Hausdorff or coefficient-splitting hypothesis. -/
theorem cochainsMap_shortExact_of_compact [CompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C]
    [TopRep.JointlyContinuous B]
    (i : A ⟶ B) (p : B ⟶ C)
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom) (n : ℕ) :
    Function.Injective ((cochainsMap (ContinuousMonoidHom.id G) i).f n) ∧
      Function.Exact ((cochainsMap (ContinuousMonoidHom.id G) i).f n)
        ((cochainsMap (ContinuousMonoidHom.id G) p).f n) ∧
      Function.Surjective ((cochainsMap (ContinuousMonoidHom.id G) p).f n) := by
  let : LocallyCompactSpace G :=
    (isCompact_univ : IsCompact (Set.univ : Set G)).locallyCompactSpace_of_mem_nhds_of_group
      (Filter.univ_mem : (Set.univ : Set G) ∈ 𝓝 (1 : G))
  exact cochainsMap_shortExact i p hi hexact hp n

end ContinuousCohomology

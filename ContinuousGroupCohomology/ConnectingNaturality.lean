/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CohomologyExactSequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Naturality of the algebraic continuous-cohomology connector

A morphism between short exact sequences of discrete topological representations
commutes with the connecting homomorphisms on the underlying cohomology modules.
The result concerns the existing continuous cohomology and its coefficient maps;
no continuity of the connecting homomorphism is asserted.

## References

* Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
  edition, Chapter I, §3, Proposition (1.3.3).
* Mathlib, `HomologicalComplex.HomologySequence.δ_naturality`.
-/

@[expose] public section

open CategoryTheory TopRep

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {A B C A' B' C' : TopRep.{max v w} k G}

private theorem cochainsMap_comp_id (f : A ⟶ B) (g : B ⟶ C) :
    cochainsMap (ContinuousMonoidHom.id G) (f ≫ g) =
      cochainsMap (ContinuousMonoidHom.id G) f ≫
        cochainsMap (ContinuousMonoidHom.id G) g := by
  convert cochainsMap_comp (ContinuousMonoidHom.id G)
    (ContinuousMonoidHom.id G) f g using 1; rfl

set_option backward.isDefEq.respectTransparency false in
/-- A morphism of short exact coefficient sequences commutes with the
algebraic connecting homomorphisms of continuous cohomology. This is the
fixed-group, underlying-module formulation of the naturality in
Neukirch–Schmidt–Wingberg, Chapter I, §3, Proposition (1.3.3). -/
theorem connecting_naturality [LocallyCompactSpace G]
    [DiscreteTopology B] [DiscreteTopology C] [TopRep.JointlyContinuous B]
    [DiscreteTopology B'] [DiscreteTopology C'] [TopRep.JointlyContinuous B']
    (i : A ⟶ B) (p : B ⟶ C) (i' : A' ⟶ B') (p' : B' ⟶ C')
    (α : A ⟶ A') (β : B ⟶ B') (γ : C ⟶ C')
    (hi : Function.Injective i.hom) (hexact : Function.Exact i.hom p.hom)
    (hp : Function.Surjective p.hom)
    (hi' : Function.Injective i'.hom) (hexact' : Function.Exact i'.hom p'.hom)
    (hp' : Function.Surjective p'.hom)
    (hleft : i ≫ β = α ≫ i') (hright : p ≫ γ = β ≫ p') (n : ℕ) :
    connecting i p hi hexact hp n ≫
      (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (map (ContinuousMonoidHom.id G) α (n + 1)) =
    (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).map
        (map (ContinuousMonoidHom.id G) γ n) ≫
      connecting i' p' hi' hexact' hp' n := by
  let F := (forget₂ (TopModuleCat.{max v w} k) (ModuleCat.{max v w} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let φ : moduleCochainsSequence i p hexact ⟶
      moduleCochainsSequence i' p' hexact' :=
    ShortComplex.homMk
      (F.map (cochainsMap (ContinuousMonoidHom.id G) α))
      (F.map (cochainsMap (ContinuousMonoidHom.id G) β))
      (F.map (cochainsMap (ContinuousMonoidHom.id G) γ))
      (by
        change F.map (cochainsMap (ContinuousMonoidHom.id G) α) ≫
            F.map (cochainsMap (ContinuousMonoidHom.id G) i') =
          F.map (cochainsMap (ContinuousMonoidHom.id G) i) ≫
            F.map (cochainsMap (ContinuousMonoidHom.id G) β)
        rw [← F.map_comp, ← F.map_comp,
          ← cochainsMap_comp_id α i', ← cochainsMap_comp_id i β]
        exact congrArg (fun f : A ⟶ B' =>
          F.map (cochainsMap (ContinuousMonoidHom.id G) f)) hleft.symm)
      (by
        change F.map (cochainsMap (ContinuousMonoidHom.id G) β) ≫
            F.map (cochainsMap (ContinuousMonoidHom.id G) p') =
          F.map (cochainsMap (ContinuousMonoidHom.id G) p) ≫
            F.map (cochainsMap (ContinuousMonoidHom.id G) γ)
        rw [← F.map_comp, ← F.map_comp,
          ← cochainsMap_comp_id β p', ← cochainsMap_comp_id p γ]
        exact congrArg (fun f : B ⟶ C' =>
          F.map (cochainsMap (ContinuousMonoidHom.id G) f)) hright.symm)
  have hδ :
      (moduleCochainsSequence_shortExact i p hi hexact hp).δ n (n + 1) rfl ≫
          HomologicalComplex.homologyMap
            (F.map (cochainsMap (ContinuousMonoidHom.id G) α)) (n + 1) =
        HomologicalComplex.homologyMap
            (F.map (cochainsMap (ContinuousMonoidHom.id G) γ)) n ≫
          (moduleCochainsSequence_shortExact i' p' hi' hexact' hp').δ n (n + 1) rfl := by
    exact HomologicalComplex.HomologySequence.δ_naturality φ
      (moduleCochainsSequence_shortExact i p hi hexact hp)
      (moduleCochainsSequence_shortExact i' p' hi' hexact' hp') n (n + 1) rfl
  apply (cancel_epi (moduleCohomologyIso C n).hom).1
  conv_lhs =>
    rw [← Category.assoc, moduleCohomologyIso_connecting,
      Category.assoc, ← moduleCohomologyIso_naturality α (n + 1)]
  conv_rhs =>
    rw [← Category.assoc, ← moduleCohomologyIso_naturality γ n,
      Category.assoc, moduleCohomologyIso_connecting i' p' hi' hexact' hp' n]
  simpa only [Category.assoc] using
    congrArg (fun f => f ≫ (moduleCohomologyIso A' (n + 1)).hom) hδ

end ContinuousCohomology

/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.TopRepUlift
public import ContinuousGroupCohomology.Topology.ContinuousMap.CompactDiscrete

/-!
# Pointwise actions on compact-open function spaces

For a topological representation `B` of `H`, the representation on `C(Q, B)` acts
on its values, *not* on the index `Q`. This differs from twisted coinduction.
No group structure, compactness, discreteness, or local compactness is needed to
define the representation. Joint continuity and discreteness are separate facts.

The construction uses Mathlib's compact-open postcomposition and the existing
topological representation of `B`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public section

universe u v w z

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {H : Type v} [Monoid H] {Q : Type z} [TopologicalSpace Q]

/-- The pointwise `H`-representation on continuous maps into `B`. -/
abbrev pointwiseContinuousMap (Q : Type z) [TopologicalSpace Q]
    (B : TopRep.{w} k H) : TopRep.{max z w} k H :=
  .of <| .ofMonoidHom {
    toFun := fun h => ContinuousLinearMap.compLeftContinuous k Q (B.ρ h)
    map_one' := by
      apply ContinuousLinearMap.ext
      intro f
      apply ContinuousMap.ext
      intro q
      change B.ρ 1 (f q) = f q
      simp
    map_mul' := by
      intro h h'
      apply ContinuousLinearMap.ext
      intro f
      apply ContinuousMap.ext
      intro q
      change B.ρ (h * h') (f q) = B.ρ h (B.ρ h' (f q))
      simp [map_mul]
  }

@[simp] theorem pointwiseContinuousMap_V (B : TopRep.{w} k H) :
    (pointwiseContinuousMap Q B).V = C(Q, B) := rfl

/-- Acting on a continuous coefficient function acts on each value. -/
@[simp] theorem pointwiseContinuousMap_ρ_apply (B : TopRep.{w} k H)
    (h : H) (f : C(Q, B)) (q : Q) :
    ((pointwiseContinuousMap Q B).ρ h f : C(Q, B)) q = B.ρ h (f q) := rfl

/-- Constant functions retain the original, possibly nontrivial, coefficient
action. This is not coinduction's translation of the index. -/
@[simp] theorem pointwiseContinuousMap_ρ_const (B : TopRep.{w} k H)
    (h : H) (b : B) (q : Q) :
    ((pointwiseContinuousMap Q B).ρ h (ContinuousMap.const Q b) : C(Q, B)) q =
      B.ρ h b := rfl

/-- Coefficient maps act on pointwise function representations by postcomposition. -/
def pointwiseContinuousMapMap {B D : TopRep.{w} k H} (f : B ⟶ D) :
    pointwiseContinuousMap Q B ⟶ pointwiseContinuousMap Q D :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      ContinuousLinearMap.compLeftContinuous k Q f.hom.toContinuousLinearMap
    isIntertwining' h := by
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousMap.ext
      intro q
      change f.hom (B.ρ h (v q)) = D.ρ h (f.hom (v q))
      exact f.hom.isIntertwining h (v q)
  }

@[simp] theorem pointwiseContinuousMapMap_apply {B D : TopRep.{w} k H}
    (f : B ⟶ D) (v : C(Q, B)) (q : Q) :
    ((pointwiseContinuousMapMap (Q := Q) f).hom v : C(Q, D)) q = f.hom (v q) := rfl

@[simp] theorem pointwiseContinuousMapMap_id (B : TopRep.{w} k H) :
    pointwiseContinuousMapMap (Q := Q) (𝟙 B) = 𝟙 (pointwiseContinuousMap Q B) := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousMap.ext
  intro q
  rfl

@[simp] theorem pointwiseContinuousMapMap_comp {B D E : TopRep.{w} k H}
    (f : B ⟶ D) (g : D ⟶ E) :
    pointwiseContinuousMapMap (Q := Q) (f ≫ g) =
      pointwiseContinuousMapMap (Q := Q) f ≫ pointwiseContinuousMapMap (Q := Q) g := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousMap.ext
  intro q
  rfl

/-- A compact index and discrete coefficients make the entire compact-open
function space discrete. -/
instance pointwiseContinuousMap_discrete [CompactSpace Q]
    (B : TopRep.{w} k H) [DiscreteTopology B] :
    DiscreteTopology (pointwiseContinuousMap Q B) :=
  ContinuousMap.discreteTopology_of_compactSpace

/-- The pointwise action is jointly continuous when evaluation of compact-open
functions is continuous and the original action is jointly continuous. -/
theorem jointlyContinuous_pointwiseContinuousMap [TopologicalSpace H]
    [LocallyCompactSpace Q] (B : TopRep.{w} k H)
    [JointlyContinuous B] : JointlyContinuous (pointwiseContinuousMap Q B) := by
  refine ⟨?_⟩
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hargs : Continuous (fun p : (H × C(Q, B)) × Q => (p.1.1, p.1.2 p.2)) :=
    continuous_fst.comp continuous_fst |>.prodMk
      (continuous_eval.comp (continuous_snd.comp continuous_fst |>.prodMk continuous_snd))
  exact JointlyContinuous.continuous_action.comp hargs

end TopRep

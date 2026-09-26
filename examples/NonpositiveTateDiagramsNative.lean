/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import ContinuousGroupCohomology.NonpositiveTateFunctoriality
import Mathlib.Data.ZMod.Basic

/-!
# Native client for finite deflation diagrams and nonpositive limits

These checks use the public categorical API for an algebraic coefficient
representation. The homological degree `n + 1` models Tate degree `-n-2`;
the other two diagrams are in degrees `-1` and `0`. The topologies below are
canonical module topologies, with no claim that stages are discrete or that
these limits compute a separately defined continuous Tate cohomology.
-/

open CategoryTheory CategoryTheory.Limits ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{u}}

example (A : Rep.{u} R G) (n : ℕ) (S : OpenNormalSubgroup G) :
    (finiteNegativeDeflationDiagram A (n + 1)).obj S =
      groupHomology (A.quotientToInvariants S.toSubgroup) (n + 1) := rfl

example (A : Rep.{u} R G) (S : OpenNormalSubgroup G) :
    (finiteNegativeOneDeflationDiagram A).obj S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact tateCohomology (A.quotientToInvariants S.toSubgroup) (-1)) := rfl

example (A : Rep.{u} R G) (S : OpenNormalSubgroup G) :
    (finiteZeroDeflationDiagram A).obj S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact tateCohomology (A.quotientToInvariants S.toSubgroup) 0) := rfl

example (A : Rep.{u} R G) (n : ℕ) (S T U : OpenNormalSubgroup G)
    (f : S ⟶ T) (g : T ⟶ U) :
    (finiteNegativeDeflationDiagram A (n + 1)).map f ≫
        (finiteNegativeDeflationDiagram A (n + 1)).map g =
          (finiteNegativeDeflationDiagram A (n + 1)).map (f ≫ g) ∧
    (finiteNegativeOneDeflationDiagram A).map f ≫
        (finiteNegativeOneDeflationDiagram A).map g =
          (finiteNegativeOneDeflationDiagram A).map (f ≫ g) ∧
    (finiteZeroDeflationDiagram A).map f ≫
        (finiteZeroDeflationDiagram A).map g =
          (finiteZeroDeflationDiagram A).map (f ≫ g) := by
  exact ⟨((finiteNegativeDeflationDiagram A (n + 1)).map_comp f g).symm,
    ((finiteNegativeOneDeflationDiagram A).map_comp f g).symm,
    ((finiteZeroDeflationDiagram A).map_comp f g).symm⟩

example (A : Rep.{u} R G) (n : ℕ) (S : OpenNormalSubgroup G) :
    (finiteNegativeDeflationDiagram A (n + 1)).map (𝟙 S) = 𝟙 _ ∧
    (finiteNegativeOneDeflationDiagram A).map (𝟙 S) = 𝟙 _ ∧
    (finiteZeroDeflationDiagram A).map (𝟙 S) = 𝟙 _ := by
  exact ⟨(finiteNegativeDeflationDiagram A (n + 1)).map_id S,
    (finiteNegativeOneDeflationDiagram A).map_id S,
    (finiteZeroDeflationDiagram A).map_id S⟩

example {A B : Rep.{u} R G} (h : A ⟶ B) (n : ℕ)
    (S : OpenNormalSubgroup G) :
    ((finiteNegativeDeflationDiagramFunctor (R := R) (G := G) (n + 1)).map h).app S =
      (groupHomology.functor R (G ⧸ S.toSubgroup) (n + 1)).map
        ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map h) := rfl

example {A B : Rep.{u} R G} (h : A ⟶ B) (S : OpenNormalSubgroup G) :
    ((finiteNegativeOneDeflationDiagramFunctor (R := R) (G := G)).map h).app S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) (-1)).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map h)) := rfl

example {A B : Rep.{u} R G} (h : A ⟶ B) (S : OpenNormalSubgroup G) :
    ((finiteZeroDeflationDiagramFunctor (R := R) (G := G)).map h).app S =
      (by
        let _ : Fintype (G ⧸ S.toSubgroup) := Fintype.ofFinite _
        exact (tateCohomologyFunctor (R := R) (G := G ⧸ S.toSubgroup) 0).map
          ((Rep.quotientToInvariantsFunctor R S.toSubgroup).map h)) := rfl

example (A : Rep.{u} R G) (n : ℕ) (S T : OpenNormalSubgroup G) (f : S ⟶ T) :
    negativeDeflationLimitProjection A (n + 1) S ≫
        (topologicalFiniteNegativeDeflationDiagram A (n + 1)).map f =
      negativeDeflationLimitProjection A (n + 1) T ∧
    negativeOneDeflationLimitProjection A S ≫
        (topologicalFiniteNegativeOneDeflationDiagram A).map f =
      negativeOneDeflationLimitProjection A T ∧
    zeroDeflationLimitProjection A S ≫
        (topologicalFiniteZeroDeflationDiagram A).map f =
      zeroDeflationLimitProjection A T := by
  exact ⟨negativeDeflationLimitProjection_naturality A (n + 1) f,
    negativeOneDeflationLimitProjection_naturality A f,
    zeroDeflationLimitProjection_naturality A f⟩

example {A B : Rep.{u} R G} (h : A ⟶ B) (n : ℕ)
    (S : OpenNormalSubgroup G) :
    (negativeDeflationLimitFunctor (R := R) (G := G) (n + 1)).map h ≫
        negativeDeflationLimitProjection B (n + 1) S =
      negativeDeflationLimitProjection A (n + 1) S ≫
        ((topologicalFiniteNegativeDeflationDiagramFunctor
          (R := R) (G := G) (n + 1)).map h).app S ∧
    (negativeOneDeflationLimitFunctor (R := R) (G := G)).map h ≫
        negativeOneDeflationLimitProjection B S =
      negativeOneDeflationLimitProjection A S ≫
        ((topologicalFiniteNegativeOneDeflationDiagramFunctor
          (R := R) (G := G)).map h).app S ∧
    (zeroDeflationLimitFunctor (R := R) (G := G)).map h ≫
        zeroDeflationLimitProjection B S =
      zeroDeflationLimitProjection A S ≫
        ((topologicalFiniteZeroDeflationDiagramFunctor
          (R := R) (G := G)).map h).app S := by
  exact ⟨negativeDeflationLimitFunctor_map_projection h (n + 1) S,
    negativeOneDeflationLimitFunctor_map_projection h S,
    zeroDeflationLimitFunctor_map_projection h S⟩

private def binaryProfinite : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2)))

private def binaryTrivial : OpenNormalSubgroup binaryProfinite :=
  { toOpenSubgroup :=
      { toSubgroup := ⊥
        isOpen' := by
          let _ : DiscreteTopology binaryProfinite := ⟨rfl⟩
          exact isOpen_discrete _ }
    isNormal' := inferInstance }

private def binaryTotal : OpenNormalSubgroup binaryProfinite :=
  { toOpenSubgroup :=
      { toSubgroup := ⊤
        isOpen' := isOpen_univ }
    isNormal' := inferInstance }

private theorem binaryTrivial_lt_total : binaryTrivial < binaryTotal := by
  apply lt_of_le_of_ne
  · intro element membership
    exact Subgroup.mem_top element
  · intro equality
    have h : (⊥ : Subgroup binaryProfinite) = ⊤ := by
      have lifted := congrArg
        (fun subgroup : OpenNormalSubgroup binaryProfinite => subgroup.toSubgroup) equality
      exact lifted
    let _ : Nontrivial binaryProfinite := by
      change Nontrivial (Multiplicative (ZMod 2))
      infer_instance
    exact bot_ne_top h

example {R : Type} [CommRing R] [TopologicalSpace R]
    (A : Rep R binaryProfinite) (n : ℕ) :
    (finiteNegativeDeflationDiagram A (n + 1)).map
        (homOfLE binaryTrivial_lt_total.le) =
      (by
        let _ : Fintype
            (binaryTotal.toSubgroup.map (QuotientGroup.mk' binaryTrivial.toSubgroup)) :=
          Fintype.ofFinite _
        exact finiteNegativeDeflation A binaryTrivial.toSubgroup binaryTotal.toSubgroup
          binaryTrivial_lt_total.le (n + 1)) := by
  let _ : Fintype
      (binaryTotal.toSubgroup.map (QuotientGroup.mk' binaryTrivial.toSubgroup)) :=
    Fintype.ofFinite _
  rfl

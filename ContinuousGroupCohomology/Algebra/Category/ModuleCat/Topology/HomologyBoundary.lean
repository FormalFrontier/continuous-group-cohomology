/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Homology

@[expose] public section

/-!
# Boundaries and zero homology classes in topological modules

The homology of a short complex in `TopModuleCat` is a cokernel of the map into
cycles. Its zero classes are exactly actual algebraic boundaries, without
separation or closed-range hypotheses.
-/

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits

universe u v

namespace TopModuleCat

variable {k : Type u} [Ring k] [TopologicalSpace k]

/-- A cycle represents zero in topological-module homology exactly when it is
in the algebraic range of the boundary map into cycles. -/
theorem shortComplex_homologyπ_eq_zero_iff
    (S : ShortComplex (TopModuleCat.{v} k)) (z : S.cycles) :
    S.homologyπ.hom z = 0 ↔ ∃ w : S.X₁, S.toCycles.hom w = z := by
  let comparison := S.descHomology (cokerπ S.toCycles) (comp_cokerπ S.toCycles)
  have hcomparison : S.homologyπ ≫ comparison = cokerπ S.toCycles :=
    S.π_descHomology _ _
  constructor
  · intro hz
    have hq : (cokerπ S.toCycles).hom z = 0 := by
      have h := congrArg comparison.hom hz
      simpa only [← hcomparison, ConcreteCategory.comp_apply, map_zero] using h
    change Submodule.mkQ S.toCycles.hom.range z = 0 at hq
    have hrange : z ∈ S.toCycles.hom.range :=
      (Submodule.Quotient.mk_eq_zero _).mp hq
    exact hrange
  · rintro ⟨w, rfl⟩
    have h := congrArg (fun f : S.X₁ ⟶ S.homology => f.hom w)
      S.toCycles_comp_homologyπ
    simpa only [ConcreteCategory.comp_apply, hom_zero_apply] using h

end TopModuleCat

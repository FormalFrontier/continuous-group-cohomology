/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientTransitions

/-!
# Ordinary-import tests of native quotient-stage transitions

The stages, cochain, cohomology class and degree are arbitrary. No zero-class,
finite-coefficient, compactness or joint-continuity hypothesis is used.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

universe u v w

open CategoryTheory TopRep

namespace CGCExamples.ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)
variable {N M L : OpenNormalSubgroup G} (hNM : N ≤ M) (hML : M ≤ L) (n : ℕ)

private theorem composite_cochain
    (σ : (TopRep.homogeneousCochains
      (TopRep.quotientInvariants L.toSubgroup X)).X n) :
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.quotientTransitionHom N L (hNM.trans hML))
      (ContinuousCohomology.quotientTransitionIncl X (hNM.trans hML))).f n) σ =
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.quotientTransitionHom N M hNM)
      (ContinuousCohomology.quotientTransitionIncl X hNM)).f n)
      (((ContinuousCohomology.cochainsMap
        (ContinuousCohomology.quotientTransitionHom M L hML)
        (ContinuousCohomology.quotientTransitionIncl X hML)).f n) σ) := by
  rw [ContinuousCohomology.quotientTransition_cochainsMap_comp X hNM hML]
  rfl

private theorem composite_class
    (a : continuousCohomology n
      (TopRep.quotientInvariants L.toSubgroup X)) :
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom N L (hNM.trans hML))
      (ContinuousCohomology.quotientTransitionIncl X (hNM.trans hML)) n).hom a =
    (ContinuousCohomology.map
      (ContinuousCohomology.quotientTransitionHom N M hNM)
      (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom
      ((ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom M L hML)
        (ContinuousCohomology.quotientTransitionIncl X hML) n).hom a) := by
  rw [ContinuousCohomology.quotientTransition_map_comp X hNM hML n]
  rfl

private theorem inflation_triangle_cochain
    (σ : (TopRep.homogeneousCochains
      (TopRep.quotientInvariants M.toSubgroup X)).X n) :
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X)).f n) σ =
    ((ContinuousCohomology.cochainsMap
      (ContinuousCohomology.openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X)).f n)
      (((ContinuousCohomology.cochainsMap
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM)).f n) σ) := by
  rw [ContinuousCohomology.quotientTransition_cochainsMap_inflate X hNM]
  rfl

private theorem inflation_triangle_class
    (a : continuousCohomology n
      (TopRep.quotientInvariants M.toSubgroup X)) :
    (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom M)
      (TopRep.quotientInvariantsIncl M.toSubgroup X) n).hom a =
    (ContinuousCohomology.map (ContinuousCohomology.openNormalQuotientHom N)
      (TopRep.quotientInvariantsIncl N.toSubgroup X) n).hom
      ((ContinuousCohomology.map
        (ContinuousCohomology.quotientTransitionHom N M hNM)
        (ContinuousCohomology.quotientTransitionIncl X hNM) n).hom a) := by
  rw [ContinuousCohomology.quotientTransition_map_inflate X hNM n]
  rfl

end CGCExamples.ContinuousCohomology

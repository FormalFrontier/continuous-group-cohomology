/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CochainInjectivity
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Injective cochain maps for a quotient group with nonsurjective coefficients

Surjective continuous group homomorphisms and injective coefficient maps induce
injective maps on homogeneous cochains and cocycles, and reflect vanishing of a
cochain differential. For quotient groups, the inclusion `ℤ → ℤ × ℤ`, `z ↦ (z, 0)`,
between trivial representations has `(0, 1)` outside its image. Nevertheless, its
degree-zero cochain map and degree-two cocycle map are injective, and its degree-two
cochain map reflects vanishing of the differential. This does not imply injectivity
on cohomology.

The quotient map, coefficient inclusion, and their surjectivity and injectivity
boundaries work for groups in any universe. The cochain and cocycle instances use
groups in `Type`: the recursive coinduced resolution retains the coefficient
carrier universe, while `ℤ` is in `Type`.
-/

@[expose] public section

universe u v

open CategoryTheory TopRep ContRepresentation

namespace IncubatorTest.ContinuousCohomology

variable {k : Type u} {G H : Type v} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep k G} {Y : TopRep k H}
  (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y)
  (hφ : Function.Surjective φ) (hf : Function.Injective f.hom)

include hφ hf in
private theorem everyResolutionLevel (i : ℕ) :
    Function.Injective (ContinuousCohomology.resolutionMap φ f i).hom :=
  ContinuousCohomology.resolutionMap_injective φ f hφ hf i

include hφ hf in
private theorem degreeZero : Function.Injective ((ContinuousCohomology.cochainsMap φ f).f 0) :=
  ContinuousCohomology.cochainsMap_injective φ f hφ hf 0

include hφ hf in
private theorem degreeTwo : Function.Injective ((ContinuousCohomology.cochainsMap φ f).f 2) :=
  ContinuousCohomology.cochainsMap_injective φ f hφ hf 2

include hφ hf in
private theorem everyCocycleDegree (n : ℕ) :
    Function.Injective (ContinuousCohomology.cocyclesMap φ f n) :=
  ContinuousCohomology.cocyclesMap_injective φ f hφ hf n

include hφ hf in
private theorem reflectsDifferential (n : ℕ) (σ : (homogeneousCochains X).X n) :
    (homogeneousCochains Y).d n (n + 1)
      ((ContinuousCohomology.cochainsMap φ f).f n σ) = 0 ↔
      (homogeneousCochains X).d n (n + 1) σ = 0 :=
  ContinuousCohomology.cochainsMap_d_eq_zero_iff φ f hφ hf n σ

end IncubatorTest.ContinuousCohomology

namespace CGCExamples.QuotientCochains

section Maps

universe w

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

/-- The continuous quotient homomorphism associated to a normal subgroup. -/
def quotientMap : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

omit [IsTopologicalGroup G] in
@[simp]
theorem quotientMap_apply (g : G) : quotientMap N g = QuotientGroup.mk g := rfl

/-- The inclusion `ℤ → ℤ × ℤ`, `z ↦ (z, 0)`, between trivial representations,
restricted along the quotient homomorphism. -/
def coefficientInclusion :
    TopRep.res (quotientMap N) (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ)) ⟶
      TopRep.of (ContRepresentation.trivial ℤ G (ℤ × ℤ)) :=
  TopRep.ofHom ⟨ContinuousLinearMap.inl ℤ ℤ ℤ, by
    intro g
    ext <;> simp [ContRepresentation.trivial_apply, ContinuousLinearMap.inl_apply]⟩

omit [IsTopologicalGroup G] in
@[simp]
theorem coefficientInclusion_apply (z : ℤ) : (coefficientInclusion N).hom z = (z, 0) := rfl

omit [IsTopologicalGroup G] in
/-- Every quotient class is in the image of the continuous quotient homomorphism. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap N) := by
  intro q
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q
  exact ⟨g, by simpa only [quotientMap_apply] using hg⟩

omit [IsTopologicalGroup G] in
/-- The first-coordinate inclusion of coefficient modules is injective. -/
theorem coefficientInclusion_injective :
    Function.Injective (coefficientInclusion N).hom := by
  intro a b hab
  exact congrArg Prod.fst hab

omit [IsTopologicalGroup G] in
/-- The coefficient inclusion is not surjective: `(0, 1)` cannot equal `(z, 0)`. -/
theorem coefficientInclusion_not_surjective :
    ¬ Function.Surjective (coefficientInclusion N).hom := by
  intro hs
  obtain ⟨a, ha⟩ := hs (0, 1)
  have h : (0 : ℤ) = 1 := congrArg Prod.snd ha
  exact zero_ne_one h

end Maps

section Cochains

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

/-- The cochain map in degree zero is injective, despite the failure of coefficient
surjectivity. -/
theorem cochainsMap_injective_zero :
    Function.Injective ((ContinuousCohomology.cochainsMap
      (quotientMap N) (coefficientInclusion N)).f 0) :=
  ContinuousCohomology.cochainsMap_injective
    (quotientMap N) (coefficientInclusion N) (quotientMap_surjective N)
    (coefficientInclusion_injective N) 0

/-- The cocycle map in degree two is injective for the same nonsurjective
coefficient inclusion. -/
theorem cocyclesMap_injective_two :
    Function.Injective (ContinuousCohomology.cocyclesMap
      (quotientMap N) (coefficientInclusion N) 2) :=
  ContinuousCohomology.cocyclesMap_injective
    (quotientMap N) (coefficientInclusion N) (quotientMap_surjective N)
    (coefficientInclusion_injective N) 2

/-- In degree two, the cochain map reflects the property of being a cocycle. -/
theorem cochainsMap_d_eq_zero_iff_two (σ :
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ))).X 2) :
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ G (ℤ × ℤ)))).d 2 3
      ((ContinuousCohomology.cochainsMap (quotientMap N) (coefficientInclusion N)).f 2 σ) = 0 ↔
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ))).d 2 3 σ = 0 :=
  ContinuousCohomology.cochainsMap_d_eq_zero_iff
    (quotientMap N) (coefficientInclusion N) (quotientMap_surjective N)
    (coefficientInclusion_injective N) 2 σ

end Cochains

end CGCExamples.QuotientCochains

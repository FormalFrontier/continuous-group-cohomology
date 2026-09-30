module

public import ContinuousGroupCohomology.CochainInjectivity
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Ordinary-import clients for native continuous cochain injection

These clients exercise arbitrary topological representations over an arbitrary ring,
the first and third levels of the resolution, and a genuine quotient-group map
with an injective coefficient morphism that is not surjective.
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

namespace IncubatorTest.ContinuousCohomology.QuotientClient

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

private def quotientMap : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

private def coefficientInclusion :
    TopRep.res (quotientMap N) (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ)) ⟶
      TopRep.of (ContRepresentation.trivial ℤ G (ℤ × ℤ)) :=
  TopRep.ofHom ⟨ContinuousLinearMap.inl ℤ ℤ ℤ, by
    intro g
    ext <;> simp [ContRepresentation.trivial_apply, ContinuousLinearMap.inl_apply]⟩

omit [IsTopologicalGroup G] in
private theorem coefficientInclusion_injective :
    Function.Injective (coefficientInclusion N).hom := by
  intro a b hab
  exact congrArg Prod.fst hab

omit [IsTopologicalGroup G] in
private theorem coefficientInclusion_not_surjective :
    ¬ Function.Surjective (coefficientInclusion N).hom := by
  intro hs
  obtain ⟨a, ha⟩ := hs (0, 1)
  have h : (0 : ℤ) = 1 := congrArg Prod.snd ha
  exact zero_ne_one h

private theorem quotientDegreeZero :
    Function.Injective ((ContinuousCohomology.cochainsMap
      (quotientMap N) (coefficientInclusion N)).f 0) :=
  ContinuousCohomology.cochainsMap_injective
    (quotientMap N) (coefficientInclusion N) QuotientGroup.mk_surjective
    (coefficientInclusion_injective N) 0

private theorem quotientDegreeTwoCocycles :
    Function.Injective (ContinuousCohomology.cocyclesMap
      (quotientMap N) (coefficientInclusion N) 2) :=
  ContinuousCohomology.cocyclesMap_injective
    (quotientMap N) (coefficientInclusion N) QuotientGroup.mk_surjective
    (coefficientInclusion_injective N) 2

private theorem quotientDegreeTwoReflects (σ :
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ))).X 2) :
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ G (ℤ × ℤ)))).d 2 3
      ((ContinuousCohomology.cochainsMap (quotientMap N) (coefficientInclusion N)).f 2 σ) = 0 ↔
    (homogeneousCochains (TopRep.of (ContRepresentation.trivial ℤ (G ⧸ N) ℤ))).d 2 3 σ = 0 :=
  ContinuousCohomology.cochainsMap_d_eq_zero_iff
    (quotientMap N) (coefficientInclusion N) QuotientGroup.mk_surjective
    (coefficientInclusion_injective N) 2 σ

end IncubatorTest.ContinuousCohomology.QuotientClient

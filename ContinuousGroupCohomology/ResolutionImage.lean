module

public import ContinuousGroupCohomology.QuotientInvariants
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.Algebra.OpenSubgroup

set_option warningAsError true

/-!
# Images of continuous resolutions over open normal quotients

The image of inflation at a fixed resolution level consists exactly of cochains whose
values descend recursively, with invariance at the bottom and right-coset constancy
at every positive level. Openness makes the quotient discrete, so choosing lifts
pointwise produces a continuous outer cochain without a topology assumption on
the coefficient representation.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (X : TopRep.{max v w} k G)

/-- The continuous quotient homomorphism attached to an open normal subgroup. -/
def openNormalQuotientHom (N : OpenNormalSubgroup G) :
    G →ₜ* G ⧸ N.toSubgroup :=
  ⟨QuotientGroup.mk' N.toSubgroup, QuotientGroup.continuous_mk⟩

/-- A cochain descends at a resolution level when its bottom values are fixed by `N`
and each higher continuous function is right-`N`-constant with descending values. -/
def StageDescends (N : OpenNormalSubgroup G) :
    (i : ℕ) → TopRep.resolutionX X i → Prop
  | 0, x => x ∈ (X.ρ.restrict N.toSubgroup.subtype).invariants
  | i + 1, F =>
      (∀ g : G, StageDescends N i (F g)) ∧
        (∀ (g : G) (t : N.toSubgroup), F (g * t.1) = F g)

@[simp] theorem stageDescends_zero (N : OpenNormalSubgroup G) (x : X) :
    StageDescends X N 0 x ↔
      x ∈ (X.ρ.restrict N.toSubgroup.subtype).invariants := Iff.rfl

@[simp] theorem stageDescends_succ (N : OpenNormalSubgroup G) (i : ℕ)
    (F : TopRep.resolutionX X (i + 1)) :
    StageDescends X N (i + 1) F ↔
      (∀ g : G, StageDescends X N i (F g)) ∧
        (∀ (g : G) (t : N.toSubgroup), F (g * t.1) = F g) := Iff.rfl

/-- Enlarging the open normal subgroup strengthens the descent condition. -/
theorem stageDescends_antitone {N M : OpenNormalSubgroup G} (h : N ≤ M)
    (i : ℕ) (a : TopRep.resolutionX X i) :
    StageDescends X M i a → StageDescends X N i a := by
  induction i with
  | zero =>
    intro ha t
    exact ha ⟨t.1, h t.2⟩
  | succ i ih =>
    rintro ⟨hvalues, hcoset⟩
    constructor
    · intro g
      exact ih (a g) (hvalues g)
    · intro g t
      exact hcoset g ⟨t.1, h t.2⟩

/-- Recursive descent is exactly membership in the actual image of the native
resolution map from the quotient-invariant coefficient representation. -/
theorem stageDescends_iff_exists_lift (N : OpenNormalSubgroup G) (i : ℕ)
    (a : TopRep.resolutionX X i) :
    StageDescends X N i a ↔
      ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) i,
        (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom b = a := by
  induction i with
  | zero =>
    constructor
    · intro ha
      exact ⟨⟨a, ha⟩, rfl⟩
    · rintro ⟨b, hb⟩
      change b.1 = a at hb
      rw [← hb]
      exact b.2
  | succ i ih =>
    constructor
    · intro ha
      classical
      have hdiscrete : DiscreteTopology (G ⧸ N.toSubgroup) :=
        QuotientGroup.discreteTopology N.isOpen'
      let representative : G ⧸ N.toSubgroup → G :=
        fun quotient => Classical.choose (QuotientGroup.mk'_surjective N.toSubgroup quotient)
      have representative_spec (quotient : G ⧸ N.toSubgroup) :
          openNormalQuotientHom N (representative quotient) = quotient :=
        Classical.choose_spec (QuotientGroup.mk'_surjective N.toSubgroup quotient)
      have value_lift (quotient : G ⧸ N.toSubgroup) :
          ∃ b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) i,
            (resolutionMap (openNormalQuotientHom N)
              (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom b =
              a (representative quotient) :=
        (ih (a (representative quotient))).mp (ha.1 (representative quotient))
      let b : TopRep.resolutionX (TopRep.quotientInvariants N.toSubgroup X) (i + 1) :=
        ⟨fun quotient => Classical.choose (value_lift quotient),
          @continuous_of_discreteTopology _ _ hdiscrete _ _ _⟩
      refine ⟨b, ?_⟩
      apply ContinuousMap.ext
      intro g
      change (resolutionMap (openNormalQuotientHom N)
        (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom
          (b (openNormalQuotientHom N g)) = a g
      have hvalue := Classical.choose_spec (value_lift (openNormalQuotientHom N g))
      change (resolutionMap (openNormalQuotientHom N)
        (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom
          (b (openNormalQuotientHom N g)) =
          a (representative (openNormalQuotientHom N g)) at hvalue
      rw [hvalue]
      obtain ⟨t, ht, hmul⟩ := (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp
        (representative_spec (openNormalQuotientHom N g))
      calc
        a (representative (openNormalQuotientHom N g)) =
            a (representative (openNormalQuotientHom N g) * t) :=
          (ha.2 (representative (openNormalQuotientHom N g)) ⟨t, ht⟩).symm
        _ = a g := congrArg a hmul
    · rintro ⟨b, rfl⟩
      constructor
      · intro g
        exact (ih _).mpr ⟨b (openNormalQuotientHom N g), rfl⟩
      · intro g t
        change (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom
            (b (openNormalQuotientHom N (g * t.1))) =
          (resolutionMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) i).hom
            (b (openNormalQuotientHom N g))
        have hquotient : openNormalQuotientHom N (g * t.1) =
            openNormalQuotientHom N g :=
          (QuotientGroup.mk'_eq_mk' N.toSubgroup).mpr
            ⟨t.1⁻¹, N.inv_mem t.2, by group⟩
        rw [hquotient]

end ContinuousCohomology

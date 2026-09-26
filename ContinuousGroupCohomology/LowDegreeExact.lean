/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.DegreeOne

/-!
# Low-degree exact sequences for split topological coefficients

This file begins the explicit degree-zero/one exact-sequence construction for
continuous group cohomology.  The splitting data are continuous linear maps,
but are deliberately not required to be equivariant for the group action.
The connecting map and degree-one exactness use this nonequivariant splitting.
-/

public section

open CategoryTheory

universe u v w

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G]
variable {A B C : TopRep.{max v w} k G}

/-- A short exact sequence of topological representations equipped with
continuous linear splitting data on the underlying topological modules.

The retraction and section need not commute with the `G`-actions.  Requiring
them to be equivariant would make the low-degree connecting map trivial. -/
structure TopologicallySplitShortExact
    (A B C : TopRep.{max v w} k G) where
  /-- The equivariant inclusion of the kernel coefficient. -/
  i : A ⟶ B
  /-- The equivariant projection to the quotient coefficient. -/
  p : B ⟶ C
  /-- Exactness of the underlying sequence. -/
  exact : Function.Exact i p
  /-- Injectivity at the left endpoint. -/
  injective_i : Function.Injective i
  /-- Surjectivity at the right endpoint. -/
  surjective_p : Function.Surjective p
  /-- A continuous linear retraction of `i`, not necessarily equivariant. -/
  retract : B →L[k] A
  /-- The retraction is a left inverse to `i`. -/
  retract_i : ∀ a, retract (i a) = a
  /-- A continuous linear section of `p`, not necessarily equivariant. -/
  section_ : C →L[k] B
  /-- The section is a right inverse to `p`. -/
  p_section : ∀ c, p (section_ c) = c

namespace TopologicallySplitShortExact

variable (S : TopologicallySplitShortExact A B C)

@[simp]
lemma p_i (a : A) : S.p (S.i a) = 0 :=
  (S.exact (S.i a)).2 ⟨a, rfl⟩

@[simp]
lemma retract_i_apply (a : A) : S.retract (S.i a) = a :=
  S.retract_i a

@[simp]
lemma p_section_apply (c : C) : S.p (S.section_ c) = c :=
  S.p_section c

/-- On the kernel of `p`, applying the retraction and then `i` recovers the
original coefficient. -/
lemma i_retract_of_p_eq_zero {b : B} (hb : S.p b = 0) :
    S.i (S.retract b) = b := by
  rcases (S.exact b).1 hb with ⟨a, rfl⟩
  rw [retract_i_apply]

/-- Every element of the kernel of `p` has the canonical preimage supplied by
the chosen retraction. -/
lemma exists_eq_i_of_p_eq_zero {b : B} (hb : S.p b = 0) :
    ∃ a : A, S.i a = b :=
  ⟨S.retract b, S.i_retract_of_p_eq_zero hb⟩

/-- Any two underlying continuous-linear retractions of `i` agree on
`ker p`. -/
lemma retract_eq_on_ker (r : B →L[k] A) (hr : ∀ a, r (S.i a) = a)
    {b : B} (hb : S.p b = 0) :
    r b = S.retract b := by
  rw [← S.i_retract_of_p_eq_zero hb, hr, retract_i_apply]

/-- Replace the chosen underlying retraction without changing the exact
coefficient sequence. -/
def withRetract (r : B →L[k] A) (hr : ∀ a, r (S.i a) = a) :
    TopologicallySplitShortExact A B C :=
  { S with retract := r, retract_i := hr }

/-- Replace the chosen underlying section without changing the exact
coefficient sequence. -/
def withSection (s : C →L[k] B) (hs : ∀ c, S.p (s c) = c) :
    TopologicallySplitShortExact A B C :=
  { S with section_ := s, p_section := hs }

/-- A morphism of topologically split short exact sequences.  Compatibility
is required only for the equivariant coefficient maps, not for the chosen
underlying splittings. -/
structure Hom {A' B' C' : TopRep.{max v w} k G}
    (T : TopologicallySplitShortExact A' B' C') where
  /-- The map on kernel coefficients. -/
  a : A ⟶ A'
  /-- The map on middle coefficients. -/
  b : B ⟶ B'
  /-- The map on quotient coefficients. -/
  c : C ⟶ C'
  i_comm : S.i ≫ b = a ≫ T.i
  p_comm : S.p ≫ c = b ≫ T.p

namespace Hom

variable {A' B' C' : TopRep.{max v w} k G}
variable {T : TopologicallySplitShortExact A' B' C'}

@[simp]
lemma i_comm_apply (F : S.Hom T) (a : A) :
    F.b (S.i a) = T.i (F.a a) :=
  ConcreteCategory.congr_hom F.i_comm a

@[simp]
lemma p_comm_apply (F : S.Hom T) (b : B) :
    F.c (S.p b) = T.p (F.b b) :=
  ConcreteCategory.congr_hom F.p_comm b

end Hom

/-- The inclusion induced on invariant coefficients.
The application formula computes using the underlying equivariant inclusion. -/
@[expose]
def invariantsInclusion : A.ρ.invariants →L[k] B.ρ.invariants :=
  S.i.hom.mapInvariants

/-- The projection induced on invariant coefficients.
The application formula computes using the underlying equivariant projection. -/
@[expose]
def invariantsProjection : B.ρ.invariants →L[k] C.ρ.invariants :=
  S.p.hom.mapInvariants

@[simp]
lemma invariantsInclusion_apply (a : A.ρ.invariants) :
    S.invariantsInclusion a = S.i a := rfl

@[simp]
lemma invariantsProjection_apply (b : B.ρ.invariants) :
    S.invariantsProjection b = S.p b := rfl

/-- Exactness of the invariant-coefficient sequence at the middle term. -/
lemma exact_invariantsInclusion_invariantsProjection :
    Function.Exact S.invariantsInclusion S.invariantsProjection := by
  apply Function.Exact.of_comp_of_mem_range
  · funext a
    apply Subtype.ext
    exact S.p_i a
  · intro b hb
    have hb' : S.p b = 0 := by
      simpa using congrArg Subtype.val hb
    have ha : S.retract b ∈ A.ρ.invariants := by
      intro g
      apply S.injective_i
      rw [TopRep.hom_comm_apply, S.i_retract_of_p_eq_zero hb', b.2 g]
    exact ⟨⟨S.retract b, ha⟩,
      Subtype.ext (S.i_retract_of_p_eq_zero hb')⟩

section Connecting

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The chosen section, restricted to invariant quotient coefficients.
Its application evaluates the underlying continuous section. -/
@[expose]
def sectionOnInvariants : C.ρ.invariants →L[k] B :=
  S.section_.comp (Submodule.subtypeL C.ρ.invariants)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
lemma sectionOnInvariants_apply (c : C.ρ.invariants) :
    S.sectionOnInvariants c = S.section_ c := rfl

/-- The continuous `A`-valued function obtained by applying the retraction to
the principal defect of a chosen lift. Its application computes this defect. -/
@[expose]
def connectingRawMap [TopRep.JointlyContinuous B] :
    C.ρ.invariants →L[k] C(G, A) :=
  (S.retract.compLeftContinuous k G).comp <|
    (Submodule.subtypeL (continuousCrossedHom B)).comp <|
      (principalToCrossedL B).comp S.sectionOnInvariants

omit [IsTopologicalGroup G] in
@[simp]
lemma connectingRawMap_apply [TopRep.JointlyContinuous B]
    (c : C.ρ.invariants) (g : G) :
    S.connectingRawMap c g =
      S.retract (B.ρ g (S.section_ c) - S.section_ c) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma p_section_defect_eq_zero (c : C.ρ.invariants) (g : G) :
    S.p (B.ρ g (S.section_ c) - S.section_ c) = 0 := by
  rw [map_sub, TopRep.hom_comm_apply, p_section_apply, c.2 g, sub_self]

/-- The connecting construction before quotienting by principal crossed
homomorphisms. Its application computes the raw connecting cocycle. -/
@[expose]
def connectingCrossed [TopRep.JointlyContinuous B] :
    C.ρ.invariants →L[k] continuousCrossedHom A :=
  S.connectingRawMap.codRestrict (continuousCrossedHom A) fun c g h => by
    apply S.injective_i
    change S.i (S.retract (B.ρ (g * h) (S.section_ c) - S.section_ c)) =
      S.i (A.ρ g (S.retract (B.ρ h (S.section_ c) - S.section_ c)) +
        S.retract (B.ρ g (S.section_ c) - S.section_ c))
    rw [S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c (g * h)),
      map_add, TopRep.hom_comm_apply,
      S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c h),
      S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g)]
    rw [map_mul]
    change B.ρ g (B.ρ h (S.section_ c)) - S.section_ c =
      B.ρ g (B.ρ h (S.section_ c) - S.section_ c) +
        (B.ρ g (S.section_ c) - S.section_ c)
    rw [map_sub]
    abel

omit [IsTopologicalGroup G] in
@[simp]
lemma connectingCrossed_apply [TopRep.JointlyContinuous B]
    (c : C.ρ.invariants) (g : G) :
    (S.connectingCrossed c).1 g =
      S.retract (B.ρ g (S.section_ c) - S.section_ c) := rfl

omit [IsTopologicalGroup G] in
lemma connectingCrossed_withRetract [TopRep.JointlyContinuous B]
    (r : B →L[k] A) (hr : ∀ a, r (S.i a) = a) :
    (S.withRetract r hr).connectingCrossed = S.connectingCrossed := by
  ext c g
  change r (B.ρ g (S.section_ c) - S.section_ c) =
    S.retract (B.ρ g (S.section_ c) - S.section_ c)
  exact S.retract_eq_on_ker r hr (S.p_section_defect_eq_zero c g)

omit [IsTopologicalGroup G] in
lemma connectingCrossed_change_section [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (s : C →L[k] B)
    (hs : ∀ c, S.p (s c) = c) (c : C.ρ.invariants) :
    S.connectingCrossed c - (S.withSection s hs).connectingCrossed c =
      principalToCrossed A (S.retract (S.section_ c - s c)) := by
  ext g
  apply S.injective_i
  change S.i (S.retract (B.ρ g (S.section_ c) - S.section_ c) -
      S.retract (B.ρ g (s c) - s c)) =
    S.i (A.ρ g (S.retract (S.section_ c - s c)) -
      S.retract (S.section_ c - s c))
  rw [map_sub S.i.hom, map_sub S.i.hom, TopRep.hom_comm_apply]
  have hsection : S.p (S.section_ c - s c) = 0 := by
    rw [map_sub, p_section_apply, hs, sub_self]
  have hdefect (t : C →L[k] B) (ht : ∀ x, S.p (t x) = x) :
      ∀ h : G, S.p (B.ρ h (t c) - t c) = 0 := by
    intro h
    rw [map_sub, TopRep.hom_comm_apply, ht, c.2 h, sub_self]
  rw [S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g),
    S.i_retract_of_p_eq_zero (hdefect s hs g),
    S.i_retract_of_p_eq_zero hsection]
  change B.ρ g (S.section_ c) - S.section_ c - (B.ρ g (s c) - s c) =
    B.ρ g (S.section_ c - s c) - (S.section_ c - s c)
  rw [map_sub]
  abel

/-- The low-degree connecting map into continuous crossed homomorphisms modulo
principal crossed homomorphisms. Its application computes on representatives. -/
@[expose]
def connectingQuotient [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    C.ρ.invariants →L[k] (continuousCrossedHom A ⧸ principalCocycles A) :=
  (principalCocycles A).mkQL.comp S.connectingCrossed

omit [IsTopologicalGroup G] in
@[simp]
lemma connectingQuotient_apply [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (c : C.ρ.invariants) :
    S.connectingQuotient c =
      (principalCocycles A).mkQ (S.connectingCrossed c) := rfl

omit [IsTopologicalGroup G] in
lemma connectingQuotient_withRetract [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (r : B →L[k] A)
    (hr : ∀ a, r (S.i a) = a) :
    (S.withRetract r hr).connectingQuotient = S.connectingQuotient := by
  rw [connectingQuotient, connectingQuotient,
    connectingCrossed_withRetract]

omit [IsTopologicalGroup G] in
lemma connectingQuotient_withSection [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (s : C →L[k] B)
    (hs : ∀ c, S.p (s c) = c) :
    (S.withSection s hs).connectingQuotient = S.connectingQuotient := by
  ext c
  rw [connectingQuotient_apply, connectingQuotient_apply]
  symm
  apply (Submodule.Quotient.eq _).2
  change S.connectingCrossed c - (S.withSection s hs).connectingCrossed c ∈
    principalCocycles A
  rw [S.connectingCrossed_change_section s hs c]
  exact LinearMap.mem_range_self _ _

omit [IsTopologicalGroup G] in
/-- If an invariant quotient coefficient already has an invariant lift, its
connecting crossed homomorphism is principal. -/
lemma connectingCrossed_invariantsProjection [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (b : B.ρ.invariants) :
    S.connectingCrossed (S.invariantsProjection b) =
      principalToCrossed A
        (S.retract (S.section_ (S.p b) - b)) := by
  ext g
  apply S.injective_i
  change S.i (S.retract (B.ρ g (S.section_ (S.p b)) - S.section_ (S.p b))) =
    S.i (A.ρ g (S.retract (S.section_ (S.p b) - b)) -
      S.retract (S.section_ (S.p b) - b))
  have hlift : S.p (S.section_ (S.p b) - b) = 0 := by
    rw [map_sub, p_section_apply, sub_self]
  have hsectionDefect :
      S.p (B.ρ g (S.section_ (S.p b)) - S.section_ (S.p b)) = 0 := by
    rw [map_sub, TopRep.hom_comm_apply, p_section_apply,
      ← TopRep.hom_comm_apply, b.2 g, sub_self]
  rw [S.i_retract_of_p_eq_zero hsectionDefect,
    map_sub S.i.hom, TopRep.hom_comm_apply,
    S.i_retract_of_p_eq_zero hlift]
  rw [map_sub, b.2 g]
  abel

omit [IsTopologicalGroup G] in
/-- Exactness at the quotient-invariant term of the low-degree sequence. -/
lemma exact_invariantsProjection_connectingQuotient
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B] :
    Function.Exact S.invariantsProjection S.connectingQuotient := by
  apply Function.Exact.of_comp_of_mem_range
  · funext b
    change S.connectingQuotient (S.invariantsProjection b) = 0
    rw [connectingQuotient_apply,
      connectingCrossed_invariantsProjection]
    exact (Submodule.Quotient.mk_eq_zero (principalCocycles A)).2
      (LinearMap.mem_range_self _ _)
  · intro c hc
    rw [connectingQuotient_apply] at hc
    have hmem : S.connectingCrossed c ∈ principalCocycles A :=
      (Submodule.Quotient.mk_eq_zero (principalCocycles A)).1 hc
    change S.connectingCrossed c ∈ LinearMap.range (principalToCrossed A) at hmem
    rcases hmem with ⟨a, ha⟩
    have hdefect (g : G) :
        B.ρ g (S.section_ c) - S.section_ c =
          B.ρ g (S.i a) - S.i a := by
      have h := congrArg
        (fun f : continuousCrossedHom A => S.i (f.1 g)) ha
      change S.i (A.ρ g a - a) =
        S.i (S.retract (B.ρ g (S.section_ c) - S.section_ c)) at h
      rw [map_sub S.i.hom, TopRep.hom_comm_apply,
        S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g)] at h
      exact h.symm
    have hb : S.section_ c - S.i a ∈ B.ρ.invariants := by
      intro g
      rw [map_sub]
      have h := hdefect g
      apply (sub_eq_sub_iff_add_eq_add).2
      simpa [add_comm] using (sub_eq_sub_iff_add_eq_add).1 h
    refine ⟨⟨S.section_ c - S.i a, hb⟩, ?_⟩
    apply Subtype.ext
    rw [invariantsProjection_apply, map_sub, p_section_apply, p_i, sub_zero]

omit [IsTopologicalGroup G] in
/-- Exactness at the first crossed-homomorphism quotient. -/
lemma exact_connectingQuotient_crossedQuotientMap_i
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B] :
    Function.Exact S.connectingQuotient (crossedQuotientMap S.i) := by
  apply Function.Exact.of_comp_of_mem_range
  · funext c
    change crossedQuotientMap S.i (S.connectingQuotient c) = 0
    rw [connectingQuotient_apply, crossedQuotientMap_mk]
    apply (Submodule.Quotient.mk_eq_zero (principalCocycles B)).2
    change crossedMap S.i (S.connectingCrossed c) ∈
      LinearMap.range (principalToCrossed B)
    refine ⟨S.section_ c, ?_⟩
    ext g
    change B.ρ g (S.section_ c) - S.section_ c =
      S.i (S.retract (B.ρ g (S.section_ c) - S.section_ c))
    exact (S.i_retract_of_p_eq_zero
      (S.p_section_defect_eq_zero c g)).symm
  · intro z hz
    refine Submodule.Quotient.induction_on _ z ?_ hz
    intro f hf
    change crossedQuotientMap S.i ((principalCocycles A).mkQ f) = 0 at hf
    rw [crossedQuotientMap_mk] at hf
    have hmem : crossedMap S.i f ∈ principalCocycles B :=
      (Submodule.Quotient.mk_eq_zero (principalCocycles B)).1 hf
    change crossedMap S.i f ∈ LinearMap.range (principalToCrossed B) at hmem
    rcases hmem with ⟨b, hb⟩
    have hc : S.p b ∈ C.ρ.invariants := by
      intro g
      have h := congrArg
        (fun q : continuousCrossedHom B => S.p (q.1 g)) hb
      change S.p (B.ρ g b - b) = S.p (S.i (f.1 g)) at h
      rw [map_sub, TopRep.hom_comm_apply, p_i] at h
      exact sub_eq_zero.mp h
    let c : C.ρ.invariants := ⟨S.p b, hc⟩
    have hlift : S.p (S.section_ c - b) = 0 := by
      rw [map_sub, p_section_apply, sub_self]
    have hdifference :
        S.connectingCrossed c - f =
          principalToCrossed A (S.retract (S.section_ c - b)) := by
      ext g
      apply S.injective_i
      change S.i (S.retract (B.ρ g (S.section_ c) - S.section_ c) - f.1 g) =
        S.i (A.ρ g (S.retract (S.section_ c - b)) -
          S.retract (S.section_ c - b))
      rw [map_sub S.i.hom,
        S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g),
        map_sub S.i.hom, TopRep.hom_comm_apply,
        S.i_retract_of_p_eq_zero hlift]
      have h := congrArg (fun q : continuousCrossedHom B => q.1 g) hb
      change B.ρ g b - b = S.i (f.1 g) at h
      rw [map_sub]
      rw [← h]
      abel
    refine ⟨c, ?_⟩
    rw [connectingQuotient_apply]
    apply (Submodule.Quotient.eq (principalCocycles A)).2
    rw [hdifference]
    exact LinearMap.mem_range_self _ _

omit [IsTopologicalGroup G] in
/-- Exactness at the second crossed-homomorphism quotient. -/
lemma exact_crossedQuotientMap_i_crossedQuotientMap_p
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous C] :
    Function.Exact (crossedQuotientMap S.i) (crossedQuotientMap S.p) := by
  apply Function.Exact.of_comp_of_mem_range
  · funext z
    refine Submodule.Quotient.induction_on _ z ?_
    intro f
    change crossedQuotientMap S.p
      (crossedQuotientMap S.i ((principalCocycles A).mkQ f)) = 0
    rw [crossedQuotientMap_mk, crossedQuotientMap_mk]
    apply (Submodule.Quotient.mk_eq_zero (principalCocycles C)).2
    change crossedMap S.p (crossedMap S.i f) ∈
      LinearMap.range (principalToCrossed C)
    refine ⟨0, ?_⟩
    ext g
    change C.ρ g 0 - 0 = S.p (S.i (f.1 g))
    rw [S.p_i]
    simp
  · intro z hz
    refine Submodule.Quotient.induction_on _ z ?_ hz
    intro f hf
    change crossedQuotientMap S.p ((principalCocycles B).mkQ f) = 0 at hf
    rw [crossedQuotientMap_mk] at hf
    have hmem : crossedMap S.p f ∈ principalCocycles C :=
      (Submodule.Quotient.mk_eq_zero (principalCocycles C)).1 hf
    change crossedMap S.p f ∈ LinearMap.range (principalToCrossed C) at hmem
    rcases hmem with ⟨c, hc⟩
    let f' : continuousCrossedHom B :=
      f - principalToCrossed B (S.section_ c)
    have hp (g : G) : S.p (f'.1 g) = 0 := by
      have h := congrArg (fun q : continuousCrossedHom C => q.1 g) hc
      change C.ρ g c - c = S.p (f.1 g) at h
      change S.p (f.1 g - (B.ρ g (S.section_ c) - S.section_ c)) = 0
      rw [map_sub S.p.hom, map_sub S.p.hom,
        TopRep.hom_comm_apply, p_section_apply]
      exact sub_eq_zero.mpr h.symm
    let a : continuousCrossedHom A :=
      ⟨⟨fun g => S.retract (f'.1 g),
          S.retract.continuous.comp f'.1.continuous⟩, by
        intro g h
        apply S.injective_i
        rw [map_add S.i.hom, TopRep.hom_comm_apply]
        change S.i (S.retract (f'.1 (g * h))) =
          B.ρ g (S.i (S.retract (f'.1 h))) + S.i (S.retract (f'.1 g))
        rw [S.i_retract_of_p_eq_zero (hp (g * h)),
          S.i_retract_of_p_eq_zero (hp h),
          S.i_retract_of_p_eq_zero (hp g)]
        exact f'.2 g h⟩
    refine ⟨(principalCocycles A).mkQ a, ?_⟩
    rw [crossedQuotientMap_mk]
    apply (Submodule.Quotient.eq (principalCocycles B)).2
    have hia : crossedMap S.i a = f' := by
      ext g
      exact S.i_retract_of_p_eq_zero (hp g)
    rw [hia]
    change f' - f ∈ LinearMap.range (principalToCrossed B)
    refine ⟨-S.section_ c, ?_⟩
    change principalToCrossed B (-S.section_ c) =
      f - principalToCrossed B (S.section_ c) - f
    rw [map_neg]
    abel

omit [IsTopologicalGroup G] in
/-- The quotient-level connecting map is natural for morphisms of split short
exact sequences; the chosen underlying splittings need not be compatible. -/
lemma connectingQuotient_natural
    {A' B' C' : TopRep.{max v w} k G}
    (T : TopologicallySplitShortExact A' B' C') (F : S.Hom T)
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A'] [TopRep.JointlyContinuous B'] :
    (crossedQuotientMap F.a).comp S.connectingQuotient =
      T.connectingQuotient.comp F.c.hom.mapInvariants := by
  ext c
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    connectingQuotient_apply, crossedQuotientMap_mk,
    connectingQuotient_apply]
  let c' : C'.ρ.invariants := F.c.hom.mapInvariants c
  apply (Submodule.Quotient.eq (principalCocycles A')).2
  change crossedMap F.a (S.connectingCrossed c) -
      T.connectingCrossed c' ∈ LinearMap.range (principalToCrossed A')
  let d : A' := T.retract (F.b (S.section_ c) - T.section_ c')
  have hd : T.p (F.b (S.section_ c) - T.section_ c') = 0 := by
    rw [map_sub T.p.hom, ← F.p_comm_apply, p_section_apply,
      p_section_apply]
    change F.c c - F.c c = 0
    exact sub_self _
  refine ⟨d, ?_⟩
  ext g
  apply T.injective_i
  change T.i (A'.ρ g d - d) =
    T.i (F.a (S.retract (B.ρ g (S.section_ c) - S.section_ c)) -
      T.retract (B'.ρ g (T.section_ c') - T.section_ c'))
  rw [map_sub T.i.hom, TopRep.hom_comm_apply,
    T.i_retract_of_p_eq_zero hd, map_sub T.i.hom,
    ← F.i_comm_apply,
    S.i_retract_of_p_eq_zero (S.p_section_defect_eq_zero c g),
    T.i_retract_of_p_eq_zero (T.p_section_defect_eq_zero c' g),
    map_sub F.b.hom, TopRep.hom_comm_apply]
  rw [map_sub]
  abel

section Native

variable [LocallyCompactSpace G]

/-- The connecting map from invariant quotient coefficients to mathlib's
native first continuous cohomology object. Its application factors through
the crossed-homomorphism quotient. -/
@[expose]
noncomputable def connectingMap [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] :
    TopModuleCat.of k C.ρ.invariants ⟶ continuousCohomology 1 A :=
  TopModuleCat.ofHom S.connectingQuotient ≫ (degreeOneIso A).hom

@[simp]
lemma connectingMap_apply [TopRep.JointlyContinuous A]
    [TopRep.JointlyContinuous B] (c : C.ρ.invariants) :
    S.connectingMap.hom c = (degreeOneIso A).hom.hom (S.connectingQuotient c) :=
  rfl

/-- The native connecting map is natural for morphisms of topologically split
short exact sequences. -/
lemma connectingMap_natural
    {A' B' C' : TopRep.{max v w} k G}
    (T : TopologicallySplitShortExact A' B' C') (F : S.Hom T)
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous A'] [TopRep.JointlyContinuous B'] :
    TopModuleCat.ofHom F.c.hom.mapInvariants ≫ T.connectingMap =
      S.connectingMap ≫ map (ContinuousMonoidHom.id G) F.a 1 := by
  ext c
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    TopModuleCat.hom_ofHom]
  change (degreeOneIso A').hom.hom
      (T.connectingQuotient (F.c.hom.mapInvariants c)) =
    (map (ContinuousMonoidHom.id G) F.a 1).hom
      ((degreeOneIso A).hom.hom (S.connectingQuotient c))
  have hq := DFunLike.congr_fun (S.connectingQuotient_natural T F) c
  have hq' : crossedQuotientMap F.a (S.connectingQuotient c) =
      T.connectingQuotient (F.c.hom.mapInvariants c) := by
    simpa only [ContinuousLinearMap.comp_apply] using hq
  rw [← hq']
  exact ConcreteCategory.congr_hom (degreeOneIso_natural F.a)
    (S.connectingQuotient c)

/-- Exactness at the quotient-invariant term, with the connecting map valued
in mathlib's native first continuous cohomology object. -/
lemma exact_invariantsProjection_connectingMap
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B] :
    Function.Exact S.invariantsProjection S.connectingMap.hom := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := S.invariantsProjection.toLinearMap)
    (f₂₃ := S.connectingQuotient.toLinearMap)
    (g₁₂ := S.invariantsProjection.toLinearMap)
    (g₂₃ := S.connectingMap.hom.toLinearMap)
    (e₁ := LinearEquiv.refl k B.ρ.invariants)
    (e₂ := LinearEquiv.refl k C.ρ.invariants)
    (e₃ := (degreeOneIso A).toContinuousLinearEquiv.toLinearEquiv)
  · ext b
    rfl
  · ext c
    rfl
  · exact S.exact_invariantsProjection_connectingQuotient

/-- Exactness at the first native continuous-cohomology term. -/
lemma exact_connectingMap_map_i
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B] :
    Function.Exact S.connectingMap.hom
      (map (ContinuousMonoidHom.id G) S.i 1).hom := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := S.connectingQuotient.toLinearMap)
    (f₂₃ := (crossedQuotientMap S.i).toLinearMap)
    (g₁₂ := S.connectingMap.hom.toLinearMap)
    (g₂₃ := (map (ContinuousMonoidHom.id G) S.i 1).hom.toLinearMap)
    (e₁ := LinearEquiv.refl k C.ρ.invariants)
    (e₂ := (degreeOneIso A).toContinuousLinearEquiv.toLinearEquiv)
    (e₃ := (degreeOneIso B).toContinuousLinearEquiv.toLinearEquiv)
  · ext c
    rfl
  · ext z
    exact ConcreteCategory.congr_hom (degreeOneIso_natural S.i).symm
      ((principalCocycles A).mkQ z)
  · exact S.exact_connectingQuotient_crossedQuotientMap_i

/-- Exactness at the second native continuous-cohomology term. -/
lemma exact_map_i_map_p
    [TopRep.JointlyContinuous A] [TopRep.JointlyContinuous B]
    [TopRep.JointlyContinuous C] :
    Function.Exact (map (ContinuousMonoidHom.id G) S.i 1).hom
      (map (ContinuousMonoidHom.id G) S.p 1).hom := by
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (f₁₂ := (crossedQuotientMap S.i).toLinearMap)
    (f₂₃ := (crossedQuotientMap S.p).toLinearMap)
    (g₁₂ := (map (ContinuousMonoidHom.id G) S.i 1).hom.toLinearMap)
    (g₂₃ := (map (ContinuousMonoidHom.id G) S.p 1).hom.toLinearMap)
    (e₁ := (degreeOneIso A).toContinuousLinearEquiv.toLinearEquiv)
    (e₂ := (degreeOneIso B).toContinuousLinearEquiv.toLinearEquiv)
    (e₃ := (degreeOneIso C).toContinuousLinearEquiv.toLinearEquiv)
  · ext z
    exact ConcreteCategory.congr_hom (degreeOneIso_natural S.i).symm
      ((principalCocycles A).mkQ z)
  · ext z
    exact ConcreteCategory.congr_hom (degreeOneIso_natural S.p).symm
      ((principalCocycles B).mkQ z)
  · exact S.exact_crossedQuotientMap_i_crossedQuotientMap_p

end Native

end Connecting

end TopologicallySplitShortExact

end ContinuousCohomology

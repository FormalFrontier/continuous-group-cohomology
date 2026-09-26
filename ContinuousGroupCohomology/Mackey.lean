/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.Corestriction
public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Tactic.Group

/-!
# The degree-one Mackey formula

This file develops the double-coset infrastructure needed for a continuous
degree-one Mackey formula.  For a representative changed by `y = h * x * b`,
it identifies the stabilizer in the right-hand subgroup, computes the exact
principal-cocycle defect of conjugating a crossed homomorphism, and transports
the right transversal used by finite-index transfer.  It then descends the
resulting representative-independent summand to `H \ G / K` and forms its
finite sum.  Finally, it assembles compatible transversals, identifies the
quotient sum with restriction after corestriction, and compares each summand
with the native conjugation/restriction and corestriction maps on first
continuous cohomology.  These constructions use no normality hypothesis.
-/

set_option autoImplicit false
set_option warningAsError true

public section

open CategoryTheory

noncomputable section

universe u v w

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ContinuousCohomology

namespace CorestrictionTransversal

variable (X : TopRep.{max v w} k G)

omit [IsTopologicalGroup G] in
/-- Conjugating a crossed homomorphism by an element of its group changes it
by the negative of a principal crossed homomorphism, in the repository's
positive-principal convention. -/
lemma innerConjCrossed_formula (H : OpenSubgroup G)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (h a : H) :
    X.ρ ((h : G)⁻¹) (f.1 (h * a * h⁻¹)) =
      f.1 a -
        ((TopRep.res H.subtype X).ρ a
            (X.ρ ((h : G)⁻¹) (f.1 h)) -
          X.ρ ((h : G)⁻¹) (f.1 h)) := by
  let c : X := X.ρ ((h : G)⁻¹) (f.1 h)
  calc
    X.ρ ((h : G)⁻¹) (f.1 (h * a * h⁻¹)) =
        X.ρ ((h : G)⁻¹)
          (X.ρ (h : G) (f.1 (a * h⁻¹)) + f.1 h) := by
            rw [show h * a * h⁻¹ = h * (a * h⁻¹) by group, f.2]
            rfl
    _ = f.1 (a * h⁻¹) + c := by
      rw [map_add, rho_mul_apply]
      simp only [inv_mul_cancel, map_one]
      rfl
    _ = (X.ρ (a : G) (f.1 h⁻¹) + f.1 a) + c := by
      rw [f.2]
      rfl
    _ = (X.ρ (a : G) (-c) + f.1 a) + c := by
      rw [crossed_inv X]
    _ = f.1 a - (X.ρ (a : G) c - c) := by
      rw [map_neg]
      abel
    _ = _ := rfl

section ConjugateTransversal

variable {K : Type*} [Group K]

/-- Transport a right transversal across conjugation of its subgroup.
Its carrier condition computes in the conjugation equivalence. -/
@[expose]
def conjugateRightTransversal (L : Subgroup K) (T : L.RightTransversal)
    (b : K) : (L.comap (MulAut.conj b).toMonoidHom).RightTransversal := by
  let T' : Set K := {t | b * t ∈ (T : Set K)}
  refine ⟨T', Subgroup.isComplement_iff_existsUnique.mpr ?_⟩
  intro g
  let p := T.2.equiv (b * g)
  let l' : L.comap (MulAut.conj b).toMonoidHom :=
    ⟨b⁻¹ * (p.1 : K) * b, by
      change b * (b⁻¹ * (p.1 : K) * b) * b⁻¹ ∈ L
      have hb : b * (b⁻¹ * (p.1 : K) * b) * b⁻¹ = (p.1 : K) := by
        group
      rw [hb]
      exact p.1.2⟩
  let t' : T' := ⟨b⁻¹ * (p.2 : K), by
    change b * (b⁻¹ * (p.2 : K)) ∈ (T : Set K)
    simp only [mul_inv_cancel_left]
    exact p.2.2⟩
  refine ⟨(l', t'), ?_, ?_⟩
  · change (b⁻¹ * (p.1 : K) * b) * (b⁻¹ * (p.2 : K)) = g
    calc
      _ = b⁻¹ * ((p.1 : K) * (p.2 : K)) := by group
      _ = b⁻¹ * (b * g) := by rw [T.2.equiv_fst_mul_equiv_snd]
      _ = g := by group
  · rintro ⟨l₁, t₁⟩ h₁
    have hp : ((⟨b * (l₁ : K) * b⁻¹, l₁.2⟩ : L),
        (⟨b * (t₁ : K), t₁.2⟩ : ↥(T : Set K))) = p := by
      apply T.2.1
      calc
        (b * (l₁ : K) * b⁻¹) * (b * (t₁ : K)) =
            b * ((l₁ : K) * (t₁ : K)) := by group
        _ = b * g := by rw [h₁]
        _ = (p.1 : K) * (p.2 : K) :=
          (T.2.equiv_fst_mul_equiv_snd _).symm
    apply Prod.ext
    · apply Subtype.ext
      have hl := congrArg (fun q : L × ↥(T : Set K) => (q.1 : K)) hp
      change (l₁ : K) = b⁻¹ * (p.1 : K) * b
      rw [← hl]
      group
    · apply Subtype.ext
      have ht := congrArg (fun q : L × ↥(T : Set K) => (q.2 : K)) hp
      change (t₁ : K) = b⁻¹ * (p.2 : K)
      rw [← ht]
      group

/-- Multiplication by the conjugating element identifies the transported and
original right transversals. The equivalence computes on representatives. -/
@[expose]
def conjugateTransversalEquiv (L : Subgroup K) (T : L.RightTransversal)
    (b : K) :
    ↥(conjugateRightTransversal L T b : Set K) ≃ ↥(T : Set K) where
  toFun t := ⟨b * (t : K), t.2⟩
  invFun s := ⟨b⁻¹ * (s : K), by
    change b * (b⁻¹ * (s : K)) ∈ (T : Set K)
    simpa only [mul_inv_cancel_left] using s.2⟩
  left_inv t := by
    apply Subtype.ext
    simp only [inv_mul_cancel_left]
  right_inv s := by
    apply Subtype.ext
    simp only [mul_inv_cancel_left]

@[simp]
lemma conjugateTransversalEquiv_coe (L : Subgroup K) (T : L.RightTransversal)
    (b : K) (t : ↥(conjugateRightTransversal L T b : Set K)) :
    (conjugateTransversalEquiv L T b t : K) = b * (t : K) := rfl

/-- The factors for conjugated right transversals agree after conjugation. -/
lemma conjugateTransversal_factor (L : Subgroup K) (T : L.RightTransversal)
    (b : K) (t : ↥(conjugateRightTransversal L T b : Set K)) (g : K) :
    b * (factor (conjugateRightTransversal L T b) t g : K) * b⁻¹ =
      (factor T (conjugateTransversalEquiv L T b t) g : K) := by
  let T' := conjugateRightTransversal L T b
  let l' := factor T' t g
  let n' := next T' t g
  have hl : b * (l' : K) * b⁻¹ ∈ L := l'.2
  have hpair :
      ((⟨b * (l' : K) * b⁻¹, hl⟩ : L),
          conjugateTransversalEquiv L T b n') =
        (factor T (conjugateTransversalEquiv L T b t) g,
          next T (conjugateTransversalEquiv L T b t) g) := by
    apply T.2.1
    calc
      (b * (l' : K) * b⁻¹) *
          (conjugateTransversalEquiv L T b n' : K) =
          b * ((l' : K) * (n' : K)) := by
            rw [conjugateTransversalEquiv_coe]
            group
      _ = b * ((t : K) * g) := by rw [factor_mul_next]
      _ = (b * (t : K)) * g := by group
      _ = (conjugateTransversalEquiv L T b t : K) * g := by
        rw [conjugateTransversalEquiv_coe]
      _ = (factor T (conjugateTransversalEquiv L T b t) g : K) *
            (next T (conjugateTransversalEquiv L T b t) g : K) :=
        (factor_mul_next _ _ _).symm
  exact congrArg (fun p : L × ↥(T : Set K) => (p.1 : K)) hpair

/-- The next representatives for conjugated right transversals agree under the
transport equivalence. -/
lemma conjugateTransversal_next (L : Subgroup K) (T : L.RightTransversal)
    (b : K) (t : ↥(conjugateRightTransversal L T b : Set K)) (g : K) :
    conjugateTransversalEquiv L T b
        (next (conjugateRightTransversal L T b) t g) =
      next T (conjugateTransversalEquiv L T b t) g := by
  let T' := conjugateRightTransversal L T b
  let l' := factor T' t g
  let n' := next T' t g
  have hl : b * (l' : K) * b⁻¹ ∈ L := l'.2
  have hpair :
      ((⟨b * (l' : K) * b⁻¹, hl⟩ : L),
          conjugateTransversalEquiv L T b n') =
        (factor T (conjugateTransversalEquiv L T b t) g,
          next T (conjugateTransversalEquiv L T b t) g) := by
    apply T.2.1
    calc
      (b * (l' : K) * b⁻¹) *
          (conjugateTransversalEquiv L T b n' : K) =
          b * ((l' : K) * (n' : K)) := by
            rw [conjugateTransversalEquiv_coe]
            group
      _ = b * ((t : K) * g) := by rw [factor_mul_next]
      _ = (b * (t : K)) * g := by group
      _ = (conjugateTransversalEquiv L T b t : K) * g := by
        rw [conjugateTransversalEquiv_coe]
      _ = (factor T (conjugateTransversalEquiv L T b t) g : K) *
            (next T (conjugateTransversalEquiv L T b t) g : K) :=
        (factor_mul_next _ _ _).symm
  exact congrArg (fun p : L × ↥(T : Set K) => p.2) hpair

end ConjugateTransversal

/-- The subgroup of `K₀` stabilizing the right `H`-coset represented by `x`.
Its membership predicate computes in the open-stabilizer comparison. -/
@[expose]
def mackeyStabilizer (H K₀ : Subgroup G) (x : G) : Subgroup K₀ :=
  H.comap ((MulAut.conj x).toMonoidHom.comp K₀.subtype)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Changing a double-coset representative by `h * x * b` conjugates its
stabilizer by `b` inside the right-hand subgroup. -/
lemma mackeyStabilizer_mul_left_mul_right (H K₀ : Subgroup G) (x : G)
    (h : H) (b : K₀) :
    mackeyStabilizer H K₀ ((h : G) * x * (b : G)) =
      (mackeyStabilizer H K₀ x).comap (MulAut.conj b).toMonoidHom := by
  ext l
  change
    (((h : G) * x * (b : G)) * (l : G) *
          ((h : G) * x * (b : G))⁻¹ ∈ H) ↔
      (x * ((b : G) * (l : G) * (b : G)⁻¹) * x⁻¹ ∈ H)
  constructor
  · intro hl
    have heq :
        x * ((b : G) * (l : G) * (b : G)⁻¹) * x⁻¹ =
          (h : G)⁻¹ *
            (((h : G) * x * (b : G)) * (l : G) *
              ((h : G) * x * (b : G))⁻¹) * (h : G) := by
      group
    rw [heq]
    exact H.mul_mem (H.mul_mem (H.inv_mem h.2) hl) h.2
  · intro hl
    have heq :
        ((h : G) * x * (b : G)) * (l : G) *
            ((h : G) * x * (b : G))⁻¹ =
          (h : G) *
            (x * ((b : G) * (l : G) * (b : G)⁻¹) * x⁻¹) * (h : G)⁻¹ := by
      group
    rw [heq]
    exact H.mul_mem (H.mul_mem h.2 hl) (H.inv_mem h.2)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coefficient action in the conjugated transfer summand has the literal
order needed for finite reindexing. -/
lemma conjugateTransferSummand_formula (b s : G) (z : X) :
    X.ρ ((b⁻¹ * s)⁻¹) (X.ρ b⁻¹ z) = X.ρ s⁻¹ z := by
  rw [← mul_apply_eq_comp, ← map_mul X.ρ]
  congr 2
  group

/-- Conjugation by `x`, restricted to the right-hand open subgroup.
Its value computes when using stabilizer membership. -/
@[expose]
def mackeyConjugationHom (K : OpenSubgroup G) (x : G) : K →ₜ* G where
  toMonoidHom := (MulAut.conj x).toMonoidHom.comp K.subtype
  continuous_toFun :=
    (IsTopologicalGroup.continuous_conj x).comp continuous_subtype_val

/-- The open stabilizer in `K` of the right `H`-coset represented by `x`.
Its underlying subgroup computes as the Mackey stabilizer. -/
@[expose]
def mackeyOpenStabilizer (H K : OpenSubgroup G) (x : G) : OpenSubgroup K :=
  H.comap (mackeyConjugationHom K x) (mackeyConjugationHom K x).continuous

@[simp]
lemma mackeyOpenStabilizer_toSubgroup (H K : OpenSubgroup G) (x : G) :
    (mackeyOpenStabilizer H K x).toSubgroup =
      mackeyStabilizer H.toSubgroup K.toSubgroup x := rfl

/-- The Mackey stabilizer has finite index in `K` as soon as `H` has finite
index in the ambient group. -/
instance mackeyOpenStabilizerFiniteIndex (H K : OpenSubgroup G) (x : G)
    [H.toSubgroup.FiniteIndex] :
    (mackeyOpenStabilizer H K x).toSubgroup.FiniteIndex := by
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_top_right]
  have h := Subgroup.relIndex_comap_ne_zero
    (mackeyConjugationHom K x).toMonoidHom
    (J := H.toSubgroup) (K := (⊤ : Subgroup G))
    (by exact Subgroup.FiniteIndex.index_ne_zero)
  change
    (H.toSubgroup.comap (mackeyConjugationHom K x).toMonoidHom).relIndex ⊤ ≠ 0
  simpa only [Subgroup.comap_top] using h

/-- Local joint-continuity synthesis through restriction to `K` and then to a
Mackey stabilizer. -/
private instance jointlyContinuous_mackeyRes
    (H K : OpenSubgroup G) (x : G) [TopRep.JointlyContinuous X] :
    TopRep.JointlyContinuous
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X)) := by
  let _ : TopRep.JointlyContinuous (TopRep.res K.subtype X) :=
    TopRep.jointlyContinuous_res K.toSubgroup X
  exact TopRep.jointlyContinuous_res
    (mackeyOpenStabilizer H K x).toSubgroup (TopRep.res K.subtype X)

/-- Joint continuity of the coefficient action persists upon restriction to a
Mackey stabilizer. This reuses the existing private local proof without adding
an instance to the API seen by importers. -/
theorem jointlyContinuous_mackeyStabilizer
    (H K : OpenSubgroup G) (x : G) [TopRep.JointlyContinuous X] :
    TopRep.JointlyContinuous
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X)) :=
  jointlyContinuous_mackeyRes X H K x

attribute [local instance] jointlyContinuous_mackeyStabilizer

/-- Conjugation identifies a Mackey stabilizer with a subgroup of `H`. -/
def mackeyStabilizerToLeft (H K : OpenSubgroup G) (x : G) :
    mackeyOpenStabilizer H K x →ₜ* H where
  toFun l := ⟨x * ((l : K) : G) * x⁻¹, l.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' l m := by
    apply Subtype.ext
    change
      x * ((((l : mackeyOpenStabilizer H K x) : K) : G) *
          (((m : mackeyOpenStabilizer H K x) : K) : G)) * x⁻¹ =
        (x * (((l : mackeyOpenStabilizer H K x) : K) : G) * x⁻¹) *
          (x * (((m : mackeyOpenStabilizer H K x) : K) : G) * x⁻¹)
    group
  continuous_toFun := Continuous.subtype_mk
    ((mackeyConjugationHom K x).continuous.comp continuous_subtype_val) _

/-- Conjugate and restrict a crossed homomorphism from `H` to the stabilizer
of the right `H`-coset represented by `x`. Its application computes by
conjugating the input cocycle. -/
@[expose]
def mackeyConjugateCrossed (H K : OpenSubgroup G) (x : G) :
    continuousCrossedHom (TopRep.res H.subtype X) →L[k]
      continuousCrossedHom
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X)) :=
  let L := mackeyOpenStabilizer H K x
  let pre : C(H, X) →L[k] C(L, X) :=
    (ContinuousMap.compCLM k X
      ⟨mackeyStabilizerToLeft H K x,
        (mackeyStabilizerToLeft H K x).continuous⟩)
  let post : C(L, X) →L[k] C(L, X) :=
    ContinuousLinearMap.compLeftContinuous k L (X.ρ x⁻¹)
  (post.comp (pre.comp
      (Submodule.subtypeL (continuousCrossedHom
        (TopRep.res H.subtype X))))).codRestrict _ fun f l m => by
    change X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x (l * m))) =
      X.ρ (((l : L) : K) : G)
          (X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x m))) +
        X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x l))
    rw [map_mul, f.2, map_add]
    change
      X.ρ x⁻¹
          (X.ρ (x * (((l : L) : K) : G) * x⁻¹)
            (f.1 (mackeyStabilizerToLeft H K x m))) +
          X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x l)) =
        X.ρ (((l : L) : K) : G)
            (X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x m))) +
          X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x l))
    rw [rho_mul_apply, rho_mul_apply]
    congr 2
    congr 1
    group

@[simp]
lemma mackeyConjugateCrossed_apply (H K : OpenSubgroup G) (x : G)
    (f : continuousCrossedHom (TopRep.res H.subtype X))
    (l : mackeyOpenStabilizer H K x) :
    (mackeyConjugateCrossed X H K x f).1 l =
      X.ρ x⁻¹ (f.1 (mackeyStabilizerToLeft H K x l)) := rfl

/-- Conjugation and restriction send principal crossed homomorphisms to
principal crossed homomorphisms with the conjugated coefficient. -/
lemma mackeyConjugateCrossed_principal (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] (c : X) :
    mackeyConjugateCrossed X H K x
        (principalToCrossed (TopRep.res H.subtype X) c) =
      principalToCrossed
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X)) (X.ρ x⁻¹ c) := by
  ext l
  rw [mackeyConjugateCrossed_apply]
  change X.ρ x⁻¹ (X.ρ (x * (((l : mackeyOpenStabilizer H K x) : K) : G) * x⁻¹) c - c) =
    X.ρ (((l : mackeyOpenStabilizer H K x) : K) : G) (X.ρ x⁻¹ c) - X.ρ x⁻¹ c
  rw [map_sub, rho_mul_apply, rho_mul_apply]
  congr 2
  group

/-- Conjugation and restriction descend to crossed homomorphisms modulo
principal crossed homomorphisms. Its lift computes on representatives. -/
@[expose]
def mackeyConjugateQuotient (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X)) ⧸
        principalCocycles
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))) :=
  (principalCocycles (TopRep.res H.subtype X)).liftQL
    ((principalCocycles
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).mkQL.comp
      (mackeyConjugateCrossed X H K x)) <| by
      intro f hf
      rw [LinearMap.mem_ker]
      change (principalCocycles
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X))).mkQL
          (mackeyConjugateCrossed X H K x f) = 0
      change f ∈ LinearMap.range
        (principalToCrossed (TopRep.res H.subtype X)) at hf
      rcases hf with ⟨c, rfl⟩
      rw [mackeyConjugateCrossed_principal]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨X.ρ x⁻¹ c, rfl⟩

@[simp]
lemma mackeyConjugateQuotient_mk (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    mackeyConjugateQuotient X H K x
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) =
      (principalCocycles
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X))).mkQ
        (mackeyConjugateCrossed X H K x f) := rfl

/-- Transfer from a Mackey stabilizer to `K`, with the finite-index witness
obtained from the ambient finite index of `H`. -/
noncomputable def mackeyTransferCrossedWithTransversal
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal) :
    continuousCrossedHom
        (TopRep.res (mackeyOpenStabilizer H K x).subtype
          (TopRep.res K.subtype X)) →L[k]
      continuousCrossedHom (TopRep.res K.subtype X) := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  exact transferCrossed (TopRep.res K.subtype X)
    (mackeyOpenStabilizer H K x) T

/-- The quotient-level Mackey summand attached to `x`, computed with a chosen
right transversal of its stabilizer in `K`. Its lift computes on cocycles. -/
@[expose]
noncomputable def mackeySummandQuotientWithTransversal
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  exact (transferQuotient (TopRep.res K.subtype X)
      (mackeyOpenStabilizer H K x) T).comp
    (mackeyConjugateQuotient X H K x)

/-- A Mackey summand on crossed-homomorphism quotients is independent of the
right transversal used for its stabilizer. -/
lemma mackeySummandQuotientWithTransversal_eq
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T S : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    mackeySummandQuotientWithTransversal X H K x T =
      mackeySummandQuotientWithTransversal X H K x S := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  simp only [mackeySummandQuotientWithTransversal]
  rw [transferQuotient_eq (TopRep.res K.subtype X)
    (mackeyOpenStabilizer H K x) T S]

/-- The quotient-level Mackey summand attached to an ambient representative.
Its apparent dependence on the representative is removed below by the
double-coset representative-change argument. -/
noncomputable def mackeySummandQuotient
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  exact mackeySummandQuotientWithTransversal X H K x default

/-- The canonical Mackey summand can be computed from any stabilizer
transversal. -/
lemma mackeySummandQuotient_eq_withTransversal
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    mackeySummandQuotient X H K x =
      mackeySummandQuotientWithTransversal X H K x T :=
  by
    let _ := mackeyOpenStabilizerFiniteIndex H K x
    exact mackeySummandQuotientWithTransversal_eq X H K x default T

@[simp]
lemma mackeySummandQuotientWithTransversal_mk
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    mackeySummandQuotientWithTransversal X H K x T
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) =
      (principalCocycles (TopRep.res K.subtype X)).mkQ
        (mackeyTransferCrossedWithTransversal X H K x T
          (mackeyConjugateCrossed X H K x f)) := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  rfl

/-- Conjugation by an element of an open subgroup, as a continuous
endomorphism of that open subgroup. It computes pointwise by conjugation. -/
@[expose]
def openSubgroupConjugationHom (K : OpenSubgroup G) (b : K) : K →ₜ* K where
  toMonoidHom := (MulAut.conj b).toMonoidHom
  continuous_toFun := IsTopologicalGroup.continuous_conj b

@[simp]
lemma openSubgroupConjugationHom_apply (K : OpenSubgroup G) (b l : K) :
    openSubgroupConjugationHom K b l = b * l * b⁻¹ := rfl

/-- The open Mackey stabilizer transforms by conjugation under a change of
ambient representative. -/
lemma mackeyOpenStabilizer_mul_left_mul_right (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K) :
    mackeyOpenStabilizer H K ((h : G) * x * (b : G)) =
      (mackeyOpenStabilizer H K x).comap
        (openSubgroupConjugationHom K b)
        (openSubgroupConjugationHom K b).continuous := by
  ext l
  change
    (l : K) ∈ mackeyStabilizer H.toSubgroup K.toSubgroup
        ((h : G) * x * (b : G)) ↔
      (l : K) ∈
        (mackeyStabilizer H.toSubgroup K.toSubgroup x).comap
          (MulAut.conj b).toMonoidHom
  rw [mackeyStabilizer_mul_left_mul_right H.toSubgroup K.toSubgroup x h b]

/-- The right transversal used after changing an ambient representative by
`h * x * b`. It computes as the conjugate transversal. -/
@[expose]
def mackeyRepresentativeRightTransversal (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal) :
    (mackeyOpenStabilizer H K ((h : G) * x * (b : G))).toSubgroup.RightTransversal := by
  let T' := conjugateRightTransversal
    (mackeyOpenStabilizer H K x).toSubgroup T b
  refine ⟨(T' : Set K), ?_⟩
  rw [mackeyOpenStabilizer_mul_left_mul_right H K x h b]
  exact T'.2

/-- Multiplication by `b` identifies the changed-representative transversal
with the original stabilizer transversal. Its application computes to the
translated representative. -/
@[expose]
def mackeyRepresentativeTransversalEquiv (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal) :
    ↥(mackeyRepresentativeRightTransversal H K x h b T : Set K) ≃
      ↥(T : Set K) := by
  exact conjugateTransversalEquiv
    (mackeyOpenStabilizer H K x).toSubgroup T b

@[simp]
lemma mackeyRepresentativeTransversalEquiv_coe (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    (t : ↥(mackeyRepresentativeRightTransversal H K x h b T : Set K)) :
    (mackeyRepresentativeTransversalEquiv H K x h b T t : K) =
      b * (t : K) := rfl

lemma mackeyRepresentativeTransversal_factor (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    (t : ↥(mackeyRepresentativeRightTransversal H K x h b T : Set K))
    (g : K) :
    b * (factor (G := K) (mackeyRepresentativeRightTransversal H K x h b T) t g : K) * b⁻¹ =
      (factor (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g : K) := by
  let T' := mackeyRepresentativeRightTransversal H K x h b T
  let l' := factor (G := K) T' t g
  let n' := next (G := K) T' t g
  have hl : b * (l' : K) * b⁻¹ ∈ (mackeyOpenStabilizer H K x).toSubgroup := by
    have hl' : (l' : K) ∈ mackeyStabilizer H.toSubgroup K.toSubgroup
        ((h : G) * x * (b : G)) := l'.2
    rw [mackeyStabilizer_mul_left_mul_right H.toSubgroup K.toSubgroup x h b] at hl'
    exact hl'
  have hpair :
      ((⟨b * (l' : K) * b⁻¹, hl⟩ : (mackeyOpenStabilizer H K x).toSubgroup),
          mackeyRepresentativeTransversalEquiv H K x h b T n') =
        (factor (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g,
          next (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g) := by
    apply T.2.1
    calc
      (b * (l' : K) * b⁻¹) *
          (mackeyRepresentativeTransversalEquiv H K x h b T n' : K) =
          b * ((l' : K) * (n' : K)) := by
            rw [mackeyRepresentativeTransversalEquiv_coe]
            group
      _ = b * ((t : K) * g) := by rw [factor_mul_next (G := K)]
      _ = (b * (t : K)) * g := by group
      _ = (mackeyRepresentativeTransversalEquiv H K x h b T t : K) * g := by
        rw [mackeyRepresentativeTransversalEquiv_coe]
      _ = (factor (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g : K) *
            (next (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g : K) :=
        (factor_mul_next (G := K) _ _ _).symm
  exact congrArg (fun p => (p.1 : K)) hpair

lemma mackeyRepresentativeTransversal_next (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    (t : ↥(mackeyRepresentativeRightTransversal H K x h b T : Set K))
    (g : K) :
    mackeyRepresentativeTransversalEquiv H K x h b T
        (next (G := K) (mackeyRepresentativeRightTransversal H K x h b T) t g) =
      next (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g := by
  let T' := mackeyRepresentativeRightTransversal H K x h b T
  let l' := factor (G := K) T' t g
  let n' := next (G := K) T' t g
  have hl : b * (l' : K) * b⁻¹ ∈ (mackeyOpenStabilizer H K x).toSubgroup := by
    have hl' : (l' : K) ∈ mackeyStabilizer H.toSubgroup K.toSubgroup
        ((h : G) * x * (b : G)) := l'.2
    rw [mackeyStabilizer_mul_left_mul_right H.toSubgroup K.toSubgroup x h b] at hl'
    exact hl'
  have hpair :
      ((⟨b * (l' : K) * b⁻¹, hl⟩ : (mackeyOpenStabilizer H K x).toSubgroup),
          mackeyRepresentativeTransversalEquiv H K x h b T n') =
        (factor (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g,
          next (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g) := by
    apply T.2.1
    calc
      (b * (l' : K) * b⁻¹) *
          (mackeyRepresentativeTransversalEquiv H K x h b T n' : K) =
          b * ((l' : K) * (n' : K)) := by
            rw [mackeyRepresentativeTransversalEquiv_coe]
            group
      _ = b * ((t : K) * g) := by rw [factor_mul_next (G := K)]
      _ = (b * (t : K)) * g := by group
      _ = (mackeyRepresentativeTransversalEquiv H K x h b T t : K) * g := by
        rw [mackeyRepresentativeTransversalEquiv_coe]
      _ = (factor (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g : K) *
            (next (G := K) T (mackeyRepresentativeTransversalEquiv H K x h b T t) g : K) :=
        (factor_mul_next (G := K) _ _ _).symm
  exact congrArg (fun p => p.2) hpair

lemma mackeyRepresentative_transferTerm (H K : OpenSubgroup G) (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X))
    (t : ↥(mackeyRepresentativeRightTransversal H K x h b T : Set K))
    (g : K) :
    (TopRep.res K.subtype X).ρ ((t : K)⁻¹)
        ((mackeyConjugateCrossed X H K ((h : G) * x * (b : G)) f).1
          (factor (G := K) (mackeyRepresentativeRightTransversal H K x h b T) t g)) =
      (TopRep.res K.subtype X).ρ
          ((mackeyRepresentativeTransversalEquiv H K x h b T t : K)⁻¹)
          ((mackeyConjugateCrossed X H K x f).1
            (factor (G := K) T
              (mackeyRepresentativeTransversalEquiv H K x h b T t) g)) -
        (TopRep.res K.subtype X).ρ
          ((mackeyRepresentativeTransversalEquiv H K x h b T t : K)⁻¹)
          ((principalToCrossed
              (TopRep.res (mackeyOpenStabilizer H K x).subtype
                (TopRep.res K.subtype X))
              (X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h)))).1
            (factor (G := K) T
              (mackeyRepresentativeTransversalEquiv H K x h b T t) g)) := by
  rw [mackeyConjugateCrossed_apply, mackeyConjugateCrossed_apply]
  let T' := mackeyRepresentativeRightTransversal H K x h b T
  let s := mackeyRepresentativeTransversalEquiv H K x h b T t
  let l' := factor (G := K) T' t g
  let l := factor (G := K) T s g
  let a : H := mackeyStabilizerToLeft H K x l
  have hl : b * (l' : K) * b⁻¹ = (l : K) := by
    exact mackeyRepresentativeTransversal_factor H K x h b T t g
  have hs : (s : K) = b * (t : K) := by
    exact mackeyRepresentativeTransversalEquiv_coe H K x h b T t
  have hlG : (b : G) * ((l' : K) : G) * (b : G)⁻¹ = ((l : K) : G) := by
    exact_mod_cast hl
  have hsG : ((s : K) : G) = (b : G) * ((t : K) : G) := by
    exact_mod_cast hs
  have ha : mackeyStabilizerToLeft H K ((h : G) * x * (b : G)) l' =
      h * a * h⁻¹ := by
    apply Subtype.ext
    change ((h : G) * x * (b : G)) * (l' : K) *
        ((h : G) * x * (b : G))⁻¹ =
      (h : G) * (x * (l : K) * x⁻¹) * (h : G)⁻¹
    rw [← hlG]
    group
  change X.ρ ((t : K) : G)⁻¹
      (X.ρ (((h : G) * x * (b : G))⁻¹)
        (f.1 (mackeyStabilizerToLeft H K ((h : G) * x * (b : G)) l'))) = _
  rw [ha]
  change _ = X.ρ ((s : K) : G)⁻¹ (X.ρ x⁻¹ (f.1 a)) - _
  calc
    _ = X.ρ (((s : K) : G)⁻¹)
        (X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 (h * a * h⁻¹)))) := by
      rw [rho_mul_apply, rho_mul_apply, rho_mul_apply]
      congr 2
      rw [hsG]
      group
    _ = _ := by
      rw [innerConjCrossed_formula X H f h a]
      rw [map_sub, map_sub]
      congr 1
      change X.ρ (((s : K) : G)⁻¹)
          (X.ρ x⁻¹
            (X.ρ (a : G) (X.ρ ((h : G)⁻¹) (f.1 h)) -
              X.ρ ((h : G)⁻¹) (f.1 h))) =
        X.ρ (((s : K) : G)⁻¹)
          (X.ρ (((l : K) : G))
              (X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h))) -
            X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h)))
      apply congrArg (X.ρ (((s : K) : G)⁻¹))
      rw [map_sub]
      congr 1
      calc
        X.ρ x⁻¹
            (X.ρ (a : G) (X.ρ ((h : G)⁻¹) (f.1 h))) =
          X.ρ (x⁻¹ * (a : G)) (X.ρ ((h : G)⁻¹) (f.1 h)) :=
            rho_mul_apply X _ _ _
        _ = X.ρ ((((l : K) : G)) * x⁻¹)
            (X.ρ ((h : G)⁻¹) (f.1 h)) := by
          congr 2
          change x⁻¹ * (x * (((l : K) : G)) * x⁻¹) = (((l : K) : G)) * x⁻¹
          group
        _ = X.ρ (((l : K) : G))
            (X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h))) :=
          (rho_mul_apply X _ _ _).symm

/-- The coefficient of the principal defect caused by changing the ambient
Mackey representative on the left. -/
noncomputable def mackeyRepresentativeCoefficient
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G) (h : H)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) : X := by
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  exact transferCoefficient (TopRep.res K.subtype X)
    (mackeyOpenStabilizer H K x) T
    (X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h)))

set_option maxHeartbeats 500000 in
/-- Changing an ambient Mackey representative from `x` to `h * x * b`, and
transporting the stabilizer transversal accordingly, changes the transferred
crossed homomorphism by one principal crossed homomorphism. -/
lemma mackeyTransferCrossed_mul_left_mul_right
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X]
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    mackeyTransferCrossedWithTransversal X H K ((h : G) * x * (b : G))
        (mackeyRepresentativeRightTransversal H K x h b T)
        (mackeyConjugateCrossed X H K ((h : G) * x * (b : G)) f) =
      mackeyTransferCrossedWithTransversal X H K x T
          (mackeyConjugateCrossed X H K x f) -
        principalToCrossed (TopRep.res K.subtype X)
          (mackeyRepresentativeCoefficient X H K x h T f) := by
  let T' := mackeyRepresentativeRightTransversal H K x h b T
  let e := mackeyRepresentativeTransversalEquiv H K x h b T
  let d := X.ρ x⁻¹ (X.ρ ((h : G)⁻¹) (f.1 h))
  let _ := mackeyOpenStabilizerFiniteIndex H K x
  let _ := mackeyOpenStabilizerFiniteIndex H K ((h : G) * x * (b : G))
  let _ : Fintype ↥(T : Set K) := T.2.finite_right.fintype
  let _ : Fintype ↥(T' : Set K) := T'.2.finite_right.fintype
  have htransfer :
      mackeyTransferCrossedWithTransversal X H K ((h : G) * x * (b : G)) T'
          (mackeyConjugateCrossed X H K ((h : G) * x * (b : G)) f) =
        mackeyTransferCrossedWithTransversal X H K x T
            (mackeyConjugateCrossed X H K x f) -
          transferCrossed (TopRep.res K.subtype X)
            (mackeyOpenStabilizer H K x) T
            (principalToCrossed
              (TopRep.res (mackeyOpenStabilizer H K x).subtype
                (TopRep.res K.subtype X)) d) := by
    ext g
    change
      (transferCrossed (TopRep.res K.subtype X)
        (mackeyOpenStabilizer H K ((h : G) * x * (b : G))) T'
        (mackeyConjugateCrossed X H K ((h : G) * x * (b : G)) f)).1 g =
      (transferCrossed (TopRep.res K.subtype X)
          (mackeyOpenStabilizer H K x) T
          (mackeyConjugateCrossed X H K x f)).1 g -
      (transferCrossed (TopRep.res K.subtype X)
          (mackeyOpenStabilizer H K x) T
          (principalToCrossed
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X)) d)).1 g
    rw [transferCrossed_apply, transferCrossed_apply, transferCrossed_apply]
    change (∑ t : ↥(T' : Set K), _) = _
    calc
      (∑ t : ↥(T' : Set K),
          (TopRep.res K.subtype X).ρ ((t : K)⁻¹)
            ((mackeyConjugateCrossed X H K ((h : G) * x * (b : G)) f).1
              (factor (G := K) T' t g))) =
          ∑ t : ↥(T' : Set K),
            ((TopRep.res K.subtype X).ρ ((e t : K)⁻¹)
                ((mackeyConjugateCrossed X H K x f).1
                  (factor (G := K) T (e t) g)) -
              (TopRep.res K.subtype X).ρ ((e t : K)⁻¹)
                ((principalToCrossed
                  (TopRep.res (mackeyOpenStabilizer H K x).subtype
                    (TopRep.res K.subtype X)) d).1
                  (factor (G := K) T (e t) g))) := by
            apply Finset.sum_congr rfl
            intro t _
            exact mackeyRepresentative_transferTerm X H K x h b T f t g
      _ = ∑ s : ↥(T : Set K),
            ((TopRep.res K.subtype X).ρ ((s : K)⁻¹)
                ((mackeyConjugateCrossed X H K x f).1
                  (factor (G := K) T s g)) -
              (TopRep.res K.subtype X).ρ ((s : K)⁻¹)
                ((principalToCrossed
                  (TopRep.res (mackeyOpenStabilizer H K x).subtype
                    (TopRep.res K.subtype X)) d).1
                  (factor (G := K) T s g))) := by
            exact Equiv.sum_comp e (fun s : ↥(T : Set K) =>
              (TopRep.res K.subtype X).ρ ((s : K)⁻¹)
                  ((mackeyConjugateCrossed X H K x f).1
                    (factor (G := K) T s g)) -
                (TopRep.res K.subtype X).ρ ((s : K)⁻¹)
                  ((principalToCrossed
                    (TopRep.res (mackeyOpenStabilizer H K x).subtype
                      (TopRep.res K.subtype X)) d).1
                    (factor (G := K) T s g)))
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [htransfer, transferCrossed_principal]
  rfl

set_option maxHeartbeats 500000 in
/-- Representative change is invisible on the quotient when the changed
stabilizer uses the transported transversal. -/
lemma mackeySummandQuotientWithTransversal_mul_left_mul_right
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (h : H) (b : K)
    (T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal)
    [TopRep.JointlyContinuous X] :
    mackeySummandQuotientWithTransversal X H K ((h : G) * x * (b : G))
        (mackeyRepresentativeRightTransversal H K x h b T) =
      mackeySummandQuotientWithTransversal X H K x T := by
  apply ContinuousLinearMap.ext
  intro q
  refine Submodule.Quotient.induction_on _ q ?_
  intro f
  change
    mackeySummandQuotientWithTransversal X H K ((h : G) * x * (b : G))
        (mackeyRepresentativeRightTransversal H K x h b T)
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) =
      mackeySummandQuotientWithTransversal X H K x T
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f)
  rw [mackeySummandQuotientWithTransversal_mk,
    mackeySummandQuotientWithTransversal_mk,
    mackeyTransferCrossed_mul_left_mul_right]
  rw [map_sub]
  have hp :
      (principalCocycles (TopRep.res K.subtype X)).mkQ
          (principalToCrossed (TopRep.res K.subtype X)
            (mackeyRepresentativeCoefficient X H K x h T f)) = 0 :=
    (Submodule.Quotient.mk_eq_zero
      (principalCocycles (TopRep.res K.subtype X))).2
      ⟨mackeyRepresentativeCoefficient X H K x h T f, rfl⟩
  rw [hp, sub_zero]

/-- The canonical quotient-level Mackey summand depends only on the ambient
double coset represented by `x`. -/
lemma mackeySummandQuotient_mul_left_mul_right
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] (x : G)
    (h : H) (b : K) [TopRep.JointlyContinuous X] :
    mackeySummandQuotient X H K ((h : G) * x * (b : G)) =
      mackeySummandQuotient X H K x := by
  let T : (mackeyOpenStabilizer H K x).toSubgroup.RightTransversal := default
  calc
    mackeySummandQuotient X H K ((h : G) * x * (b : G)) =
        mackeySummandQuotientWithTransversal X H K ((h : G) * x * (b : G))
          (mackeyRepresentativeRightTransversal H K x h b T) :=
      mackeySummandQuotient_eq_withTransversal X H K _ _
    _ = mackeySummandQuotientWithTransversal X H K x T :=
      mackeySummandQuotientWithTransversal_mul_left_mul_right X H K x h b T
    _ = mackeySummandQuotient X H K x :=
      (mackeySummandQuotient_eq_withTransversal X H K x T).symm

/-- A finite left index gives finitely many double cosets. -/
noncomputable instance mackeyDoubleCosetFinite
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex] :
    Finite (DoubleCoset.Quotient (H : Set G) K) := by
  let T : H.toSubgroup.RightTransversal := default
  let _ : Fintype ↥(T : Set G) := T.2.finite_right.fintype
  apply Finite.of_surjective
    (fun t : ↥(T : Set G) => DoubleCoset.mk H.toSubgroup K.toSubgroup (t : G))
  intro q
  let p := T.2.equiv q.out
  refine ⟨p.2, ?_⟩
  rw [← DoubleCoset.out_eq' q]
  rw [← T.2.equiv_fst_mul_equiv_snd q.out]
  exact (DoubleCoset.mk_mem_mul p.1 p.2).symm

/-- The representative-independent quotient-level summand attached to a
double coset. It computes on canonical representatives. -/
@[expose]
noncomputable def mackeyDoubleCosetSummand
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X]
    (q : DoubleCoset.Quotient (H : Set G) K) :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) :=
  Quotient.lift (fun x => mackeySummandQuotient X H K x) (by
    intro x y hxy
    obtain ⟨h, hh, b, hb, rfl⟩ := DoubleCoset.rel_iff.mp hxy
    exact (mackeySummandQuotient_mul_left_mul_right X H K x
      ⟨h, hh⟩ ⟨b, hb⟩).symm) q

@[simp]
lemma mackeyDoubleCosetSummand_mk
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] (x : G) :
    mackeyDoubleCosetSummand X H K
        (DoubleCoset.mk H.toSubgroup K.toSubgroup x) =
      mackeySummandQuotient X H K x :=
  rfl

/-- The finite sum of the quotient-level summands over `H \ G / K`. -/
noncomputable def mackeyDoubleCosetSum
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] :
    (continuousCrossedHom (TopRep.res H.subtype X) ⧸
        principalCocycles (TopRep.res H.subtype X)) →L[k]
      (continuousCrossedHom (TopRep.res K.subtype X) ⧸
        principalCocycles (TopRep.res K.subtype X)) := by
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  exact ∑ q : DoubleCoset.Quotient (H : Set G) K,
    mackeyDoubleCosetSummand X H K q

/-- The ambient representative attached to a double coset and a representative
of a right coset of its Mackey stabilizer. Its product formula is used by the
assembled-transversal membership calculation. -/
@[expose]
def mackeyAssembledRepresentative (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (p : Sigma fun q => Subtype (T q : Set K)) : G :=
  p.1.out * (p.2.1 : G)

/-- Double-coset representatives followed by stabilizer transversals assemble
to a right transversal of `H` in the ambient group. Its carrier computes as
the range of assembled representatives. -/
@[expose]
noncomputable def mackeyAssembledRightTransversal (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal) :
    H.toSubgroup.RightTransversal := by
  let S : Set G := Set.range (mackeyAssembledRepresentative H K T)
  refine ⟨S, Subgroup.isComplement_iff_existsUnique.mpr ?_⟩
  intro g
  let q := DoubleCoset.mk H.toSubgroup K.toSubgroup g
  obtain ⟨h₀, hh₀, b₀, hb₀, hout⟩ :=
    DoubleCoset.mk_out_eq_mul H.toSubgroup K.toSubgroup g
  let p := (T q).2.equiv (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K)
  let l := p.1
  let t := p.2
  have hlH : q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹ ∈ H :=
    l.2
  let h : H := ⟨h₀⁻¹ *
    (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹),
      H.mul_mem (H.inv_mem hh₀) hlH⟩
  let s : Subtype S :=
    ⟨q.out * (t.1 : G), ⟨⟨q, t⟩, rfl⟩⟩
  have hdecomp : (h : G) * s.1 = g := by
    change
      (h₀⁻¹ *
          (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹)) *
          (q.out * (t.1 : G)) = g
    have hp := (T q).2.equiv_fst_mul_equiv_snd (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K)
    change ((l : mackeyOpenStabilizer H K q.out) : K) * t.1 =
      (⟨b₀⁻¹, K.inv_mem hb₀⟩ : K) at hp
    have hpG : (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
        (t.1 : G) = (b₀ : G)⁻¹ := by
      have hpG' := congrArg (fun z : K => (z : G)) hp
      change (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
        (t.1 : G) = (b₀ : G)⁻¹ at hpG'
      exact hpG'
    calc
      _ = h₀⁻¹ * q.out *
          ((((l : mackeyOpenStabilizer H K q.out) : K) : G) * (t.1 : G)) := by
        group
      _ = h₀⁻¹ * q.out * (b₀ : G)⁻¹ := by rw [hpG]
      _ = h₀⁻¹ * (h₀ * g * b₀) * (b₀ : G)⁻¹ := by rw [hout]
      _ = g := by group
  refine ⟨(h, s), hdecomp, ?_⟩
  rintro ⟨h₁, s₁⟩ hs₁
  obtain ⟨⟨q₁, t₁⟩, ht₁⟩ := s₁.2
  have heq : (h₁ : G) *
      (q₁.out * (t₁.1 : G)) = g := by
    change (h₁ : G) *
      mackeyAssembledRepresentative H K T ⟨q₁, t₁⟩ = g
    rw [ht₁]
    exact hs₁
  have hq : q₁ = q := by
    calc
      q₁ = DoubleCoset.mk H.toSubgroup K.toSubgroup q₁.out :=
        (DoubleCoset.out_eq' q₁).symm
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
          (q₁.out * (t₁.1 : G)) := by
        symm
        exact DoubleCoset.mk_mul_mem t₁.1 q₁.out
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
          ((h₁ : G) * (q₁.out * (t₁.1 : G))) := by
        symm
        exact DoubleCoset.mk_mem_mul h₁ _
      _ = DoubleCoset.mk H.toSubgroup K.toSubgroup g := congrArg _ heq
      _ = q := rfl
  subst q₁
  let lK : K := t.1 * t₁.1⁻¹
  have hlH₁ : q.out * ((lK : K) : G) * q.out⁻¹ ∈ H := by
    have hrel : q.out * ((lK : K) : G) * q.out⁻¹ =
        (h : G)⁻¹ * (h₁ : G) := by
      dsimp [lK]
      change q.out * ((t.1 : G) * (t₁.1 : G)⁻¹) * q.out⁻¹ =
        (h : G)⁻¹ * (h₁ : G)
      have hmain : (h₁ : G) * (q.out * (t₁.1 : G)) =
          (h : G) * (q.out * (t.1 : G)) := by
        rw [heq]
        exact hdecomp.symm
      calc
        _ = (h : G)⁻¹ * ((h : G) * (q.out * (t.1 : G))) *
            (t₁.1 : G)⁻¹ * q.out⁻¹ := by group
        _ = (h : G)⁻¹ * ((h₁ : G) * (q.out * (t₁.1 : G))) *
            (t₁.1 : G)⁻¹ * q.out⁻¹ := by rw [hmain]
        _ = (h : G)⁻¹ * (h₁ : G) := by group
    rw [hrel]
    exact H.mul_mem (H.inv_mem h.2) h₁.2
  let l₁ : mackeyOpenStabilizer H K q.out := ⟨lK, hlH₁⟩
  have hpair :
      (l₁, t₁) =
        (1, t) := by
    apply (T q).2.1
    change lK * t₁.1 = (1 : K) * t.1
    simp only [lK, one_mul]
    group
  have htt : t₁ = t := congrArg Prod.snd hpair
  have hss : s₁ = s := by
    apply Subtype.ext
    change s₁.1 = q.out * (t.1 : G)
    calc
      s₁.1 = mackeyAssembledRepresentative H K T ⟨q, t₁⟩ := ht₁.symm
      _ = mackeyAssembledRepresentative H K T ⟨q, t⟩ := by rw [htt]
      _ = q.out * (t.1 : G) := rfl
  have hhh : h₁ = h := by
    apply Subtype.ext
    apply mul_right_cancel (b := s₁.1)
    rw [hs₁, hss]
    exact hdecomp.symm
  exact Prod.ext hhh hss

/-- A double-coset representative followed by a local representative, viewed
inside the assembled ambient transversal. Its ambient value computes as a
product of representatives. -/
@[expose]
noncomputable def mackeyAssembledRepresentativeMem (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (t : Subtype (T q : Set K)) :
    Subtype (mackeyAssembledRightTransversal H K T : Set G) :=
  ⟨q.out * (t.1 : G), ⟨⟨q, t⟩, rfl⟩⟩

@[simp]
lemma mackeyAssembledRepresentativeMem_coe (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (t : Subtype (T q : Set K)) :
    (mackeyAssembledRepresentativeMem H K T q t).1 =
      q.out * (t.1 : G) := rfl

/-- The factor in the assembled ambient transversal is the conjugate of the
factor in the corresponding stabilizer transversal. -/
lemma mackeyAssembled_factor (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (t : Subtype (T q : Set K)) (g : K) :
    factor (mackeyAssembledRightTransversal H K T)
        (mackeyAssembledRepresentativeMem H K T q t) (g : G) =
      (⟨q.out *
        (((factor (G := K) (T q) t g :
          mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹,
        (factor (G := K) (T q) t g).2⟩ : H) := by
  let S := mackeyAssembledRightTransversal H K T
  let s := mackeyAssembledRepresentativeMem H K T q t
  let l := factor (G := K) (T q) t g
  let n := next (G := K) (T q) t g
  have hlH : q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
      q.out⁻¹ ∈ H := l.2
  let h : H := ⟨q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
    q.out⁻¹, hlH⟩
  let s' := mackeyAssembledRepresentativeMem H K T q n
  have hpair :
      (factor S s (g : G), next S s (g : G)) = (h, s') := by
    apply S.2.1
    calc
      ((factor S s (g : G) : H) : G) * (next S s (g : G)).1 =
          s.1 * (g : G) := factor_mul_next S s (g : G)
      _ = q.out * ((t.1 * g : K) : G) := by
        dsimp only [s, mackeyAssembledRepresentativeMem]
        change (q.out * (t.1 : G)) * (g : G) =
          q.out * ((t.1 : G) * (g : G))
        group
      _ = q.out *
          ((((l : mackeyOpenStabilizer H K q.out) : K) * n.1 : K) : G) := by
        rw [show ((l : mackeyOpenStabilizer H K q.out) : K) * n.1 =
          t.1 * g from by
            simpa only [l, n] using factor_mul_next (G := K) (T q) t g]
      _ = (h : G) * s'.1 := by
        rw [show
          ((((l : mackeyOpenStabilizer H K q.out) : K) * n.1 : K) : G) =
            (((l : mackeyOpenStabilizer H K q.out) : K) : G) * (n.1 : G) from rfl]
        dsimp only [h, s', mackeyAssembledRepresentativeMem]
        change q.out *
            ((((l : mackeyOpenStabilizer H K q.out) : K) : G) * (n.1 : G)) =
          (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹) *
            (q.out * (n.1 : G))
        group
  exact congrArg (fun p : H × Subtype (S : Set G) => p.1) hpair

/-- The next representative in the assembled ambient transversal retains the
double coset and applies the local next-representative operation. -/
lemma mackeyAssembled_next (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (q : DoubleCoset.Quotient (H : Set G) K)
    (t : Subtype (T q : Set K)) (g : K) :
    next (mackeyAssembledRightTransversal H K T)
        (mackeyAssembledRepresentativeMem H K T q t) (g : G) =
      mackeyAssembledRepresentativeMem H K T q
        (next (G := K) (T q) t g) := by
  let S := mackeyAssembledRightTransversal H K T
  let s := mackeyAssembledRepresentativeMem H K T q t
  let l := factor (G := K) (T q) t g
  let n := next (G := K) (T q) t g
  have hlH : q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
      q.out⁻¹ ∈ H := l.2
  let h : H := ⟨q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) *
    q.out⁻¹, hlH⟩
  let s' := mackeyAssembledRepresentativeMem H K T q n
  have hpair :
      (factor S s (g : G), next S s (g : G)) = (h, s') := by
    apply S.2.1
    calc
      ((factor S s (g : G) : H) : G) * (next S s (g : G)).1 =
          s.1 * (g : G) := factor_mul_next S s (g : G)
      _ = q.out * ((t.1 * g : K) : G) := by
        dsimp only [s, mackeyAssembledRepresentativeMem]
        change (q.out * (t.1 : G)) * (g : G) =
          q.out * ((t.1 : G) * (g : G))
        group
      _ = q.out *
          ((((l : mackeyOpenStabilizer H K q.out) : K) * n.1 : K) : G) := by
        rw [show ((l : mackeyOpenStabilizer H K q.out) : K) * n.1 =
          t.1 * g from by
            simpa only [l, n] using factor_mul_next (G := K) (T q) t g]
      _ = (h : G) * s'.1 := by
        rw [show
          ((((l : mackeyOpenStabilizer H K q.out) : K) * n.1 : K) : G) =
            (((l : mackeyOpenStabilizer H K q.out) : K) : G) * (n.1 : G) from rfl]
        dsimp only [h, s', mackeyAssembledRepresentativeMem]
        change q.out *
            ((((l : mackeyOpenStabilizer H K q.out) : K) : G) * (n.1 : G)) =
          (q.out * (((l : mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹) *
            (q.out * (n.1 : G))
        group
  exact congrArg (fun p : H × Subtype (S : Set G) => p.2) hpair

/-- The sigma type of double cosets and local transversal representatives is
equivalent to the assembled ambient transversal. -/
noncomputable def mackeyAssembledTransversalEquiv (H K : OpenSubgroup G)
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal) :
    (Sigma fun q => Subtype (T q : Set K)) ≃
      Subtype (mackeyAssembledRightTransversal H K T : Set G) :=
  Equiv.ofBijective
    (fun p => mackeyAssembledRepresentativeMem H K T p.1 p.2)
    ⟨by
      rintro ⟨q₁, t₁⟩ ⟨q₂, t₂⟩ ht
      have htG : q₁.out * (t₁.1 : G) = q₂.out * (t₂.1 : G) :=
        congrArg Subtype.val ht
      have hq : q₁ = q₂ := by
        calc
          q₁ = DoubleCoset.mk H.toSubgroup K.toSubgroup q₁.out :=
            (DoubleCoset.out_eq' q₁).symm
          _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
              (q₁.out * (t₁.1 : G)) := by
            symm
            exact DoubleCoset.mk_mul_mem t₁.1 q₁.out
          _ = DoubleCoset.mk H.toSubgroup K.toSubgroup
              (q₂.out * (t₂.1 : G)) := congrArg _ htG
          _ = DoubleCoset.mk H.toSubgroup K.toSubgroup q₂.out :=
            DoubleCoset.mk_mul_mem t₂.1 q₂.out
          _ = q₂ := DoubleCoset.out_eq' q₂
      subst q₂
      have htG' : (t₁.1 : G) = (t₂.1 : G) := mul_left_cancel htG
      have htK : t₁.1 = t₂.1 := by
        apply Subtype.ext
        exact htG'
      have htt : t₁ = t₂ := Subtype.ext htK
      subst t₂
      rfl,
    by
      intro s
      obtain ⟨p, hp⟩ := s.2
      refine ⟨p, ?_⟩
      apply Subtype.ext
      exact hp⟩

variable (X : TopRep.{max v w} k G)

/-- The crossed-homomorphism sum of the Mackey stabilizer transfers, computed
from a chosen family of local right transversals. -/
noncomputable def mackeyCrossedSumWithTransversal (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    continuousCrossedHom (TopRep.res K.subtype X) := by
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  exact ∑ q : DoubleCoset.Quotient (H : Set G) K,
    mackeyTransferCrossedWithTransversal X H K q.out (T q)
      (mackeyConjugateCrossed X H K q.out f)

/-- Restricting a transfer computed with the assembled transversal is the sum
of the transfers from the Mackey stabilizers, at the crossed-homomorphism
level. -/
lemma transferCrossed_mackey_apply (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) (g : K) :
    (transferCrossed X H (mackeyAssembledRightTransversal H K T) f).1 (g : G) =
      (mackeyCrossedSumWithTransversal X H K T f).1 g := by
  classical
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  let _ (q : DoubleCoset.Quotient (H : Set G) K) :
      Fintype (Subtype (T q : Set K)) := (T q).2.finite_right.fintype
  let S := mackeyAssembledRightTransversal H K T
  let _ : Fintype (Subtype (S : Set G)) := S.2.finite_right.fintype
  let e := mackeyAssembledTransversalEquiv H K T
  change _ =
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)).1 g
  rw [show
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)).1 g =
      ∑ q : DoubleCoset.Quotient (H : Set G) K,
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f)).1 g from by
    let F := fun q : DoubleCoset.Quotient (H : Set G) K =>
      mackeyTransferCrossedWithTransversal X H K q.out (T q)
        (mackeyConjugateCrossed X H K q.out f)
    have hcoe :
        ((↑(∑ q, F q) : C(K, X))) = ∑ q, (F q).1 := by
      simpa only using
        (Submodule.coe_sum (p := continuousCrossedHom (TopRep.res K.subtype X))
          F Finset.univ)
    calc
      (∑ q, F q).1 g = (∑ q, (F q).1) g :=
        congrArg (fun c : C(K, X) => c g) hcoe
      _ = ∑ q, (F q).1 g := by
        change ContinuousMap.evalCLM k g (∑ q, (F q).1) = _
        rw [map_sum]
        rfl]
  rw [transferCrossed_apply]
  calc
    (∑ s : Subtype (S : Set G),
        X.ρ (s.1⁻¹) (f.1 (factor S s (g : G)))) =
      ∑ p : Sigma fun q => Subtype (T q : Set K),
        X.ρ ((e p).1⁻¹) (f.1 (factor S (e p) (g : G))) := by
          exact (e.sum_comp fun s : Subtype (S : Set G) =>
            X.ρ (s.1⁻¹) (f.1 (factor S s (g : G)))).symm
    _ = ∑ q : DoubleCoset.Quotient (H : Set G) K,
        ∑ t : Subtype (T q : Set K),
          X.ρ ((q.out * (t.1 : G))⁻¹)
            (f.1 (⟨q.out *
              (((factor (G := K) (T q) t g :
                mackeyOpenStabilizer H K q.out) : K) : G) * q.out⁻¹,
              (factor (G := K) (T q) t g).2⟩ : H)) := by
          rw [Fintype.sum_sigma]
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro t _
          change X.ρ
              ((mackeyAssembledRepresentativeMem H K T q t).1⁻¹)
              (f.1 (factor S
                (mackeyAssembledRepresentativeMem H K T q t) (g : G))) = _
          rw [mackeyAssembledRepresentativeMem_coe,
            mackeyAssembled_factor]
    _ = ∑ q : DoubleCoset.Quotient (H : Set G) K,
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f)).1 g := by
          apply Finset.sum_congr rfl
          intro q _
          let _ := mackeyOpenStabilizerFiniteIndex H K q.out
          rw [show mackeyTransferCrossedWithTransversal X H K q.out (T q) =
              transferCrossed (TopRep.res K.subtype X)
                (mackeyOpenStabilizer H K q.out) (T q) from rfl]
          rw [transferCrossed_apply]
          apply Finset.sum_congr rfl
          intro t _
          rw [mackeyConjugateCrossed_apply]
          change X.ρ ((q.out * (t.1 : G))⁻¹) _ =
            X.ρ (t.1 : G)⁻¹ (X.ρ q.out⁻¹ _)
          rw [mul_inv_rev, rho_mul_apply]
          apply congrArg (X.ρ ((t.1 : G)⁻¹ * q.out⁻¹))
          apply congrArg f.1
          apply Subtype.ext
          rfl

/-- Crossed-homomorphism form of the degree-one Mackey decomposition for the
assembled ambient transversal. -/
lemma crossedRestrict_transferCrossed_mackey (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (T : (q : DoubleCoset.Quotient (H : Set G) K) ->
      (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal)
    (f : continuousCrossedHom (TopRep.res H.subtype X)) :
    crossedRestrict X K
        (transferCrossed X H (mackeyAssembledRightTransversal H K T) f) =
      mackeyCrossedSumWithTransversal X H K T f := by
  ext g
  exact transferCrossed_mackey_apply X H K T f g

/-- A canonical right transversal for each Mackey stabilizer. -/
noncomputable def mackeyStabilizerRightTransversal (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex]
    (q : DoubleCoset.Quotient (H : Set G) K) :
    (mackeyOpenStabilizer H K q.out).toSubgroup.RightTransversal := by
  let _ := mackeyOpenStabilizerFiniteIndex H K q.out
  exact default

/-- The ambient right transversal assembled from canonical double-coset
representatives and canonical stabilizer transversals. -/
noncomputable def mackeyRightTransversal (H K : OpenSubgroup G)
    [H.toSubgroup.FiniteIndex] : H.toSubgroup.RightTransversal :=
  mackeyAssembledRightTransversal H K (mackeyStabilizerRightTransversal H K)

set_option maxHeartbeats 2000000 in
/-- Quotient-level degree-one Mackey formula. -/
lemma crossedQuotientRestrict_comp_transferQuotient_mackey
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] :
    (crossedQuotientRestrict X K).comp
        (transferQuotient X H (mackeyRightTransversal H K)) =
      mackeyDoubleCosetSum X H K := by
  classical
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  let T := mackeyStabilizerRightTransversal H K
  apply ContinuousLinearMap.ext
  intro z
  refine Submodule.Quotient.induction_on _ z ?_
  intro f
  change
    (principalCocycles (TopRep.res K.subtype X)).mkQ
        (crossedRestrict X K
          (transferCrossed X H (mackeyAssembledRightTransversal H K T) f)) =
      mackeyDoubleCosetSum X H K
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f)
  rw [crossedRestrict_transferCrossed_mackey X H K T f]
  change
    (principalCocycles (TopRep.res K.subtype X)).mkQ
        (∑ q : DoubleCoset.Quotient (H : Set G) K,
          mackeyTransferCrossedWithTransversal X H K q.out (T q)
            (mackeyConjugateCrossed X H K q.out f)) = _
  rw [map_sum]
  change
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      (principalCocycles (TopRep.res K.subtype X)).mkQ
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f))) =
      (∑ q : DoubleCoset.Quotient (H : Set G) K,
        mackeyDoubleCosetSummand X H K q)
          ((principalCocycles (TopRep.res H.subtype X)).mkQ f)
  rw [show
    (∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyDoubleCosetSummand X H K q)
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) =
      ∑ q : DoubleCoset.Quotient (H : Set G) K,
        mackeyDoubleCosetSummand X H K q
          ((principalCocycles (TopRep.res H.subtype X)).mkQ f) from by
    simpa only using
      (sum_apply Finset.univ
        (fun q : DoubleCoset.Quotient (H : Set G) K =>
          mackeyDoubleCosetSummand X H K q)
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f))]
  apply Finset.sum_congr rfl
  intro q _
  symm
  calc
    mackeyDoubleCosetSummand X H K q
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) =
      mackeySummandQuotient X H K q.out
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) := by
          have hmap : mackeyDoubleCosetSummand X H K q =
              mackeyDoubleCosetSummand X H K
                (DoubleCoset.mk H.toSubgroup K.toSubgroup q.out) :=
            congrArg (mackeyDoubleCosetSummand X H K)
              (DoubleCoset.out_eq' q).symm
          rw [hmap, mackeyDoubleCosetSummand_mk]
    _ = mackeySummandQuotientWithTransversal X H K q.out (T q)
        ((principalCocycles (TopRep.res H.subtype X)).mkQ f) := by
          rw [mackeySummandQuotient_eq_withTransversal X H K q.out (T q)]
    _ = (principalCocycles (TopRep.res K.subtype X)).mkQ
        (mackeyTransferCrossedWithTransversal X H K q.out (T q)
          (mackeyConjugateCrossed X H K q.out f)) := by
          rw [mackeySummandQuotientWithTransversal_mk]

/-- Categorical form of the quotient-level Mackey formula. -/
@[reassoc]
lemma transferQuotient_comp_crossedQuotientRestrict_mackey_hom
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (transferQuotient X H (mackeyRightTransversal H K)) ≫
        TopModuleCat.ofHom (crossedQuotientRestrict X K) =
      TopModuleCat.ofHom (mackeyDoubleCosetSum X H K) := by
  ext z
  exact DFunLike.congr_fun
    (crossedQuotientRestrict_comp_transferQuotient_mackey X H K) z

/-- The coefficient comparison for the conjugation map from a Mackey
stabilizer to the left subgroup. -/
def mackeyCoefficientHom (H K : OpenSubgroup G) (x : G) :
    TopRep.res (mackeyStabilizerToLeft H K x)
        (TopRep.res H.subtype X) ⟶
      TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X) :=
  TopRep.ofHom {
    __ := X.ρ x⁻¹
    isIntertwining' := by
      intro l
      ext z
      change X.ρ x⁻¹
          (X.ρ (x * (((l : mackeyOpenStabilizer H K x) : K) : G) * x⁻¹) z) =
        X.ρ (((l : mackeyOpenStabilizer H K x) : K) : G) (X.ρ x⁻¹ z)
      rw [rho_mul_apply, rho_mul_apply]
      congr 2
      group }

set_option maxHeartbeats 800000 in
/-- Evaluation in degree one of the homogeneous-cochain map induced by a group
homomorphism and compatible coefficient morphism. -/
lemma cochainsMap_one_apply
    {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    {A : TopRep.{max v w} k G} {B : TopRep.{max v w} k J}
    (phi : J →ₜ* G) (f : TopRep.res phi A ⟶ B)
    (sigma : (TopRep.homogeneousCochains A).X 1) (h : J) :
    (((cochainsMap phi f).f 1 sigma).1 1 h) =
      f.hom (sigma.1 1 (phi h)) := by
  have hc := congrArg (fun F => F sigma) (cochainsMap_f_hom phi f 1)
  refine (congrArg (fun tau => tau.1 1 h) hc).trans ?_
  change ((resolutionMap phi f (1 + 1)).hom sigma.1) 1 h = _
  have hr₂ := congrArg (fun r => r.hom sigma.1) (resolutionMap_succ phi f 1)
  refine (congrArg (fun tau => tau 1 h) hr₂).trans ?_
  have ho := ContRepresentation.coind₁ResMap_apply phi
    (resolutionMap phi f 1).hom sigma.1 1
  refine (congrArg (fun tau => tau h) ho).trans ?_
  rw [map_one]
  have hr₁ := congrArg (fun r => r.hom (sigma.1 1))
    (resolutionMap_succ phi f 0)
  refine (congrArg (fun tau => tau h) hr₁).trans ?_
  exact ContRepresentation.coind₁ResMap_apply phi f.hom (sigma.1 1) h

set_option maxHeartbeats 800000 in
/-- The explicit conjugation/restriction map on crossed homomorphisms agrees
with the map induced on degree-one cocycles. -/
lemma cocyclesOneCrossedIso_mackey (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace H]
    [LocallyCompactSpace K]
    [LocallyCompactSpace (mackeyOpenStabilizer H K x)] :
    cocyclesMap (mackeyStabilizerToLeft H K x)
          (mackeyCoefficientHom X H K x) 1 ≫
        (cocyclesOneCrossedIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).hom =
      (cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
        TopModuleCat.ofHom (mackeyConjugateCrossed X H K x) := by
  ext σ l
  simp only [TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
    ConcreteCategory.hom_ofHom]
  change
    (((cocyclesOneCrossedIso
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).hom
      (cocyclesMap (mackeyStabilizerToLeft H K x)
        (mackeyCoefficientHom X H K x) 1 σ)).1 l) =
      (mackeyConjugateCrossed X H K x
        ((cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom σ)).1 l
  rw [cocyclesOneCrossedIso_hom_apply, mackeyConjugateCrossed_apply,
    cocyclesOneCrossedIso_hom_apply]
  have hh := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i
      (cochainsMap (mackeyStabilizerToLeft H K x)
        (mackeyCoefficientHom X H K x)) 1) σ
  simp only [ConcreteCategory.comp_apply] at hh
  change
    (((HomologicalComplex.iCycles
        (TopRep.homogeneousCochains
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))) 1)
      ((HomologicalComplex.cyclesMap
        (cochainsMap (mackeyStabilizerToLeft H K x)
          (mackeyCoefficientHom X H K x)) 1) σ)).1 1 l) = _
  refine (congrArg (fun τ => τ.1 1 l) hh).trans ?_
  exact cochainsMap_one_apply (mackeyStabilizerToLeft H K x)
    (mackeyCoefficientHom X H K x)
    ((TopRep.homogeneousCochains (TopRep.res H.subtype X)).iCycles 1 σ) l

/-- The crossed-homomorphism conjugation map commutes with passage to principal
cocycle quotients. -/
lemma mackeyConjugateCrossed_comp_mkQL (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] :
    TopModuleCat.ofHom (mackeyConjugateCrossed X H K x) ≫
        TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).mkQL =
      TopModuleCat.ofHom
          (principalCocycles (TopRep.res H.subtype X)).mkQL ≫
        TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) := by
  ext f
  rfl

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The native cohomology map induced by conjugation and coefficient transport
agrees with the conjugation map on crossed-homomorphism quotients. -/
lemma homologyQuotientIso_mackey (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace H]
    [LocallyCompactSpace K]
    [LocallyCompactSpace (mackeyOpenStabilizer H K x)] :
    map (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1 ≫
        (homologyQuotientIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).hom =
      (homologyQuotientIso (TopRep.res H.subtype X)).hom ≫
        TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) := by
  apply (cancel_epi (π (TopRep.res H.subtype X) 1)).1
  calc
    π (TopRep.res H.subtype X) 1 ≫
          (map (mackeyStabilizerToLeft H K x)
              (mackeyCoefficientHom X H K x) 1 ≫
            (homologyQuotientIso
              (TopRep.res (mackeyOpenStabilizer H K x).subtype
                (TopRep.res K.subtype X))).hom) =
        (π (TopRep.res H.subtype X) 1 ≫
          map (mackeyStabilizerToLeft H K x)
            (mackeyCoefficientHom X H K x) 1) ≫
          (homologyQuotientIso
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).hom := (Category.assoc _ _ _).symm
    _ = (cocyclesMap (mackeyStabilizerToLeft H K x)
            (mackeyCoefficientHom X H K x) 1 ≫
          π (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X)) 1) ≫
        (homologyQuotientIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).hom := by
      rw [π_map]
      rfl
    _ = cocyclesMap (mackeyStabilizerToLeft H K x)
            (mackeyCoefficientHom X H K x) 1 ≫
        (π (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X)) 1 ≫
          (homologyQuotientIso
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).hom) := Category.assoc _ _ _
    _ = cocyclesMap (mackeyStabilizerToLeft H K x)
            (mackeyCoefficientHom X H K x) 1 ≫
        ((cocyclesOneCrossedIso
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).hom ≫
          TopModuleCat.ofHom
            (principalCocycles
              (TopRep.res (mackeyOpenStabilizer H K x).subtype
                (TopRep.res K.subtype X))).mkQL) := by
      rw [π_comp_homologyQuotientIso]
    _ = (cocyclesMap (mackeyStabilizerToLeft H K x)
            (mackeyCoefficientHom X H K x) 1 ≫
          (cocyclesOneCrossedIso
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).hom) ≫
        TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).mkQL := (Category.assoc _ _ _).symm
    _ = ((cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
          TopModuleCat.ofHom (mackeyConjugateCrossed X H K x)) ≫
        TopModuleCat.ofHom
          (principalCocycles
            (TopRep.res (mackeyOpenStabilizer H K x).subtype
              (TopRep.res K.subtype X))).mkQL := by
      rw [cocyclesOneCrossedIso_mackey]
    _ = (cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
        (TopModuleCat.ofHom (mackeyConjugateCrossed X H K x) ≫
          TopModuleCat.ofHom
            (principalCocycles
              (TopRep.res (mackeyOpenStabilizer H K x).subtype
                (TopRep.res K.subtype X))).mkQL) := Category.assoc _ _ _
    _ = (cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
        (TopModuleCat.ofHom
            (principalCocycles (TopRep.res H.subtype X)).mkQL ≫
          TopModuleCat.ofHom (mackeyConjugateQuotient X H K x)) := by
      rw [mackeyConjugateCrossed_comp_mkQL]
    _ = ((cocyclesOneCrossedIso (TopRep.res H.subtype X)).hom ≫
          TopModuleCat.ofHom
            (principalCocycles (TopRep.res H.subtype X)).mkQL) ≫
        TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) :=
      (Category.assoc _ _ _).symm
    _ = (π (TopRep.res H.subtype X) 1 ≫
          (homologyQuotientIso (TopRep.res H.subtype X)).hom) ≫
        TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) := by
      rw [π_comp_homologyQuotientIso]
    _ = π (TopRep.res H.subtype X) 1 ≫
        ((homologyQuotientIso (TopRep.res H.subtype X)).hom ≫
          TopModuleCat.ofHom (mackeyConjugateQuotient X H K x)) :=
      Category.assoc _ _ _

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugation and restriction commute with the crossed-quotient-to-degree-one
cohomology comparison. -/
lemma degreeOneIso_mackey (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace H]
    [LocallyCompactSpace K]
    [LocallyCompactSpace (mackeyOpenStabilizer H K x)] :
    TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) ≫
        (degreeOneIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).hom =
      (degreeOneIso (TopRep.res H.subtype X)).hom ≫
        map (mackeyStabilizerToLeft H K x)
          (mackeyCoefficientHom X H K x) 1 := by
  apply (cancel_mono
    (homologyQuotientIso
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).hom).1
  rw [degreeOneIso, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [Category.assoc, homologyQuotientIso_mackey, ← Category.assoc,
    degreeOneIso, Iso.symm_hom, Iso.inv_hom_id, Category.id_comp]

set_option maxHeartbeats 800000 in
/-- A reassociated inverse form of `degreeOneIso_mackey`. -/
lemma map_comp_degreeOneIso_inv_mackey (H K : OpenSubgroup G) (x : G)
    [TopRep.JointlyContinuous X] [LocallyCompactSpace H]
    [LocallyCompactSpace K]
    [LocallyCompactSpace (mackeyOpenStabilizer H K x)] :
    map (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1 ≫
        (degreeOneIso
          (TopRep.res (mackeyOpenStabilizer H K x).subtype
            (TopRep.res K.subtype X))).inv =
      (degreeOneIso (TopRep.res H.subtype X)).inv ≫
        TopModuleCat.ofHom (mackeyConjugateQuotient X H K x) := by
  apply (cancel_mono
    (degreeOneIso
      (TopRep.res (mackeyOpenStabilizer H K x).subtype
        (TopRep.res K.subtype X))).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Category.assoc, degreeOneIso_mackey, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- Canonical degree-one corestriction unfolds through the crossed-quotient
comparison and the canonical stabilizer transversal. -/
lemma corestrictionOne_eq_degreeOne
    {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
    (Y : TopRep.{max v w} k J) (L : OpenSubgroup J)
    [L.toSubgroup.FiniteIndex] [TopRep.JointlyContinuous Y]
    [LocallyCompactSpace J] [LocallyCompactSpace L] :
    corestrictionOne Y L =
      (degreeOneIso (TopRep.res L.subtype Y)).inv ≫
        TopModuleCat.ofHom (transferQuotient Y L default) ≫
          (degreeOneIso Y).hom :=
  rfl

/-- The native degree-one summand attached to a double coset: conjugate and
restrict to its Mackey stabilizer, then corestrict to the right subgroup. -/
noncomputable def mackeyDoubleCosetOneSummand
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    (q : DoubleCoset.Quotient (H : Set G) K) :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶
      continuousCohomology 1 (TopRep.res K.subtype X) := by
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace (mackeyOpenStabilizer H K q.out) :=
    (mackeyOpenStabilizer H K q.out).isOpen'.locallyCompactSpace
  let _ := mackeyOpenStabilizerFiniteIndex H K q.out
  exact map (mackeyStabilizerToLeft H K q.out)
      (mackeyCoefficientHom X H K q.out) 1 ≫
    corestrictionOne (TopRep.res K.subtype X)
      (mackeyOpenStabilizer H K q.out)

set_option maxHeartbeats 2000000 in
/-- The native double-coset summand agrees with the representative-independent
crossed-quotient summand transported through the degree-one comparison. -/
lemma mackeyDoubleCosetOneSummand_eq_quotient
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G]
    (q : DoubleCoset.Quotient (H : Set G) K) :
    let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
    let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
    mackeyDoubleCosetOneSummand X H K q =
      (degreeOneIso (TopRep.res H.subtype X)).inv ≫
        TopModuleCat.ofHom (mackeyDoubleCosetSummand X H K q) ≫
          (degreeOneIso (TopRep.res K.subtype X)).hom := by
  dsimp only
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace (mackeyOpenStabilizer H K q.out) :=
    (mackeyOpenStabilizer H K q.out).isOpen'.locallyCompactSpace
  let _ := mackeyOpenStabilizerFiniteIndex H K q.out
  let a := (degreeOneIso (TopRep.res H.subtype X)).inv
  let c := TopModuleCat.ofHom (mackeyConjugateQuotient X H K q.out)
  let t := TopModuleCat.ofHom
    (transferQuotient (TopRep.res K.subtype X)
      (mackeyOpenStabilizer H K q.out) default)
  let b := (degreeOneIso (TopRep.res K.subtype X)).hom
  have hconj :
      map (mackeyStabilizerToLeft H K q.out)
            (mackeyCoefficientHom X H K q.out) 1 ≫
          (degreeOneIso
            (TopRep.res (mackeyOpenStabilizer H K q.out).subtype
              (TopRep.res K.subtype X))).inv =
        a ≫ c := by
    dsimp only [a, c]
    exact map_comp_degreeOneIso_inv_mackey X H K q.out
  have hq :
      TopModuleCat.ofHom (mackeyDoubleCosetSummand X H K q) =
        c ≫ t := by
    dsimp only [c, t]
    have hmap : mackeyDoubleCosetSummand X H K q =
        mackeyDoubleCosetSummand X H K
          (DoubleCoset.mk H.toSubgroup K.toSubgroup q.out) :=
      congrArg (mackeyDoubleCosetSummand X H K)
        (DoubleCoset.out_eq' q).symm
    rw [hmap, mackeyDoubleCosetSummand_mk,
      mackeySummandQuotient_eq_withTransversal X H K q.out default]
    rfl
  rw [mackeyDoubleCosetOneSummand]
  rw [corestrictionOne_eq_degreeOne]
  calc
    _ = (a ≫ c) ≫ t ≫ b := by
      dsimp only [a, c, t, b]
      simpa only [Category.assoc] using congrArg
        (fun f => f ≫ t ≫ b)
        hconj
    _ = a ≫ TopModuleCat.ofHom (mackeyDoubleCosetSummand X H K q) ≫ b := by
      simpa only [Category.assoc] using congrArg
        (fun f => a ≫ f ≫ b) hq.symm
    _ = (degreeOneIso (TopRep.res H.subtype X)).inv ≫
        TopModuleCat.ofHom (mackeyDoubleCosetSummand X H K q) ≫
          (degreeOneIso (TopRep.res K.subtype X)).hom := by
      rfl

/-- The finite native degree-one Mackey sum over `H \\ G / K`. -/
noncomputable def mackeyDoubleCosetOneSum
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    continuousCohomology 1 (TopRep.res H.subtype X) ⟶
      continuousCohomology 1 (TopRep.res K.subtype X) := by
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  exact (degreeOneIso (TopRep.res H.subtype X)).inv ≫
    TopModuleCat.ofHom (mackeyDoubleCosetSum X H K) ≫
      (degreeOneIso (TopRep.res K.subtype X)).hom

set_option maxHeartbeats 800000 in
/-- The native Mackey sum is the finite sum of its double-coset summands. -/
lemma mackeyDoubleCosetOneSum_eq_sum
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    mackeyDoubleCosetOneSum X H K =
      (@Finset.univ (DoubleCoset.Quotient (H : Set G) K) (Fintype.ofFinite _)).sum
        (mackeyDoubleCosetOneSummand X H K) := by
  classical
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  let _ : Fintype (DoubleCoset.Quotient (H : Set G) K) := Fintype.ofFinite _
  change mackeyDoubleCosetOneSum X H K =
    ∑ q : DoubleCoset.Quotient (H : Set G) K,
      mackeyDoubleCosetOneSummand X H K q
  simp only [mackeyDoubleCosetOneSum, mackeyDoubleCosetSum]
  let F := fun q : DoubleCoset.Quotient (H : Set G) K =>
    mackeyDoubleCosetSummand X H K q
  have hof (s : Finset (DoubleCoset.Quotient (H : Set G) K)) :
      TopModuleCat.ofHom (∑ q ∈ s, F q) =
        ∑ q ∈ s, TopModuleCat.ofHom (F q) := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert q s hq ih =>
        rw [Finset.sum_insert hq, Finset.sum_insert hq]
        change TopModuleCat.ofHom (F q) +
            TopModuleCat.ofHom (∑ x ∈ s, F x) =
          TopModuleCat.ofHom (F q) +
            ∑ x ∈ s, TopModuleCat.ofHom (F x)
        rw [ih]
  rw [hof Finset.univ]
  let a := (degreeOneIso (TopRep.res H.subtype X)).inv
  let b := fun q : DoubleCoset.Quotient (H : Set G) K =>
    TopModuleCat.ofHom (F q)
  let c := (degreeOneIso (TopRep.res K.subtype X)).hom
  calc
    a ≫ (∑ q, b q) ≫ c = (a ≫ ∑ q, b q) ≫ c :=
      (Category.assoc _ _ _).symm
    _ = (∑ q, a ≫ b q) ≫ c := by
      rw [show a ≫ (∑ q, b q) = ∑ q, a ≫ b q from by
        simpa only using (Preadditive.comp_sum Finset.univ a b)]
    _ = ∑ q, (a ≫ b q) ≫ c := by
      simpa only using (Preadditive.sum_comp Finset.univ (fun q => a ≫ b q) c)
    _ = ∑ q, a ≫ b q ≫ c := by
      simp only [Category.assoc]
    _ = ∑ q, mackeyDoubleCosetOneSummand X H K q := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [a, b, c, F] using
        (mackeyDoubleCosetOneSummand_eq_quotient X H K q).symm

set_option maxHeartbeats 800000 in
/-- Restriction to `K` after canonical corestriction from `H` is the finite
degree-one Mackey sum over `H \\ G / K`. -/
lemma corestrictionOne_comp_restriction_mackey
    (H K : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    [TopRep.JointlyContinuous X] [LocallyCompactSpace G] :
    let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
    let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
    corestrictionOne X H ≫
          map (openSubgroupInclusion K) (restrictionCoeffHom X K) 1 =
        mackeyDoubleCosetOneSum X H K := by
  dsimp only
  let _ : LocallyCompactSpace H := H.isOpen'.locallyCompactSpace
  let _ : LocallyCompactSpace K := K.isOpen'.locallyCompactSpace
  rw [corestrictionOne_eq_withTransversal X H (mackeyRightTransversal H K)]
  simp only [corestrictionOneWithTransversal, degreeOneIso_inv,
    mackeyDoubleCosetOneSum]
  rw [Category.assoc, Category.assoc, ← degreeOneIso_restrict X K]
  rw [transferQuotient_comp_crossedQuotientRestrict_mackey_hom_assoc]


end CorestrictionTransversal

end ContinuousCohomology

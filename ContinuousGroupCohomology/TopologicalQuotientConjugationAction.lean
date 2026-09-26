/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Formalization Worker A
-/
module

public import ContinuousGroupCohomology.ContinuousGroupExtension
public import ContinuousGroupCohomology.QuotientConjugationAction
public import Mathlib.Topology.Algebra.Group.TopologicalAbelianization

/-!
# Quotient conjugation on topological abelianization

For a continuous extension `1 → N → E → Q → 1`, this file refines
the algebraic quotient conjugation action to the topological abelianization of
the kernel.  The closed-embedding part of the extension witness makes the
conjugation automorphisms of `N` continuous.  These automorphisms preserve the
closure of the commutator subgroup and hence descend to bundled continuous
automorphisms of `TopologicalAbelianization N`.

Pinned mathlib does not give `ContinuousMulEquiv X X` a group structure.
Accordingly, the homomorphism laws are retained by a `MulAut`-valued action,
while `quotientConjActTopologicalAbelianizationContinuous` provides the bundled
continuous automorphism at every quotient element.  The lift formula,
lift-independence, and naturality under continuous extension equivalences make
the relationship between those two views explicit.
-/

set_option warningAsError true

@[expose] public section

noncomputable section

universe uN uE uQ uH

namespace TopologicalAbelianization

variable (G : Type uN) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The canonical homomorphism from algebraic abelianization to topological
abelianization. -/
def fromAbelianization : Abelianization G →* TopologicalAbelianization G :=
  Abelianization.lift
    (QuotientGroup.mk' (commutator G).topologicalClosure)

@[simp]
theorem fromAbelianization_apply_of (g : G) :
    fromAbelianization G (Abelianization.of g) = QuotientGroup.mk g := rfl

end TopologicalAbelianization

namespace ContinuousMulEquiv

variable {G : Type uN} {H : Type uH}
  [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- A continuous multiplicative equivalence descends to a continuous
multiplicative equivalence of quotient groups when it carries the first
normal subgroup onto the second. -/
def quotientGroupCongr (e : G ≃ₜ* H) (N : Subgroup G) (M : Subgroup H)
    [N.Normal] [M.Normal] (he : N.map e = M) : G ⧸ N ≃ₜ* H ⧸ M where
  toMulEquiv := QuotientGroup.congr N M e.toMulEquiv he
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk N).continuous_iff]
    exact QuotientGroup.continuous_mk.comp e.continuous
  continuous_invFun := by
    rw [(QuotientGroup.isQuotientMap_mk M).continuous_iff]
    exact QuotientGroup.continuous_mk.comp e.symm.continuous

end ContinuousMulEquiv

namespace ContinuousGroupExtension

variable {N : Type uN} {E : Type uE} {Q : Type uQ}
  [Group N] [Group E] [Group Q]
  [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q]
  [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q]

/-- Conjugation on the kernel is continuous.  The proof uses the fact that the
kernel inclusion is an inducing map, not an independently assumed topology on
the abstract conjugation automorphism. -/
theorem continuous_conjAct (S : ContinuousGroupExtension N E Q) (e : E) :
    Continuous (S.toGroupExtension.conjAct e) := by
  rw [S.isSES.isClosedEmbedding.isInducing.continuous_iff]
  have h : Continuous (fun n : N => e * S.inl n * e⁻¹) :=
    (continuous_const.mul S.isSES.isClosedEmbedding.continuous).mul continuous_const
  convert h using 1
  funext n
  exact S.toGroupExtension.inl_conjAct_comm

/-- Conjugation by a middle-group element, bundled as a continuous
multiplicative automorphism of the kernel. -/
def conjActContinuous (S : ContinuousGroupExtension N E Q) (e : E) : N ≃ₜ* N where
  toMulEquiv := S.toGroupExtension.conjAct e
  continuous_toFun := S.continuous_conjAct e
  continuous_invFun := by
    have h : (S.toGroupExtension.conjAct e).invFun =
        S.toGroupExtension.conjAct e⁻¹ := by
      funext n
      have hn := DFunLike.congr_fun
        (map_inv S.toGroupExtension.conjAct e) n
      exact hn.symm
    rw [h]
    exact S.continuous_conjAct e⁻¹

/-- Continuous conjugation preserves the closure of the kernel's commutator
subgroup. -/
theorem map_topologicalClosure_commutator_conjActContinuous
    (S : ContinuousGroupExtension N E Q) (e : E) :
    (commutator N).topologicalClosure.map (S.conjActContinuous e) =
      (commutator N).topologicalClosure := by
  apply SetLike.ext'
  change (S.conjActContinuous e) '' closure (commutator N : Set N) =
    closure (commutator N : Set N)
  rw [show (S.conjActContinuous e) '' closure (commutator N : Set N) =
      closure ((S.conjActContinuous e) '' (commutator N : Set N)) from
    (S.conjActContinuous e).toHomeomorph.image_closure _]
  congr 1
  have hc : (commutator N).map (S.conjActContinuous e).toMulEquiv.toMonoidHom =
      commutator N := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (S.conjActContinuous e).surjective]
    rfl
  exact congrArg (fun K : Subgroup N => (K : Set N)) hc

/-- Conjugation by a middle-group element on the topological abelianization of
the kernel, bundled as a continuous automorphism. -/
def conjActTopologicalAbelianizationContinuous
    (S : ContinuousGroupExtension N E Q) (e : E) :
    TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N :=
  (S.conjActContinuous e).quotientGroupCongr
    (commutator N).topologicalClosure (commutator N).topologicalClosure
    (S.map_topologicalClosure_commutator_conjActContinuous e)

/-- Conjugation on topological abelianization sends a representative to the
class of its conjugate. -/
@[simp]
theorem conjActTopologicalAbelianizationContinuous_apply_mk
    (S : ContinuousGroupExtension N E Q) (e : E) (n : N) :
    S.conjActTopologicalAbelianizationContinuous e (QuotientGroup.mk n) =
      QuotientGroup.mk (S.toGroupExtension.conjAct e n) := rfl

/-- The middle-group action on topological abelianization.  Its values admit
the bundled-continuous refinement
`conjActTopologicalAbelianizationContinuous`. -/
def conjActTopologicalAbelianization (S : ContinuousGroupExtension N E Q) :
    E →* MulAut (TopologicalAbelianization N) where
  toFun e := (S.conjActTopologicalAbelianizationContinuous e).toMulEquiv
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    change QuotientGroup.mk (S.toGroupExtension.conjAct 1 n) = QuotientGroup.mk n
    rw [map_one]
    rfl
  map_mul' e e' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
    change QuotientGroup.mk (S.toGroupExtension.conjAct (e * e') n) =
      QuotientGroup.mk
        (S.toGroupExtension.conjAct e (S.toGroupExtension.conjAct e' n))
    rw [map_mul]
    rfl

/-- An embedded kernel element acts trivially on topological abelianization. -/
@[simp]
theorem conjActTopologicalAbelianization_inl
    (S : ContinuousGroupExtension N E Q) (n : N) :
    S.conjActTopologicalAbelianization (S.inl n) = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  change QuotientGroup.mk (S.toGroupExtension.conjAct (S.inl n) x) =
    QuotientGroup.mk x
  have h : S.toGroupExtension.conjAct (S.inl n) x = n * x * n⁻¹ := by
    apply S.inl_injective
    rw [S.toGroupExtension.inl_conjAct_comm]
    simp
  rw [h]
  simp

/-- The kernel of the extension projection acts trivially on topological
abelianization. -/
theorem ker_rightHom_le_ker_conjActTopologicalAbelianization
    (S : ContinuousGroupExtension N E Q) :
    S.rightHom.ker ≤ S.conjActTopologicalAbelianization.ker := by
  rw [← S.range_inl_eq_ker_rightHom]
  rintro e ⟨n, rfl⟩
  rw [MonoidHom.mem_ker]
  exact S.conjActTopologicalAbelianization_inl n

/-- The quotient-group action on the topological abelianization of the kernel. -/
noncomputable def quotientConjActTopologicalAbelianization
    (S : ContinuousGroupExtension N E Q) :
    Q →* MulAut (TopologicalAbelianization N) :=
  (QuotientGroup.lift S.rightHom.ker S.conjActTopologicalAbelianization
    S.ker_rightHom_le_ker_conjActTopologicalAbelianization).comp
      S.toGroupExtension.quotientKerRightHomEquivRight.symm.toMonoidHom

/-- The quotient action evaluated on a projected middle-group element is the
corresponding conjugation action. -/
@[simp]
theorem quotientConjActTopologicalAbelianization_rightHom
    (S : ContinuousGroupExtension N E Q) (e : E) :
    S.quotientConjActTopologicalAbelianization (S.rightHom e) =
      S.conjActTopologicalAbelianization e := by
  change QuotientGroup.lift S.rightHom.ker S.conjActTopologicalAbelianization
    S.ker_rightHom_le_ker_conjActTopologicalAbelianization
      (S.toGroupExtension.quotientKerRightHomEquivRight.symm (S.rightHom e)) = _
  have hq : S.toGroupExtension.quotientKerRightHomEquivRight.symm (S.rightHom e) =
      QuotientGroup.mk' S.rightHom.ker e := by
    apply S.toGroupExtension.quotientKerRightHomEquivRight.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [hq]
  exact QuotientGroup.lift_mk' S.rightHom.ker
    S.ker_rightHom_le_ker_conjActTopologicalAbelianization e

/-- The value of the quotient action at any element, bundled as a continuous
automorphism of topological abelianization. -/
def quotientConjActTopologicalAbelianizationContinuous
    (S : ContinuousGroupExtension N E Q) (q : Q) :
    TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N where
  toMulEquiv := S.quotientConjActTopologicalAbelianization q
  continuous_toFun := by
    obtain ⟨e, rfl⟩ := S.rightHom_surjective q
    rw [S.quotientConjActTopologicalAbelianization_rightHom]
    exact (S.conjActTopologicalAbelianizationContinuous e).continuous
  continuous_invFun := by
    obtain ⟨e, rfl⟩ := S.rightHom_surjective q
    rw [S.quotientConjActTopologicalAbelianization_rightHom]
    exact (S.conjActTopologicalAbelianizationContinuous e).symm.continuous

/-- The bundled continuous quotient action agrees with continuous conjugation
on every lift. -/
@[simp]
theorem quotientConjActTopologicalAbelianizationContinuous_rightHom
    (S : ContinuousGroupExtension N E Q) (e : E) :
    S.quotientConjActTopologicalAbelianizationContinuous (S.rightHom e) =
      S.conjActTopologicalAbelianizationContinuous e := by
  apply ContinuousMulEquiv.ext
  intro x
  exact DFunLike.congr_fun
    (S.quotientConjActTopologicalAbelianization_rightHom e) x

/-- Arbitrary-lift formula for the continuous quotient action on a
representative of topological abelianization. -/
@[simp]
theorem quotientConjActTopologicalAbelianizationContinuous_apply_mk
    (S : ContinuousGroupExtension N E Q) (e : E) (n : N) :
    S.quotientConjActTopologicalAbelianizationContinuous
        (S.rightHom e) (QuotientGroup.mk n) =
      QuotientGroup.mk (S.toGroupExtension.conjAct e n) := by
  rw [S.quotientConjActTopologicalAbelianizationContinuous_rightHom]
  rfl

/-- Two lifts of the same quotient element induce the same bundled continuous
automorphism of topological abelianization. -/
theorem conjActTopologicalAbelianizationContinuous_eq_of_rightHom_eq
    (S : ContinuousGroupExtension N E Q) {e e' : E}
    (h : S.rightHom e = S.rightHom e') :
    S.conjActTopologicalAbelianizationContinuous e =
      S.conjActTopologicalAbelianizationContinuous e' := by
  rw [← S.quotientConjActTopologicalAbelianizationContinuous_rightHom e,
    ← S.quotientConjActTopologicalAbelianizationContinuous_rightHom e', h]

/-- Representative-level form of independence from the chosen lift. -/
theorem topologicalAbelianization_conjAct_eq_of_rightHom_eq
    (S : ContinuousGroupExtension N E Q) {e e' : E}
    (h : S.rightHom e = S.rightHom e') (n : N) :
    QuotientGroup.mk (S.toGroupExtension.conjAct e n) =
      (QuotientGroup.mk (S.toGroupExtension.conjAct e' n) :
        TopologicalAbelianization N) := by
  rw [← S.quotientConjActTopologicalAbelianizationContinuous_apply_mk e n,
    ← S.quotientConjActTopologicalAbelianizationContinuous_apply_mk e' n,
    h]

/-- The canonical map from algebraic to topological abelianization
intertwines the accepted algebraic quotient action with the topological one. -/
theorem fromAbelianization_quotientConjAct (S : ContinuousGroupExtension N E Q)
    (q : Q) (x : Abelianization N) :
    TopologicalAbelianization.fromAbelianization N
        (S.toGroupExtension.quotientConjActAbelianization q x) =
      S.quotientConjActTopologicalAbelianization q
        (TopologicalAbelianization.fromAbelianization N x) := by
  obtain ⟨e, rfl⟩ := S.rightHom_surjective q
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  rfl

namespace Equiv

variable {E' : Type uH} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E']
  {S : ContinuousGroupExtension N E Q}
  {S' : ContinuousGroupExtension N E' Q}

/-- A continuous equivalence of extensions intertwines the middle-group
actions on topological abelianization. -/
theorem conjActTopologicalAbelianization (equiv : S.Equiv S') (e : E) :
    S'.conjActTopologicalAbelianization (equiv e) =
      S.conjActTopologicalAbelianization e := by
  apply MulEquiv.ext
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective x
  change QuotientGroup.mk (S'.toGroupExtension.conjAct (equiv e) n) =
    QuotientGroup.mk (S.toGroupExtension.conjAct e n)
  congr 1
  apply S'.inl_injective
  calc
    S'.inl (S'.toGroupExtension.conjAct (equiv e) n) =
        equiv e * S'.inl n * (equiv e)⁻¹ :=
      S'.toGroupExtension.inl_conjAct_comm
    _ = equiv (e * S.inl n * e⁻¹) := by simp
    _ = equiv (S.inl (S.toGroupExtension.conjAct e n)) :=
      congrArg equiv S.toGroupExtension.inl_conjAct_comm.symm
    _ = S'.inl (S.toGroupExtension.conjAct e n) := equiv.map_inl _

/-- Equivalent continuous extensions with the same kernel and quotient have
the same quotient action on topological abelianization. -/
theorem quotientConjActTopologicalAbelianization (equiv : S.Equiv S') :
    S'.quotientConjActTopologicalAbelianization =
      S.quotientConjActTopologicalAbelianization := by
  apply MonoidHom.ext
  intro q
  obtain ⟨e, rfl⟩ := S.rightHom_surjective q
  calc
    S'.quotientConjActTopologicalAbelianization (S.rightHom e) =
        S'.quotientConjActTopologicalAbelianization (S'.rightHom (equiv e)) :=
      congrArg S'.quotientConjActTopologicalAbelianization
        (equiv.rightHom_map e).symm
    _ = S'.conjActTopologicalAbelianization (equiv e) :=
      S'.quotientConjActTopologicalAbelianization_rightHom _
    _ = S.conjActTopologicalAbelianization e :=
      equiv.conjActTopologicalAbelianization e
    _ = S.quotientConjActTopologicalAbelianization (S.rightHom e) :=
      (S.quotientConjActTopologicalAbelianization_rightHom e).symm

/-- Naturality of the bundled continuous automorphism attached to each
quotient element under an equivalence of continuous extensions. -/
theorem quotientConjActTopologicalAbelianizationContinuous
    (equiv : S.Equiv S') (q : Q) :
    S'.quotientConjActTopologicalAbelianizationContinuous q =
      S.quotientConjActTopologicalAbelianizationContinuous q := by
  apply ContinuousMulEquiv.ext
  intro x
  exact DFunLike.congr_fun
    (DFunLike.congr_fun equiv.quotientConjActTopologicalAbelianization q) x

end Equiv

end ContinuousGroupExtension

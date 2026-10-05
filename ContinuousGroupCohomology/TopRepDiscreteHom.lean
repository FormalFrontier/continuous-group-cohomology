/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.TopRepUlift
public import Mathlib.RepresentationTheory.Invariants
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Discrete linear Hom of topological representations

The carrier of `DiscreteLinHom k X Y` consists of **all** `k`-linear maps, with the
discrete topology. The conjugation representation is Mathlib's
`Representation.linHom`; we lift its operators to continuous linear maps on
the discrete carrier. Scalar continuity and joint continuity of the group
action are separate questions. In particular, finiteness of the acting group
does not make scalar multiplication continuous on an arbitrary discrete Hom.

The statements below generalize the discrete-module internal Hom of
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, corrected second
edition, §1.1: the source takes integer coefficients and a profinite group.

## References

* Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, §1.1 (including the correction to the finite-generation
  hypothesis credited to Siyan Daniel Li).
* Mathlib's representation-theory formalization by Antoine Labelle and its
  intertwining-map API by Stepan Nesterov and Edison Xie provide the algebraic
  conjugation action and the fixed-map comparison. The open-stabilizer
  criterion is from Mathlib's topological-action development by Yury Kudryashov.
-/

@[expose] public section

universe u v w x z

/-- The linear maps from `A` to `B`, equipped with a chosen discrete topology
independent of any topology on a space of continuous linear maps. -/
def DiscreteLinHom (k : Type u) (A : Type v) (B : Type w)
    [CommSemiring k] [AddCommMonoid A] [Module k A]
    [AddCommMonoid B] [Module k B] := A →ₗ[k] B

namespace DiscreteLinHom

variable {k : Type u} [CommSemiring k] {A : Type v} {B : Type w}
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]

instance instFunLike : FunLike (DiscreteLinHom k A B) A B :=
  inferInstanceAs (FunLike (A →ₗ[k] B) A B)

instance instAddCommMonoid : AddCommMonoid (DiscreteLinHom k A B) :=
  inferInstanceAs (AddCommMonoid (A →ₗ[k] B))

instance instModule : Module k (DiscreteLinHom k A B) :=
  inferInstanceAs (Module k (A →ₗ[k] B))

instance instTopologicalSpace : TopologicalSpace (DiscreteLinHom k A B) := ⊥

instance instDiscreteTopology : DiscreteTopology (DiscreteLinHom k A B) := ⟨rfl⟩

/-- Regard an ordinary linear map as an element of the discrete carrier. -/
def ofLinearMap (f : A →ₗ[k] B) : DiscreteLinHom k A B := f

/-- Forget the selected topology on a discrete linear map. -/
def toLinearMap (f : DiscreteLinHom k A B) : A →ₗ[k] B := f

@[simp] theorem toLinearMap_ofLinearMap (f : A →ₗ[k] B) :
    (ofLinearMap f : DiscreteLinHom k A B).toLinearMap = f := rfl

@[simp] theorem ofLinearMap_toLinearMap (f : DiscreteLinHom k A B) :
    ofLinearMap f.toLinearMap = f := rfl

@[simp] theorem ofLinearMap_apply (f : A →ₗ[k] B) (a : A) :
    (ofLinearMap f : DiscreteLinHom k A B) a = f a := rfl

@[ext] theorem ext {f h : DiscreteLinHom k A B} (heq : ∀ a, f a = h a) : f = h :=
  LinearMap.ext heq

/-- With finitely many module generators, continuity into the discrete linear-map
carrier can be tested by continuous evaluations. This uses Mathlib's finite
spanning set and linear-map extensionality on its span. -/
private theorem continuous_of_eval_on_finite {T : Type*} [TopologicalSpace T]
    [Module.Finite k A] [TopologicalSpace B] [DiscreteTopology B]
    {F : T → DiscreteLinHom k A B}
    (hF : ∀ a : A, Continuous fun t => F t a) : Continuous F := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule k A).FG)
  rw [continuous_discrete_rng]
  intro f
  have hpre : F ⁻¹' {f} = ⋂ a ∈ s, {t | F t a = f a} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · intro h a ha
      rw [h]
    · intro h
      apply ext
      intro a
      have heq : (F t).toLinearMap = f.toLinearMap :=
        LinearMap.ext_on hs (fun b hb => h b hb)
      exact congrArg (fun l : A →ₗ[k] B => l a) heq
  rw [hpre]
  exact isOpen_biInter_finset (fun a _ => (isOpen_discrete {f a}).preimage (hF a))

variable [TopologicalSpace k]

/-- Discrete scalars act continuously on the discrete Hom carrier. -/
instance instContinuousSMulOfDiscrete [DiscreteTopology k] :
    ContinuousSMul k (DiscreteLinHom k A B) :=
  ⟨continuous_of_discreteTopology⟩

/-- Finite generation of the source and continuity of scalar multiplication
on the discrete target suffice for scalar continuity on discrete linear Hom;
the scalar ring itself need not be discrete. -/
theorem continuousSMul_of_finite [Module.Finite k A] [TopologicalSpace B]
    [DiscreteTopology B] [ContinuousSMul k B] :
    ContinuousSMul k (DiscreteLinHom k A B) := by
  constructor
  rw [continuous_prod_of_discrete_right]
  intro f
  apply continuous_of_eval_on_finite
  intro a
  change Continuous (fun r : k => r • f a)
  fun_prop

instance instContinuousSMulOfFinite [Module.Finite k A] [TopologicalSpace B]
    [DiscreteTopology B] [ContinuousSMul k B] :
    ContinuousSMul k (DiscreteLinHom k A B) :=
  continuousSMul_of_finite

end DiscreteLinHom

namespace DiscreteLinHom

variable {k : Type u} [CommRing k] {A : Type v} {B : Type w}
    [AddCommMonoid A] [Module k A] [AddCommGroup B] [Module k B]

instance instAddCommGroup : AddCommGroup (DiscreteLinHom k A B) :=
  inferInstanceAs (AddCommGroup (A →ₗ[k] B))

end DiscreteLinHom

namespace TopRep

variable {k : Type u} [CommRing k] [TopologicalSpace k]
    {G : Type x} [Group G]
    (X : TopRep.{v} k G) (Y : TopRep.{w} k G)

/-- Discrete linear Hom, with Mathlib's inverse-oriented conjugation action.
This bundles operatorwise continuity, not joint continuity in `G`. Scalar
continuity is required independently; it follows, for example, from discrete
scalars or from finite generation of `X` and discrete `Y`. -/
noncomputable def discreteLinHom
    [ContinuousSMul k (DiscreteLinHom k X Y)] :
    TopRep.{max v w} k G :=
  let ρ := Representation.linHom X.ρ.toRepresentation Y.ρ.toRepresentation
  .of <| (show ContRepresentation k G (DiscreteLinHom k X Y) from
    ContRepresentation.ofMonoidHom
    { toFun := fun g =>
        { toLinearMap := ρ g
          cont := continuous_of_discreteTopology }
      map_one' := by
        apply ContinuousLinearMap.coe_injective
        exact ρ.map_one
      map_mul' := by
        intro g h
        apply ContinuousLinearMap.coe_injective
        exact ρ.map_mul g h })

/-- The ordinary linear map underlying an element of the discrete Hom
representation. -/
def discreteLinHomToLinearMap [ContinuousSMul k (DiscreteLinHom k X Y)]
    (f : discreteLinHom X Y) : X →ₗ[k] Y :=
  (show DiscreteLinHom k X Y from f).toLinearMap

/-- An ordinary linear map as an element of the discrete Hom representation. -/
def discreteLinHomOfLinearMap [ContinuousSMul k (DiscreteLinHom k X Y)]
    (f : X →ₗ[k] Y) : discreteLinHom X Y :=
  DiscreteLinHom.ofLinearMap f

@[simp] theorem discreteLinHomToLinearMap_ofLinearMap
    [ContinuousSMul k (DiscreteLinHom k X Y)] (f : X →ₗ[k] Y) :
    discreteLinHomToLinearMap X Y (discreteLinHomOfLinearMap X Y f) = f := rfl

@[simp] theorem discreteLinHomOfLinearMap_toLinearMap
    [ContinuousSMul k (DiscreteLinHom k X Y)] (f : discreteLinHom X Y) :
    discreteLinHomOfLinearMap X Y (discreteLinHomToLinearMap X Y f) = f := rfl

@[ext] theorem discreteLinHom_ext
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    {f h : discreteLinHom X Y}
    (heq : ∀ a, (discreteLinHomToLinearMap X Y f) a =
      (discreteLinHomToLinearMap X Y h) a) : f = h :=
  DiscreteLinHom.ext heq

@[simp] theorem discreteLinHom_ρ_apply
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    (g : G) (f : discreteLinHom X Y) (a : X) :
    (discreteLinHomToLinearMap X Y ((discreteLinHom X Y).ρ g f)) a =
      Y.ρ g ((discreteLinHomToLinearMap X Y f) (X.ρ g⁻¹ a)) := by
  rfl

/-- Forgetting operatorwise continuity recovers Mathlib's conjugation
representation on all linear maps. -/
theorem discreteLinHom_toRepresentation
    [ContinuousSMul k (DiscreteLinHom k X Y)] :
    ((discreteLinHom X Y).ρ.toRepresentation :
      Representation k G (DiscreteLinHom k X Y)) =
        (X.ρ.toRepresentation).linHom Y.ρ.toRepresentation := by
  rfl

private theorem mem_discreteLinHom_linearMap_iff
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    (f : DiscreteLinHom k X Y) :
    f.toLinearMap ∈ ((X.ρ.toRepresentation).linHom Y.ρ.toRepresentation).invariants ↔
      ∀ g : G, ∀ a : X, f (X.ρ g a) = Y.ρ g (f a) := by
  have h := Representation.mem_linHom_invariants_iff_isIntertwining
    (ρ := X.ρ.toRepresentation) (σ := Y.ρ.toRepresentation) f.toLinearMap
  let ρ := (X.ρ.toRepresentation).linHom Y.ρ.toRepresentation
  constructor
  · intro hf g a
    have hmem := (ρ.mem_invariants f.toLinearMap).mp hf
    have hfixed : ∀ g : G,
        (Y.ρ.toRepresentation : Representation k G Y) g ∘ₗ f.toLinearMap ∘ₗ
          (X.ρ.toRepresentation : Representation k G X) g⁻¹ = f.toLinearMap := by
      intro g
      simpa [ρ, Representation.linHom_apply] using hmem g
    exact (h.mp hfixed).isIntertwining g a
  · intro hf
    apply (ρ.mem_invariants f.toLinearMap).mpr
    intro g
    simpa [ρ, Representation.linHom_apply] using (h.mpr ⟨hf⟩) g

/-- A point of discrete Hom is fixed under conjugation precisely when its
underlying linear map intertwines the two input actions. Mathlib's
`Representation.invariantsEquivIntertwiningMap` supplies the bundled
invariants/intertwiners equivalence; no second equivalence is needed. -/
theorem mem_discreteLinHom_invariants_iff
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    (f : discreteLinHom X Y) :
    f ∈ ((discreteLinHom X Y).ρ.toRepresentation).invariants ↔
      ∀ g : G, ∀ a : X,
        (discreteLinHomToLinearMap X Y f) (X.ρ g a) =
          Y.ρ g ((discreteLinHomToLinearMap X Y f) a) := by
  rw [discreteLinHom_toRepresentation X Y]
  exact mem_discreteLinHom_linearMap_iff X Y (show DiscreteLinHom k X Y from f)

/-- A discrete acting group acts jointly continuously on discrete Hom,
irrespective of the topology or generation properties of the inputs. -/
theorem discreteLinHom_jointlyContinuous_of_discreteGroup
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    [TopologicalSpace G] [DiscreteTopology G] :
    JointlyContinuous (discreteLinHom X Y) := by
  have : DiscreteTopology (discreteLinHom X Y) := DiscreteLinHom.instDiscreteTopology
  constructor
  exact continuous_of_discreteTopology

/-- A finite `T₁` acting group is discrete; no finite-generation hypothesis
on the source or joint-continuity hypothesis on the inputs is required.
This extends the finite-group case of Neukirch–Schmidt–Wingberg,
*Cohomology of Number Fields*, corrected second edition, §1.1, from
profinite groups and integer modules to finite `T₁` topologized groups
and `k`-modules. -/
theorem discreteLinHom_jointlyContinuous_of_finiteGroup
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    [TopologicalSpace G] [Finite G] [T1Space G] :
    JointlyContinuous (discreteLinHom X Y) := by
  have : DiscreteTopology G := Finite.instDiscreteTopology
  exact discreteLinHom_jointlyContinuous_of_discreteGroup X Y

/-- With discrete, jointly continuous input actions, finite generation of
the source gives joint continuity of conjugation without discrete scalars or
any separation assumption on the acting group. This extends the
finite-generation case of Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, corrected second edition, §1.1 (with Siyan Daniel Li's correction),
from profinite groups and integer modules to topological groups and
finitely generated `k`-modules. -/
theorem discreteLinHom_jointlyContinuous_of_finiteSource
    [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology X] [DiscreteTopology Y]
    [JointlyContinuous X] [JointlyContinuous Y] [Module.Finite k X] :
    JointlyContinuous (discreteLinHom X Y) := by
  have : DiscreteTopology (discreteLinHom X Y) := DiscreteLinHom.instDiscreteTopology
  constructor
  rw [continuous_prod_of_discrete_right]
  intro f
  apply DiscreteLinHom.continuous_of_eval_on_finite
  intro a
  have hXa : Continuous (fun g : G => X.ρ g⁻¹ a) :=
    (JointlyContinuous.continuous_action (X := X)).comp
      (continuous_inv.prodMk continuous_const)
  have hf : Continuous (fun b : X => (discreteLinHomToLinearMap X Y f) b) :=
    continuous_of_discreteTopology
  have hYa : Continuous (fun g : G =>
      Y.ρ g ((discreteLinHomToLinearMap X Y f) (X.ρ g⁻¹ a))) :=
    (JointlyContinuous.continuous_action (X := Y)).comp
      (continuous_id.prodMk (hf.comp hXa))
  convert hYa using 1
  ext g
  exact discreteLinHom_ρ_apply X Y g f a

/-- For a finite acting group, only finitely many distinct point-stabilizer
subsets occur. Mathlib's finite-intersection openness criterion makes their
common kernel open, without a separation hypothesis. -/
private theorem isOpen_actionKernel
    {Z : TopRep.{z} k G} [TopologicalSpace G] [Finite G]
    [DiscreteTopology Z] [JointlyContinuous Z] :
    IsOpen {g : G | ∀ a : Z, Z.ρ g a = a} := by
  let stabilizer : Z → Set G := fun a => {g | Z.ρ g a = a}
  have hfinite : (Set.range stabilizer).Finite := Set.toFinite _
  have hopen (a : Z) : IsOpen (stabilizer a) := by
    have h : Continuous (fun g : G => Z.ρ g a) :=
      (JointlyContinuous.continuous_action (X := Z)).comp
        (continuous_id.prodMk continuous_const)
    exact (isOpen_discrete {a}).preimage h
  have hOpen : IsOpen (⋂ a, stabilizer a) := by
    rw [← Set.sInter_range]
    exact hfinite.isOpen_sInter (by rintro _ ⟨a, rfl⟩; exact hopen a)
  convert hOpen using 1
  ext g
  simp [stabilizer]

/-- For finite, possibly non-`T₁` groups, joint continuity of the discrete
input actions supplies an open common action kernel. No separation assumption
on `G` or finite-generation assumption on `X` is needed. -/
theorem discreteLinHom_jointlyContinuous_of_finiteGroup_of_jointlyContinuous
    [ContinuousSMul k (DiscreteLinHom k X Y)]
    [TopologicalSpace G] [IsTopologicalGroup G] [Finite G]
    [DiscreteTopology X] [DiscreteTopology Y]
    [JointlyContinuous X] [JointlyContinuous Y] :
    JointlyContinuous (discreteLinHom X Y) := by
  have : DiscreteTopology (discreteLinHom X Y) := DiscreteLinHom.instDiscreteTopology
  let : MulAction G (discreteLinHom X Y) :=
    { smul g f := (discreteLinHom X Y).ρ g f
      one_smul f := by
        change (discreteLinHom X Y).ρ 1 f = f
        rw [map_one]
        rfl
      mul_smul g h f := by
        change (discreteLinHom X Y).ρ (g * h) f =
          (discreteLinHom X Y).ρ g ((discreteLinHom X Y).ρ h f)
        rw [map_mul]
        rfl }
  let K : Subgroup G :=
    { carrier := {g | (∀ a : X, X.ρ g a = a) ∧ ∀ b : Y, Y.ρ g b = b}
      one_mem' := by constructor <;> intro a <;> simp
      mul_mem' := by
        rintro g h ⟨hgX, hgY⟩ ⟨hhX, hhY⟩
        constructor
        · intro a
          calc
            X.ρ (g * h) a = X.ρ g (X.ρ h a) := by rw [map_mul]; rfl
            _ = X.ρ g a := by rw [hhX a]
            _ = a := hgX a
        · intro b
          calc
            Y.ρ (g * h) b = Y.ρ g (Y.ρ h b) := by rw [map_mul]; rfl
            _ = Y.ρ g b := by rw [hhY b]
            _ = b := hgY b
      inv_mem' := by
        rintro g ⟨hgX, hgY⟩
        constructor
        · intro a
          have hcomp : X.ρ g (X.ρ g⁻¹ a) = a := by
            have hmul : X.ρ (g * g⁻¹) a = a := by simp
            rw [map_mul] at hmul
            exact hmul
          exact (hgX _).symm.trans hcomp
        · intro b
          have hcomp : Y.ρ g (Y.ρ g⁻¹ b) = b := by
            have hmul : Y.ρ (g * g⁻¹) b = b := by simp
            rw [map_mul] at hmul
            exact hmul
          exact (hgY _).symm.trans hcomp }
  have hK : IsOpen (K : Set G) := by
    change IsOpen ({g : G | ∀ a : X, X.ρ g a = a} ∩
      {g : G | ∀ b : Y, Y.ρ g b = b})
    exact (isOpen_actionKernel (Z := X)).inter (isOpen_actionKernel (Z := Y))
  have hcontinuous : ContinuousSMul G (discreteLinHom X Y) :=
    continuousSMul_iff_stabilizer_isOpen.mpr (fun f => by
      apply Subgroup.isOpen_mono (H₁ := K) (H₂ := MulAction.stabilizer G f) ?_ hK
      intro g hg
      change (discreteLinHom X Y).ρ g f = f
      apply discreteLinHom_ext X Y
      intro a
      rw [discreteLinHom_ρ_apply]
      rw [(K.inv_mem hg).1 a, hg.2 ((discreteLinHomToLinearMap X Y f) a)])
  let := hcontinuous
  constructor
  exact continuous_smul

end TopRep

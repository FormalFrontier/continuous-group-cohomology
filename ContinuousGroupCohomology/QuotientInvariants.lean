/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents (Hive Task hive-request-982cdb753403f2f54933b957f62e80c721169374)
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Topology.Algebra.Group.Quotient
public import ContinuousGroupCohomology.TopRepUlift

set_option warningAsError true

/-!
# Quotient representations on invariant submodules

For a normal subgroup `N` of `G`, the invariant submodule of a topological representation
under `N` carries the induced action of `G ⧸ N` and its inherited submodule topology.
This gives a functor on continuous representations and a canonical continuous inclusion
after restriction along the quotient homomorphism. Pointwise continuity of operators
does not imply joint continuity of the group action; the latter is established separately
under two explicit sufficient hypotheses.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace TopRep

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] (N : Subgroup G) [N.Normal]

/-- Normality makes the invariant submodule stable under the original group action. -/
lemma quotientInvariants_stable (X : TopRep.{w} k G) (g : G)
    {x : X} (hx : x ∈ (X.ρ.restrict N.subtype).invariants) :
    X.ρ g x ∈ (X.ρ.restrict N.subtype).invariants := by
  intro n
  have h := hx ⟨g⁻¹ * n.1 * g, Subgroup.Normal.conj_mem' ‹N.Normal› n.1 n.2 g⟩
  calc
    X.ρ n (X.ρ g x) = X.ρ (n.1 * g) x := by rw [map_mul]; rfl
    _ = X.ρ (g * (g⁻¹ * n.1 * g)) x := by congr 1; group
    _ = X.ρ g (X.ρ (g⁻¹ * n.1 * g) x) := by rw [map_mul]; rfl
    _ = X.ρ g x := congrArg (fun y => X.ρ g y) h

/-- The pointwise-continuous action of `G` on its `N`-invariants. -/
def quotientInvariantsAction (X : TopRep.{w} k G) :
    G →* ((X.ρ.restrict N.subtype).invariants →L[k]
      (X.ρ.restrict N.subtype).invariants) where
  toFun g := (X.ρ g).restrict (fun _ hx => quotientInvariants_stable N X g hx)
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp [map_mul]

/-- The action on the invariant submodule descends through `G ⧸ N`. -/
def quotientInvariantsActionQuot (X : TopRep.{w} k G) :
    (G ⧸ N) →* ((X.ρ.restrict N.subtype).invariants →L[k]
      (X.ρ.restrict N.subtype).invariants) :=
  QuotientGroup.lift N (quotientInvariantsAction N X) (by
    intro g hg
    change quotientInvariantsAction N X g = 1
    ext x
    exact x.2 ⟨g, hg⟩)

/-- The native quotient representation on the `N`-invariants with their inherited topology.
No topology on `G` or joint continuity in the group variable is needed. -/
def quotientInvariants (X : TopRep.{w} k G) : TopRep.{w} k (G ⧸ N) :=
  .of (.ofMonoidHom (quotientInvariantsActionQuot N X))

/-- Evaluation of the residual quotient action on a representative. -/
@[simp] theorem quotientInvariants_ρ_mk (X : TopRep.{w} k G) (g : G)
    (x : quotientInvariants N X) :
    ((quotientInvariants N X).ρ (QuotientGroup.mk' N g) x).1 = X.ρ g x.1 :=
  rfl

/-- The continuous, equivariant inclusion of quotient invariants into the original
representation, after restricting along `G → G ⧸ N`. -/
def quotientInvariantsIncl (X : TopRep.{w} k G) :
    res (QuotientGroup.mk' N) (quotientInvariants N X) ⟶ X :=
  ofHom {
    toContinuousLinearMap := ((X.ρ.restrict N.subtype).invariants).subtypeL
    isIntertwining' := by
      intro g
      ext x
      exact quotientInvariants_ρ_mk N X g x
  }

/-- Map invariants of equivariant continuous linear maps, preserving the residual quotient
action. -/
def quotientInvariantsMap {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    quotientInvariants N X ⟶ quotientInvariants N Y :=
  ofHom {
    toContinuousLinearMap := (f.hom.restrict N.subtype).mapInvariants
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext x
        change f.hom (X.ρ g x.1) = Y.ρ g (f.hom x.1)
        exact f.hom.isIntertwining g x.1
  }

/-- Functorial quotient invariants for native topological representations. -/
def quotientInvariantsFunctor : TopRep.{w} k G ⥤ TopRep.{w} k (G ⧸ N) where
  obj := quotientInvariants N
  map := quotientInvariantsMap N
  map_id := by
    intro X
    ext x
    apply Subtype.ext
    rfl
  map_comp := by
    intro X Y Z f g
    ext x
    apply Subtype.ext
    rfl

/-- Evaluation of the functor's coefficient map inside the underlying representation. -/
@[simp] theorem quotientInvariantsFunctor_map_val {X Y : TopRep.{w} k G}
    (f : X ⟶ Y) (x : quotientInvariants N X) :
    (((quotientInvariantsFunctor (k := k) N).map f) x).1 = f.hom x.1 :=
  rfl

/-- Naturality of the continuous inclusion, in the variance required by restriction
along the quotient map. -/
theorem quotientInvariantsIncl_naturality {X Y : TopRep.{w} k G} (f : X ⟶ Y) :
    (resFunctor (QuotientGroup.mk' N)).map
      ((quotientInvariantsFunctor (k := k) N).map f) ≫ quotientInvariantsIncl N Y =
        quotientInvariantsIncl N X ≫ f := by
  ext x
  rfl

/-- Joint continuity descends from `G` to `G ⧸ N` through the open quotient map,
for any normal subgroup (not necessarily open or closed). -/
theorem jointlyContinuous_quotientInvariants [TopologicalSpace G]
    [SeparatelyContinuousMul G] (X : TopRep.{w} k G) [JointlyContinuous X] :
    JointlyContinuous (quotientInvariants N X) := by
  constructor
  rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap
    IsOpenQuotientMap.id).continuous_comp_iff]
  have hprod : Continuous (fun p : G × quotientInvariants N X => (p.1, p.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hact : Continuous (fun p : G × quotientInvariants N X => X.ρ p.1 p.2.1) :=
    JointlyContinuous.continuous_action.comp hprod
  have hsub : Continuous (fun p : G × quotientInvariants N X =>
      (⟨X.ρ p.1 p.2.1, quotientInvariants_stable N X p.1 p.2.2⟩ :
        (X.ρ.restrict N.subtype).invariants)) :=
    hact.subtype_mk (fun p => quotientInvariants_stable N X p.1 p.2.2)
  have heq : (fun p : G × quotientInvariants N X =>
      (quotientInvariants N X).ρ (QuotientGroup.mk' N p.1) p.2) =
      (fun p : G × quotientInvariants N X =>
        (⟨X.ρ p.1 p.2.1, quotientInvariants_stable N X p.1 p.2.2⟩ :
          (X.ρ.restrict N.subtype).invariants)) := by
    funext p
    apply Subtype.ext
    exact quotientInvariants_ρ_mk N X p.1 p.2
  change Continuous (fun p : G × quotientInvariants N X =>
    (quotientInvariants N X).ρ (QuotientGroup.mk' N p.1) p.2)
  rw [heq]
  exact hsub

/-- If `N` is open, the *quotient topology* on `G ⧸ N` is discrete, and the pointwise
continuous quotient operators give a jointly continuous action without assuming it for `X`. -/
theorem jointlyContinuous_quotientInvariants_of_isOpen [TopologicalSpace G]
    [SeparatelyContinuousMul G] (X : TopRep.{w} k G) (hN : IsOpen (N : Set G)) :
    JointlyContinuous (quotientInvariants N X) := by
  let _ := QuotientGroup.discreteTopology hN
  constructor
  apply continuous_prod_of_discrete_left.mpr
  intro q
  exact ((quotientInvariants N X).ρ q).continuous

end TopRep

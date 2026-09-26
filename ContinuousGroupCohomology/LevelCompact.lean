/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
Original development: Beacon
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Stabilizer
public import Mathlib.Topology.Algebra.OpenSubgroup

public section

/-!
# Levelwise compact coefficient representations

This file equips the invariants of a representation under every open subgroup
with independently specified compact Hausdorff additive-group topologies.  The
topologies are compatible with transport by the ambient group action: if
`V ≤ σ U σ⁻¹`, then multiplication by `σ` sends `U`-invariants continuously to
`V`-invariants.

The topology is deliberately levelwise.  There is no topology on the ambient
coefficient module and no topology or continuous-scalar hypothesis on the
coefficient ring.  Discreteness or continuity of the ambient action is a
separate condition for downstream applications.
-/

noncomputable section

namespace ContinuousGroupCohomology

universe uR uG uA

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- The submodule of vectors fixed by an open subgroup. -/
abbrev openSubgroupInvariants (A : Rep.{uA} R G) (U : OpenSubgroup G) :=
  Representation.invariants (A.ρ.comp U.toSubgroup.subtype)

/-- Transport open-subgroup invariants by the ambient group action.

The containment has the source-to-target orientation: if
`V ≤ σ U σ⁻¹`, then `a ↦ σ • a` sends `A^U` to `A^V`. -/
@[expose] def openSubgroupInvariantsTransport (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (σ : G)
    (h : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ)) :
    openSubgroupInvariants A U →ₗ[R] openSubgroupInvariants A V where
  toFun x := ⟨A.ρ σ x, fun g ↦ by
    change A.ρ (g : G) (A.ρ σ x) = A.ρ σ x
    rw [← Representation.mem_stabilizer, A.ρ.stabilizer_conj σ x]
    exact (Subgroup.map_mono (fun u hu ↦ x.2 ⟨u, hu⟩)) (h g.2)⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

@[simp]
lemma openSubgroupInvariantsTransport_coe (A : Rep.{uA} R G)
    (U V : OpenSubgroup G) (σ : G)
    (h : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (x : openSubgroupInvariants A U) :
    (openSubgroupInvariantsTransport A U V σ h x : A) = A.ρ σ x :=
  rfl

/-- The containment needed to compose two open-subgroup invariant transports. -/
lemma openSubgroupInvariantsTransport_comp_le (U V W : OpenSubgroup G)
    (σ τ : G) (hUV : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (hVW : W.toSubgroup ≤ V.toSubgroup.map (MulAut.conj τ)) :
    W.toSubgroup ≤ U.toSubgroup.map (MulAut.conj (τ * σ)) := by
  intro w hw
  rcases hVW hw with ⟨v, hv, rfl⟩
  rcases hUV hv with ⟨u, hu, rfl⟩
  exact ⟨u, hu, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- Transport through two subgroup containments composes by multiplying the
transporting elements in target-to-source order. -/
lemma openSubgroupInvariantsTransport_comp (A : Rep.{uA} R G)
    (U V W : OpenSubgroup G) (σ τ : G)
    (hUV : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ))
    (hVW : W.toSubgroup ≤ V.toSubgroup.map (MulAut.conj τ)) :
    (openSubgroupInvariantsTransport A V W τ hVW).comp
        (openSubgroupInvariantsTransport A U V σ hUV) =
      openSubgroupInvariantsTransport A U W (τ * σ)
        (openSubgroupInvariantsTransport_comp_le U V W σ τ hUV hVW) := by
  ext x
  simp [← Module.End.mul_apply, ← map_mul]

/-- Compact Hausdorff additive-group topologies on the invariants under every
open subgroup, compatible with transport by the ambient group action.

This is additional levelwise topology data.  It does not impose a topology on
the ambient coefficient module or on the coefficient ring. -/
structure LevelCompact (A : Rep.{uA} R G) where
  topology : ∀ U : OpenSubgroup G, TopologicalSpace (openSubgroupInvariants A U)
  compact : ∀ U, @CompactSpace (openSubgroupInvariants A U) (topology U)
  t2 : ∀ U, @T2Space (openSubgroupInvariants A U) (topology U)
  topologicalAddGroup :
    ∀ U, @IsTopologicalAddGroup (openSubgroupInvariants A U) (topology U) _
  continuous_transport : ∀ (U V : OpenSubgroup G) (σ : G)
    (h : V.toSubgroup ≤ U.toSubgroup.map (MulAut.conj σ)),
    @Continuous (openSubgroupInvariants A U) (openSubgroupInvariants A V)
      (topology U) (topology V) (openSubgroupInvariantsTransport A U V σ h)

namespace LevelCompact

/-- Inclusion of invariant submodules for an inclusion of open subgroups. -/
def inclusion (A : Rep.{uA} R G) (U V : OpenSubgroup G) (h : V ≤ U) :
    openSubgroupInvariants A U →ₗ[R] openSubgroupInvariants A V :=
  openSubgroupInvariantsTransport A U V 1 (by
    intro g hg
    exact ⟨g, h hg, by simp⟩)

@[simp]
lemma inclusion_coe (A : Rep.{uA} R G) (U V : OpenSubgroup G) (h : V ≤ U)
    (x : openSubgroupInvariants A U) : (inclusion A U V h x : A) = x := by
  change A.ρ 1 x = x
  simp

@[simp]
lemma inclusion_self (A : Rep.{uA} R G) (U : OpenSubgroup G) :
    inclusion A U U le_rfl = LinearMap.id := by
  ext x
  simp

lemma inclusion_injective (A : Rep.{uA} R G) (U V : OpenSubgroup G) (h : V ≤ U) :
    Function.Injective (inclusion A U V h) := by
  intro x y hxy
  apply Subtype.ext
  simpa only [inclusion_coe] using
    congr_arg (fun z : openSubgroupInvariants A V ↦ (z : A)) hxy

/-- The inclusion `A^U → A^V` is continuous whenever `V ≤ U`. -/
lemma continuous_inclusion (A : Rep.{uA} R G) (L : LevelCompact A)
    (U V : OpenSubgroup G) (h : V ≤ U) :
    @Continuous (openSubgroupInvariants A U) (openSubgroupInvariants A V)
      (L.topology U) (L.topology V) (inclusion A U V h) :=
  L.continuous_transport U V 1 (by
    intro g hg
    exact ⟨g, h hg, by simp⟩)

/-- The natural inclusion between two levels is a closed embedding.  In
particular, the topology on `A^U` is the topology induced from `A^V`. -/
lemma inclusion_isClosedEmbedding (A : Rep.{uA} R G) (L : LevelCompact A)
    (U V : OpenSubgroup G) (h : V ≤ U) :
    @Topology.IsClosedEmbedding
      (openSubgroupInvariants A U) (openSubgroupInvariants A V)
      (L.topology U) (L.topology V) (inclusion A U V h) :=
  @Continuous.isClosedEmbedding
    (openSubgroupInvariants A U) (openSubgroupInvariants A V)
    (L.topology U) (L.topology V) (L.compact U) (L.t2 V)
    (inclusion A U V h) (continuous_inclusion A L U V h)
    (inclusion_injective A U V h)

end LevelCompact

end ContinuousGroupCohomology

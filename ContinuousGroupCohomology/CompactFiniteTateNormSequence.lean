/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactExceptionalTateDiagrams

/-!
# Compact finite Tate norm sequence

The actual compact finite coinvariants under open-normal deflation form a
diagram. Together with the constant diagram of compact total invariants and
the published finite Tate kernel and quotient diagrams, they give a natural
finite norm row. At every stage the two middle pairs are exact, the kernel
inclusion is injective, and the quotient projection is surjective.

The coefficient ring has no topology. These are compact Hausdorff *additive*
groups for a chosen `LevelCompact`, not topological modules. No claim about
exactness after taking an inverse limit is made here.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- Compact finite coinvariants with the residual-norm deflation for `S ≤ T`. -/
@[expose] noncomputable def compactFiniteCoinvariantsDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj S := finiteCoinvariants A (L := L) S
  map {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteCoinvariantDeflation A L S T (leOfHom f)
  map_id S := by
    let _ : Fintype (S.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact finiteCoinvariantDeflation_refl A L S
  map_comp {S T U} f g := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' T.toSubgroup)) :=
      Fintype.ofFinite _
    let _ : Fintype (U.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    exact (finiteCoinvariantDeflation_comp A L S T U (leOfHom f) (leOfHom g)).symm

/-- Total invariants carry the identity transition at every deflation level. -/
@[expose] noncomputable def compactTotalInvariantsDiagram :
    OpenNormalSubgroup G ⥤ CompHausAddCommGrp.{u} where
  obj _ := group A L (⊤ : OpenSubgroup G)
  map _ := 𝟙 _

/-- Inclusion of the actual compact finite Tate kernel into coinvariants. -/
@[expose] noncomputable def compactFiniteTateNegOneInclusion :
    compactFiniteNegativeOneDeflationDiagram A L ⟶
      compactFiniteCoinvariantsDiagram A L where
  app S := finiteTateNegOneι A L S
  naturality {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact (finiteTateNegOneι_finiteTateNegOneDeflation_apply
      A L S T (leOfHom f) x)

/-- The actual finite norm to the *same* compact total-invariants group. -/
@[expose] noncomputable def compactFiniteTateNorm :
    compactFiniteCoinvariantsDiagram A L ⟶
      compactTotalInvariantsDiagram A L where
  app S := normFromFiniteCoinvariants A L S
  naturality {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact normFromFiniteCoinvariants_finiteCoinvariantDeflation
      A L S T (leOfHom f) x

/-- Projection to the quotient by the actual closed range of the finite norm. -/
@[expose] noncomputable def compactFiniteTateZeroProjection :
    compactTotalInvariantsDiagram A L ⟶
      compactFiniteZeroDeflationDiagram A L where
  app S := finiteTateZeroπ A L S
  naturality {S T} f := by
    let _ : Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup)) :=
      Fintype.ofFinite _
    apply CompHausAddCommGrp.hom_ext
    ext x
    exact (finiteTateZeroDeflation_finiteTateZeroπ_apply
      A L S T (leOfHom f) x).symm

/-- The compact coinvariant diagram has the actual finite coinvariants at `S`. -/
@[simp] lemma compactFiniteCoinvariantsDiagram_obj (S : OpenNormalSubgroup G) :
    (compactFiniteCoinvariantsDiagram A L).obj S = finiteCoinvariants A (L := L) S :=
  rfl

/-- The compact invariant diagram is constant at the total-invariants group. -/
@[simp] lemma compactTotalInvariantsDiagram_obj (S : OpenNormalSubgroup G) :
    (compactTotalInvariantsDiagram A L).obj S = group A L (⊤ : OpenSubgroup G) :=
  rfl

/-- The kernel natural transformation has the actual kernel inclusion at `S`. -/
@[simp] lemma compactFiniteTateNegOneInclusion_app (S : OpenNormalSubgroup G) :
    (compactFiniteTateNegOneInclusion A L).app S = finiteTateNegOneι A L S :=
  rfl

/-- The norm natural transformation has the actual finite norm at `S`. -/
@[simp] lemma compactFiniteTateNorm_app (S : OpenNormalSubgroup G) :
    (compactFiniteTateNorm A L).app S = normFromFiniteCoinvariants A L S :=
  rfl

/-- The quotient natural transformation has the actual quotient map at `S`. -/
@[simp] lemma compactFiniteTateZeroProjection_app (S : OpenNormalSubgroup G) :
    (compactFiniteTateZeroProjection A L).app S = finiteTateZeroπ A L S :=
  rfl

/-- The kernel inclusion and the norm are exact at every finite level. -/
theorem finiteTateNorm_exact_left (S : OpenNormalSubgroup G) :
    Function.Exact (finiteTateNegOneι A L S)
      (normFromFiniteCoinvariants A L S) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · intro hx
    obtain ⟨k, rfl⟩ := hx
    exact normFromFiniteCoinvariants_finiteTateNegOneι_apply A L S k

/-- The norm and quotient projection are exact at every finite level. -/
theorem finiteTateNorm_exact_right (S : OpenNormalSubgroup G) :
    Function.Exact (normFromFiniteCoinvariants A L S)
      (finiteTateZeroπ A L S) := by
  intro y
  constructor
  · intro hy
    change QuotientAddGroup.mk' (normFromFiniteCoinvariants A L S).hom.range y = 0 at hy
    rw [← AddMonoidHom.mem_ker, QuotientAddGroup.ker_mk'] at hy
    exact hy
  · intro hy
    obtain ⟨x, rfl⟩ := hy
    exact finiteTateZeroπ_normFromFiniteCoinvariants_apply A L S x

/-- The finite Tate kernel is an actual subtype of compact coinvariants. -/
theorem finiteTateNegOneι_injective (S : OpenNormalSubgroup G) :
    Function.Injective (finiteTateNegOneι A L S) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The finite Tate quotient is an actual quotient of compact invariants. -/
theorem finiteTateZeroπ_surjective (S : OpenNormalSubgroup G) :
    Function.Surjective (finiteTateZeroπ A L S) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨y, rfl⟩

/-- Degree-zero deflation is onto, without any surjectivity assumption on
coinvariant or degree-`-1` deflation. -/
theorem finiteTateZeroDeflation_surjective
    (S T : OpenNormalSubgroup G) (hST : S ≤ T)
    [Fintype (T.toSubgroup.map (QuotientGroup.mk' S.toSubgroup))] :
    Function.Surjective (finiteTateZeroDeflation A L S T hST) := by
  intro x
  obtain ⟨y, rfl⟩ := finiteTateZeroπ_surjective A L T x
  exact ⟨finiteTateZeroπ A L S y,
    finiteTateZeroDeflation_finiteTateZeroπ_apply A L S T hST y⟩

end ContinuousGroupCohomology.LevelCompact

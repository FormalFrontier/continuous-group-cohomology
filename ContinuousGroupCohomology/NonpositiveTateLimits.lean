/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteTateDiagrams
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Topological limits of finite Tate deflation diagrams

This file equips the finite-level Tate deflation diagrams with
mathlib's canonical module topology and forms their limits in
`TopModuleCat`.  The topology on each limit is therefore the one induced by
its canonical projections to the finite-level stages.

The three constructions correspond to the homological model for Tate degrees
below `-1`, the exceptional degree `-1`, and degree `0`.  This file only
packages those diagrams and their limit projections.  In particular, it does
not assert discreteness of the stages, exactness, cup-product compatibility,
or an identification with a separately defined continuous Tate cohomology.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R]
variable {G : ProfiniteGrp.{u}}

/-- The finite negative-deflation diagram, with every stage equipped with its
canonical module topology.  For positive `n`, its stages model Tate degree
`-n-1`. -/
@[expose] noncomputable def topologicalFiniteNegativeDeflationDiagram
    (A : Rep.{u} R G) (n : ℕ) : OpenNormalSubgroup G ⥤ TopModuleCat.{u} R :=
  finiteNegativeDeflationDiagram A n ⋙ TopModuleCat.withModuleTopology.{u, u} R

/-- The finite degree-`-1` deflation diagram, with every stage equipped with
its canonical module topology. -/
@[expose] noncomputable def topologicalFiniteNegativeOneDeflationDiagram
    (A : Rep.{u} R G) : OpenNormalSubgroup G ⥤ TopModuleCat.{u} R :=
  finiteNegativeOneDeflationDiagram A ⋙ TopModuleCat.withModuleTopology.{u, u} R

/-- The finite degree-zero deflation diagram, with every stage equipped with
its canonical module topology. -/
@[expose] noncomputable def topologicalFiniteZeroDeflationDiagram
    (A : Rep.{u} R G) : OpenNormalSubgroup G ⥤ TopModuleCat.{u} R :=
  finiteZeroDeflationDiagram A ⋙ TopModuleCat.withModuleTopology.{u, u} R

/-- The topological limit of the finite negative-deflation diagram in
homological degree `n`.  For positive `n`, this models Tate degree `-n-1`. -/
noncomputable abbrev negativeDeflationLimit (A : Rep.{u} R G) (n : ℕ) :
    TopModuleCat.{u} R :=
  limit (topologicalFiniteNegativeDeflationDiagram A n)

/-- The canonical projection from the negative-deflation limit to the stage
indexed by `S`. -/
@[expose] noncomputable def negativeDeflationLimitProjection (A : Rep.{u} R G) (n : ℕ)
    (S : OpenNormalSubgroup G) :
    negativeDeflationLimit A n ⟶
      (topologicalFiniteNegativeDeflationDiagram A n).obj S :=
  limit.π (topologicalFiniteNegativeDeflationDiagram A n) S

/-- The projections from the negative-deflation limit commute with every
finite-level deflation map. -/
@[reassoc]
theorem negativeDeflationLimitProjection_naturality (A : Rep.{u} R G) (n : ℕ)
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    negativeDeflationLimitProjection A n S ≫
        (topologicalFiniteNegativeDeflationDiagram A n).map f =
      negativeDeflationLimitProjection A n T :=
  limit.w (topologicalFiniteNegativeDeflationDiagram A n) f

/-- The topological limit of the finite degree-`-1` deflation diagram. -/
noncomputable abbrev negativeOneDeflationLimit (A : Rep.{u} R G) :
    TopModuleCat.{u} R :=
  limit (topologicalFiniteNegativeOneDeflationDiagram A)

/-- The canonical projection from the degree-`-1` deflation limit to the stage
indexed by `S`. -/
@[expose] noncomputable def negativeOneDeflationLimitProjection (A : Rep.{u} R G)
    (S : OpenNormalSubgroup G) :
    negativeOneDeflationLimit A ⟶
      (topologicalFiniteNegativeOneDeflationDiagram A).obj S :=
  limit.π (topologicalFiniteNegativeOneDeflationDiagram A) S

/-- The projections from the degree-`-1` deflation limit commute with every
finite-level deflation map. -/
@[reassoc]
theorem negativeOneDeflationLimitProjection_naturality (A : Rep.{u} R G)
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    negativeOneDeflationLimitProjection A S ≫
        (topologicalFiniteNegativeOneDeflationDiagram A).map f =
      negativeOneDeflationLimitProjection A T :=
  limit.w (topologicalFiniteNegativeOneDeflationDiagram A) f

/-- The topological limit of the finite degree-zero deflation diagram. -/
noncomputable abbrev zeroDeflationLimit (A : Rep.{u} R G) : TopModuleCat.{u} R :=
  limit (topologicalFiniteZeroDeflationDiagram A)

/-- The canonical projection from the degree-zero deflation limit to the stage
indexed by `S`. -/
@[expose] noncomputable def zeroDeflationLimitProjection (A : Rep.{u} R G)
    (S : OpenNormalSubgroup G) :
    zeroDeflationLimit A ⟶ (topologicalFiniteZeroDeflationDiagram A).obj S :=
  limit.π (topologicalFiniteZeroDeflationDiagram A) S

/-- The projections from the degree-zero deflation limit commute with every
finite-level deflation map. -/
@[reassoc]
theorem zeroDeflationLimitProjection_naturality (A : Rep.{u} R G)
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    zeroDeflationLimitProjection A S ≫
        (topologicalFiniteZeroDeflationDiagram A).map f =
      zeroDeflationLimitProjection A T :=
  limit.w (topologicalFiniteZeroDeflationDiagram A) f

end ContinuousGroupCohomology

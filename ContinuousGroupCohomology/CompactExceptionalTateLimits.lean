/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Original development: Beacon
Native adaptation: hive-request-64988ad41c768fe5c8bfc3f699d6db6c8fb4b650
  (c322a0ba-d728-4f4a-9ec6-678e3ca42caf)
-/
module

public import ContinuousGroupCohomology.CompactAddCommGroupLimits
public import ContinuousGroupCohomology.CompactExceptionalTateDiagrams

/-!
# Compact exceptional Tate limits

The degree-`-1` and degree-zero compact finite Tate deflation diagrams have
compact Hausdorff additive inverse limits. Canonical projections commute with
deflation, and their images equal the eventual ranges of finite deflations;
the eventual ranges need not be whole stages. No topological module structure,
inverse-limit exactness, or higher/lower Tate degrees are asserted.

Adapted from Beacon's compact Tate limits in the continuous-group-cohomology
source research at commit `9fbcd52d0fe4ce982ac506976542523d91dd84c4`.
-/

public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ContinuousGroupCohomology.LevelCompact

universe u

variable {R : Type u} [CommRing R] {G : ProfiniteGrp.{u}}
variable (A : Rep.{u} R G) (L : LevelCompact A)

/-- The compact Hausdorff degree-`-1` Tate inverse limit. -/
abbrev compactNegativeOneTateLimit : CompHausAddCommGrp.{u} :=
  limit (compactFiniteNegativeOneDeflationDiagram A L)

/-- Canonical projection to a degree-`-1` finite Tate stage. -/
def compactNegativeOneTateLimitπ (S : OpenNormalSubgroup G) :
    compactNegativeOneTateLimit A L ⟶ finiteTateNegOne A L S :=
  limit.π (compactFiniteNegativeOneDeflationDiagram A L) S

/-- Public identification of the named degree-`-1` projection with the
categorical projection, without exposing the definition across modules. -/
lemma compactNegativeOneTateLimitπ_eq_limit_π (S : OpenNormalSubgroup G) :
    compactNegativeOneTateLimitπ A L S =
      limit.π (compactFiniteNegativeOneDeflationDiagram A L) S :=
  by rfl

/-- The degree-`-1` projections commute with deflation. -/
lemma compactNegativeOneTateLimitπ_naturality
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    compactNegativeOneTateLimitπ A L S ≫
        (compactFiniteNegativeOneDeflationDiagram A L).map f =
      compactNegativeOneTateLimitπ A L T :=
  limit.w (compactFiniteNegativeOneDeflationDiagram A L) f

/-- The degree-`-1` projection image equals the eventual range at that stage. -/
lemma compactNegativeOneTateLimitπ_range_eq_eventualRange
    (S : OpenNormalSubgroup G) :
    Set.range (compactNegativeOneTateLimitπ A L S) =
      ((compactFiniteNegativeOneDeflationDiagram A L) ⋙
        forget CompHausAddCommGrp.{u}).eventualRange S :=
  CompHausAddCommGrp.limit_π_range_eq_eventualRange.{u, u}
    (compactFiniteNegativeOneDeflationDiagram A L) S

/-- The compact Hausdorff degree-zero Tate inverse limit. -/
abbrev compactZeroTateLimit : CompHausAddCommGrp.{u} :=
  limit (compactFiniteZeroDeflationDiagram A L)

/-- Canonical projection to a degree-zero finite Tate stage. -/
def compactZeroTateLimitπ (S : OpenNormalSubgroup G) :
    compactZeroTateLimit A L ⟶ finiteTateZero A L S :=
  limit.π (compactFiniteZeroDeflationDiagram A L) S

/-- Public identification of the named degree-zero projection with the
categorical projection, without exposing the definition across modules. -/
lemma compactZeroTateLimitπ_eq_limit_π (S : OpenNormalSubgroup G) :
    compactZeroTateLimitπ A L S =
      limit.π (compactFiniteZeroDeflationDiagram A L) S :=
  by rfl

/-- The degree-zero projections commute with deflation. -/
lemma compactZeroTateLimitπ_naturality
    {S T : OpenNormalSubgroup G} (f : S ⟶ T) :
    compactZeroTateLimitπ A L S ≫
        (compactFiniteZeroDeflationDiagram A L).map f =
      compactZeroTateLimitπ A L T :=
  limit.w (compactFiniteZeroDeflationDiagram A L) f

/-- The degree-zero projection image equals the eventual range at that stage. -/
lemma compactZeroTateLimitπ_range_eq_eventualRange
    (S : OpenNormalSubgroup G) :
    Set.range (compactZeroTateLimitπ A L S) =
      ((compactFiniteZeroDeflationDiagram A L) ⋙
        forget CompHausAddCommGrp.{u}).eventualRange S :=
  CompHausAddCommGrp.limit_π_range_eq_eventualRange.{u, u}
    (compactFiniteZeroDeflationDiagram A L) S

end ContinuousGroupCohomology.LevelCompact

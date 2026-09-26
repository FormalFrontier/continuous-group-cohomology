/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ClosedTopologicalCoinvariants
public import ContinuousGroupCohomology.CompactAddCommGroup
public import ContinuousGroupCohomology.CompactAddCommGroupLimits
public import ContinuousGroupCohomology.CompactBarFunctoriality
public import ContinuousGroupCohomology.CompactFiniteHomology
public import ContinuousGroupCohomology.CompactNegativeTate
public import ContinuousGroupCohomology.CompactTopModuleLimits
public import ContinuousGroupCohomology.Composition
public import ContinuousGroupCohomology.ContinuousCohomologyUlift
public import ContinuousGroupCohomology.ContinuousGroupExtension
public import ContinuousGroupCohomology.Corestriction
public import ContinuousGroupCohomology.DegreeOne
public import ContinuousGroupCohomology.ExceptionalDeflation
public import ContinuousGroupCohomology.FiniteCoinvariants
public import ContinuousGroupCohomology.FiniteDeflationTransitivity
public import ContinuousGroupCohomology.FiniteNegativeDeflation
public import ContinuousGroupCohomology.GroupExtensionUlift
public import ContinuousGroupCohomology.HomogeneousCochainsUlift
public import ContinuousGroupCohomology.LevelCompact
public import ContinuousGroupCohomology.LevelCompactFunctoriality
public import ContinuousGroupCohomology.LevelCompactNorm
public import ContinuousGroupCohomology.LowDegreeExact
public import ContinuousGroupCohomology.Mackey
public import ContinuousGroupCohomology.NestedInvariants
public import ContinuousGroupCohomology.NormalizedCohomology
public import ContinuousGroupCohomology.QuotientConjugationAction
public import ContinuousGroupCohomology.RestrictedLevelCompact
public import ContinuousGroupCohomology.TopModuleCatUlift
public import ContinuousGroupCohomology.TopRepUlift
public import ContinuousGroupCohomology.TopologicalModN
public import ContinuousGroupCohomology.TopologicalQuotientConjugationAction
public import ContinuousGroupCohomology.Torsion

/-!
# Continuous group cohomology: native core

The public root reexports the low-degree continuous cohomology and transfer
interface, compact-group degree-one torsion, topological quotients and actions,
finite coinvariants, exceptional deflation and its transitivity, compact
finite-bar homology, and compact or restricted finite-stage constructions.
All shipped production modules are native Lean modules and reachable through
this root.

Finite-group statements require the indicated finite-group hypotheses; compact
limit statements concern compact Hausdorff additive groups and level systems,
not a general completed continuous homology construction. The finite-bar
homology comparison is additive, beginning in positive homology degree one
and finite Tate degree negative two; functoriality requires equivariance and
continuity of the coefficient map.
-/

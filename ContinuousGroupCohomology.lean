/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ClosedTopologicalCoinvariants
public import ContinuousGroupCohomology.CompactAddCommGroup
public import ContinuousGroupCohomology.CompactAddCommGroupLimits
public import ContinuousGroupCohomology.CompactExceptionalTateCoefficientMaps
public import ContinuousGroupCohomology.CompactExceptionalTateDiagrams
public import ContinuousGroupCohomology.CompactExceptionalTateLimitFunctoriality
public import ContinuousGroupCohomology.CompactExceptionalTateLimits
public import ContinuousGroupCohomology.CompactFiniteTateNormSequence
public import ContinuousGroupCohomology.CompactTateNormLimitSequence
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
public import ContinuousGroupCohomology.ExceptionalTateDeflationTopology
public import ContinuousGroupCohomology.FiniteCoinvariantDeflation
public import ContinuousGroupCohomology.FiniteCoinvariants
public import ContinuousGroupCohomology.FiniteDeflationTransitivity
public import ContinuousGroupCohomology.FiniteNegativeDeflation
public import ContinuousGroupCohomology.FiniteTateDiagrams
public import ContinuousGroupCohomology.FiniteTateTopology
public import ContinuousGroupCohomology.GroupExtensionUlift
public import ContinuousGroupCohomology.HomogeneousCochainsUlift
public import ContinuousGroupCohomology.LevelCompact
public import ContinuousGroupCohomology.LevelCompactFunctoriality
public import ContinuousGroupCohomology.LevelCompactNorm
public import ContinuousGroupCohomology.LowDegreeExact
public import ContinuousGroupCohomology.Mackey
public import ContinuousGroupCohomology.NestedInvariants
public import ContinuousGroupCohomology.NormalizedCohomology
public import ContinuousGroupCohomology.NonpositiveTateFunctoriality
public import ContinuousGroupCohomology.NonpositiveTateLimits
public import ContinuousGroupCohomology.QuotientConjugationAction
public import ContinuousGroupCohomology.RestrictedLevelCompact
public import ContinuousGroupCohomology.RestrictedLevelCompactFunctoriality
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
finite-bar homology, compact exceptional Tate kernels/quotients and continuous
finite-level deflation and their compact diagrams, additive comparisons and
compact Hausdorff additive limits, finite Tate deflation diagrams and their
topological limits, continuous coefficient maps on compact exceptional Tate
stages and limits, and functoriality of selected compact norm systems.
The compact finite Tate norm row and its full-open-normal inverse-limit sequence
identify the actual universal-norm kernel and compact quotient in the chosen
compact Hausdorff additive topologies.
All shipped production modules are native Lean modules and reachable through
this root.

Finite-group statements require the indicated finite-group hypotheses; compact
limit statements concern compact Hausdorff additive groups and level systems,
not a general completed continuous homology construction. The finite-bar
homology comparison is additive, beginning in positive homology degree one
and finite Tate degree negative two; functoriality requires equivariance and
continuity of the coefficient map. Compact exceptional Tate degrees `-1` and
`0` compare additively with algebraic Tate cohomology, without giving the
algebraic Tate groups a topology or assuming a topology on the coefficient ring.
Restricted norm functoriality uses the actual selected level topologies and
requires preservation of arbitrary chosen restricted systems; full and universal-
norm systems admit canonical functors without additional preservation assumptions.
-/

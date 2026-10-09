/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.QuotientInvariants
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ClusterPt
import examples.FiniteStageResolutionNative

/-!
# Quotient-invariants client entrypoint

The generic action, coefficient functor, continuity and boundary-case proofs
reside in `examples.FiniteStageResolutionNative`. This entrypoint publicly
imports `ContinuousGroupCohomology.QuotientInvariants` and imports the Mathlib
modules for its real-coefficient examples and the client module. Import the
production module for the quotient representation on the invariant submodule.
Joint continuity holds with the specified joint-action or open-subgroup
hypotheses; pointwise operator continuity alone does not imply it.
-/

set_option warningAsError true

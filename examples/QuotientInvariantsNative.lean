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
elaborate in `examples.FiniteStageResolutionNative`. This module retains its
original producer and Mathlib imports, including their visibility; import
`ContinuousGroupCohomology.QuotientInvariants` for the production API.
The seven current client proof environments, comprising ten original proof
environments, elaborate together in that host. Importing this forwarding root
does not repeat the original isolated proof elaboration.
-/

set_option warningAsError true

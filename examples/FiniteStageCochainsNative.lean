/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.FiniteStageCochains
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units
import examples.FiniteStageResolutionNative

/-!
# Finite-stage cochain client entrypoint

The degree-zero and degree-two cochain lifts, differential-zero descent and
nonzero sign-orbit cochain proof elaborate in `examples.FiniteStageResolutionNative`.
This module retains its public producer and Mathlib imports; import
`ContinuousGroupCohomology.FiniteStageCochains` for the production API. Seven
current client proof environments, comprising ten original environments, now
elaborate together in the host. Importing this forwarding root does not repeat
the original isolated proof elaboration.
-/

set_option warningAsError true

@[expose] public section

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
nonzero sign-orbit cochain client reside in `examples.FiniteStageResolutionNative`.
This entrypoint publicly imports `ContinuousGroupCohomology.FiniteStageCochains`
and the Mathlib modules for its sign action, and imports the client module.
Import the production module for finite-stage lifts of homogeneous cochains
and closed cochains. The sign-orbit cochain does not assert closedness.
-/

set_option warningAsError true

@[expose] public section

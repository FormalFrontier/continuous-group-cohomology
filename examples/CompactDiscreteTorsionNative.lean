/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.CompactDiscreteTorsion
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Int.Order.Units
import examples.ContinuousTorsionNative

set_option autoImplicit false
set_option warningAsError true

/-!
# Compact discrete torsion client entrypoint

The compact finite-quotient and positive-degree torsion clients reside in
`examples.ContinuousTorsionNative`, alongside degree-one torsion and
arbitrary-degree discreteness clients. This entrypoint publicly imports
`ContinuousGroupCohomology.CompactDiscreteTorsion` and the Mathlib modules
used by its sign examples; it imports `examples.ContinuousTorsionNative` for
the clients. Import the production module directly to use classwise finite
quotient descent and positive-degree torsion.
-/

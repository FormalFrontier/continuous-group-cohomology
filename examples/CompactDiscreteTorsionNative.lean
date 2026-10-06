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
arbitrary-degree discreteness clients. This entrypoint retains its original
public producer and Mathlib imports and imports the host ordinarily, without
re-exporting it. None of the three former client proof-import environments,
including the original Torsion-only host, is checked in isolation.
-/

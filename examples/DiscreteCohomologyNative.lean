/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.DiscreteCohomology
import examples.ContinuousTorsionNative

set_option autoImplicit false
set_option warningAsError true

/-!
# Discrete continuous cohomology client entrypoint

The arbitrary-degree and arbitrary-coefficient discreteness clients reside in
`examples.ContinuousTorsionNative`, alongside degree-one torsion and compact
finite-quotient clients. This entrypoint retains its original public producer
import and imports the host ordinarily, without re-exporting it. None of the
three former client proof-import environments, including the original
Torsion-only host, is checked in isolation.
-/

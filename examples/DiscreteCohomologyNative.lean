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
finite-quotient clients. This entrypoint publicly imports the production
`ContinuousGroupCohomology.DiscreteCohomology` module and imports the client
module ordinarily. Import the production module directly for discreteness
of native continuous cohomology in every degree, including degree zero.
-/

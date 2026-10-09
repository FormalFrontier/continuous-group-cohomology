/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.OpenNormalDiagram
import examples.FiniteStageResolutionNative

/-!
# Open-normal diagram client entrypoint

The arbitrary-degree diagram and filtered-index clients reside in
`examples.FiniteStageResolutionNative`. This entrypoint publicly imports
`ContinuousGroupCohomology.OpenNormalDiagram` and imports that client module.
Import the production module for the open-normal diagram and its inflation
cocone. The index is filtered by intersections; no colimit property is
asserted by the diagram alone.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

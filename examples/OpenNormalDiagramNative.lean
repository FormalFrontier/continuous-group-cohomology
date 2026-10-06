/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.OpenNormalDiagram
import examples.FiniteStageResolutionNative

/-!
# Open-normal diagram client entrypoint

The arbitrary-degree diagram and filtered-index proofs elaborate in
`examples.FiniteStageResolutionNative`. This module retains its public producer
import; import `ContinuousGroupCohomology.OpenNormalDiagram` for the production
API. Seven current client proof environments, comprising ten original ones,
elaborate together in the host. Importing this forwarding root does not repeat
the original isolated proof elaboration.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

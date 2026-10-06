/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.SeededCochains
import examples.FiniteStageResolutionNative

/-!
# Ordinary-import client for seeded cochain descent

The cochain, its degree and the prescribed open normal subgroup are all arbitrary.
The descent proof elaborates in `examples.FiniteStageResolutionNative`; this root
retains its public producer import. Seven current client proof environments,
comprising ten original ones, elaborate together in the host. Importing this
forwarding root does not repeat the original isolated proof elaboration. Import
`ContinuousGroupCohomology.SeededCochains` for the production API.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

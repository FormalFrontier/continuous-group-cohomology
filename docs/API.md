# Native API reference (historical analyzed snapshot)

**Historical snapshot only:** this index analyzes the earlier
27-leaf/eight-client graph and historical Tate dependency specified in
[reproduction](README.md#frozen-inputs), **not** the current
47-leaf/twenty-four-client build (72 local modules including the root). It excludes `CompactNegativeTate`,
`CompactBarFunctoriality`, `ExceptionalDeflation`,
`FiniteDeflationTransitivity`, `Torsion`, `FiniteTateDiagrams`,
`NonpositiveTateLimits`, `NonpositiveTateFunctoriality`,
`FiniteTateTopology`, `FiniteCoinvariantDeflation`,
`ExceptionalTateDeflationTopology`, `CompactExceptionalTateDiagrams`,
`CompactExceptionalTateLimits`, `CompactExceptionalTateCoefficientMaps`,
`CompactExceptionalTateLimitFunctoriality`, `RestrictedLevelCompactFunctoriality`,
`CompactFiniteTateNormSequence`, `CompactTateNormLimitSequence`,
`CompactTateNormNaturality`, `CompactUniversalNormLimits` and their sixteen direct clients; its root
import row is historical. See the [manual compact-bar guide](CompactBar.md),
[finite-deflation guide](FiniteDeflation.md),
[compact exceptional Tate guide](FiniteTateTopology.md),
[compact coefficient and norm functoriality guide](CompactCoefficientFunctoriality.md),
[finite Tate diagrams guide](FiniteTateDiagrams.md),
[finite norm-row guide](CompactFiniteTateNormSequence.md),
[full-system norm-limit guide](CompactTateNormLimitSequence.md),
[compact norm-row naturality guide](CompactTateNormNaturality.md),
[compact universal-norm limit guide](CompactUniversalNormLimits.md),
[degree-one torsion guide](../README.md#degree-one-torsion) and current Lean
sources for the additional APIs and their exact hypotheses.

Source: pinned Lean `v4.34.0-rc2`, mathlib `e37d88a26f3791ed5a93daa1f949af1021b8d103`,
independent doc-gen4 `97d4ecdfc8e09e7f511724c25e303d448de6a3db`. All 28 production modules (public root and 27 leaves)
and eight checked-use client modules are indexed below. Each complete native displayed
signature retains its implicit, typeclass and universe binders (native pretty-print
abbreviations `⋯`, where present, are linked to their original unelided source).
Source anchors point into this tree; 35 unchanged native records are reused from `f73154dfa181cc8fd00a102c58f221940a335ad0`
with explicit +4 line remaps in NestedInvariants and TopModuleCatUlift; NativeCore is renewed
on the final source. Generated entries can point to their parent; raw origin is in the manifest.
Missing Lean docstrings have explicitly labeled, independently written catalogue prose.
Module prose, private declarations and proof bodies are outside this declaration/instance
index. This is not proof, source-coverage, rights or release certification.
[Reproduction and scope](README.md).

## Production API

### ContinuousGroupCohomology

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### ContinuousGroupCohomology.ClosedTopologicalCoinvariants

64 native named entries; 3 native instance-table rows.

#### PointwiseContinuousMulAction

Kind: `structure`.

```lean
structure PointwiseContinuousMulAction (G : Type uG) (A : Type uA) [Group G] [Group A] [TopologicalSpace A] : Type (max uA uG)
```

**Native source docstring:** An action by multiplicative automorphisms whose individual values are
continuous.  The acting group carries no topology, and this structure makes no
joint-continuity claim.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L36) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.mk

Kind: `ctor`.

```lean
constructor PointwiseContinuousMulAction.mk : {G : Type uG} → {A : Type uA} → [inst : Group G] → [inst_1 : Group A] → [inst_2 : TopologicalSpace A] → (toMonoidHom : G →* MulAut A) → (∀ (g : G), Continuous ⇑(toMonoidHom g)) → PointwiseContinuousMulAction G A
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `PointwiseContinuousMulAction`; the structure fields and parameters are in the displayed signature and source declaration. Closed versus algebraic action-difference quotients for pointwise-continuous actions.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L36) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.toMonoidHom

Kind: `def`.

```lean
abbrev PointwiseContinuousMulAction.toMonoidHom {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (self : PointwiseContinuousMulAction G A) : G →* MulAut A
```

**Native source docstring:** The underlying algebraic action.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L42) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.continuous_toFun

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.continuous_toFun {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (self : PointwiseContinuousMulAction G A) (g : G) : Continuous ⇑(self.toMonoidHom g)
```

**Native source docstring:** Each action value is continuous.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L44) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.instCoeFun

Kind: `instance`.

```lean
instance PointwiseContinuousMulAction.instCoeFun {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] : CoeFun (PointwiseContinuousMulAction G A) fun (x : PointwiseContinuousMulAction G A) => G → A → A
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CoeFun` instance in closed versus algebraic action-difference quotients for pointwise-continuous actions (native type names: `PointwiseContinuousMulAction`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L51) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.ext

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.ext {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] {ρ σ : PointwiseContinuousMulAction G A} (h : ρ.toMonoidHom = σ.toMonoidHom) : ρ = σ
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `ext` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L54) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.ext_iff

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.ext_iff {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] {ρ σ : PointwiseContinuousMulAction G A} : ρ = σ ↔ ρ.toMonoidHom = σ.toMonoidHom
```

**Original catalogue explanation (not a Lean docstring):** The iff characterization named `ext_iff` in closed versus algebraic action-difference quotients for pointwise-continuous actions; use the full signature for both directions and their assumptions.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L54) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map_one

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.map_one {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) (a : A) : (fun (g : G) => ⇑(ρ.toMonoidHom g)) 1 a = a
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `map_one` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L62) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map_mul

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.map_mul {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) (g h : G) (a : A) : (fun (g : G) => ⇑(ρ.toMonoidHom g)) (g * h) a = (fun (g : G) => ⇑(ρ.toMonoidHom g)) g ((fun (g : G) => ⇑(ρ.toMonoidHom g)) h a)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `map_mul` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L66) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.continuousMulEquiv

Kind: `def`.

```lean
def PointwiseContinuousMulAction.continuousMulEquiv {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) (g : G) : A ≃ₜ* A
```

**Native source docstring:** An individual action value, bundled as a continuous multiplicative
equivalence.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L71) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.continuousMulEquiv_apply

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.continuousMulEquiv_apply {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) (g : G) (a : A) : (ρ.continuousMulEquiv g) a = (fun (g : G) => ⇑(ρ.toMonoidHom g)) g a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `continuousMulEquiv_apply` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L84) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.trivial

Kind: `def`.

```lean
def PointwiseContinuousMulAction.trivial {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] : PointwiseContinuousMulAction G A
```

**Native source docstring:** The trivial pointwise continuous action.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L88) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.trivial_apply

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.trivial_apply {G : Type uG} {A : Type uA} [Group G] [Group A] [TopologicalSpace A] (g : G) (a : A) : (fun (g : G) => ⇑(trivial.toMonoidHom g)) g a = a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `trivial_apply` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L93) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.differenceSet

Kind: `def`.

```lean
def PointwiseContinuousMulAction.differenceSet {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : Set A
```

**Native source docstring:** The set of action differences `g • a * a⁻¹`.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L104) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.differenceSubgroup

Kind: `def`.

```lean
def PointwiseContinuousMulAction.differenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : Subgroup A
```

**Native source docstring:** The algebraic subgroup generated by all action differences.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L108) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup

Kind: `def`.

```lean
def PointwiseContinuousMulAction.closedDifferenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : Subgroup A
```

**Native source docstring:** The closed subgroup generated by all action differences.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L112) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.instNormalDifferenceSubgroup

Kind: `instance`.

```lean
instance PointwiseContinuousMulAction.instNormalDifferenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : ρ.differenceSubgroup.Normal
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `Subgroup.Normal` instance in closed versus algebraic action-difference quotients for pointwise-continuous actions (native type names: `PointwiseContinuousMulAction.differenceSubgroup`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L116) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup

Kind: `instance`.

```lean
instance PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : ρ.closedDifferenceSubgroup.Normal
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `Subgroup.Normal` instance in closed versus algebraic action-difference quotients for pointwise-continuous actions (native type names: `PointwiseContinuousMulAction.closedDifferenceSubgroup`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L120) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.AlgebraicCoinvariants

Kind: `def`.

```lean
abbrev PointwiseContinuousMulAction.AlgebraicCoinvariants {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : Type uA
```

**Native source docstring:** Underlying algebraic coinvariants: quotient by the unclosed relation
subgroup.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L124) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.Coinvariants

Kind: `def`.

```lean
abbrev PointwiseContinuousMulAction.Coinvariants {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : Type uA
```

**Native source docstring:** Closed topological coinvariants, carrying mathlib's quotient topology.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L129) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.coinvariantsMk

Kind: `def`.

```lean
def PointwiseContinuousMulAction.coinvariantsMk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : A →ₜ* ρ.Coinvariants
```

**Native source docstring:** The canonical continuous projection to closed topological coinvariants.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L133) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.coinvariantsMk_apply

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.coinvariantsMk_apply {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) (a : A) : ρ.coinvariantsMk a = ↑a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `coinvariantsMk_apply` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L139) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.difference_mem_differenceSubgroup

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.difference_mem_differenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) (g : G) (a : A) : (fun (g : G) => ⇑(ρ.toMonoidHom g)) g a * a⁻¹ ∈ ρ.differenceSubgroup
```

**Native source docstring:** Each action difference belongs to the algebraic relation subgroup.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L144) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.coinvariantsMk_action

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.coinvariantsMk_action {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) (g : G) (a : A) : ρ.coinvariantsMk ((fun (g : G) => ⇑(ρ.toMonoidHom g)) g a) = ρ.coinvariantsMk a
```

**Native source docstring:** The projection identifies an element with each of its translates.  This
also fixes the action-difference orientation used by the construction.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L150) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicMk

Kind: `def`.

```lean
def PointwiseContinuousMulAction.algebraicMk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : A →ₜ* ρ.AlgebraicCoinvariants
```

**Native source docstring:** The algebraic quotient projection.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L160) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicToClosed

Kind: `def`.

```lean
def PointwiseContinuousMulAction.algebraicToClosed {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : ρ.AlgebraicCoinvariants →ₜ* ρ.Coinvariants
```

**Native source docstring:** Canonical comparison from algebraic coinvariants to closed topological
coinvariants.  It is generally a further quotient, not an equivalence.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L166) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicToClosed_algebraicMk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.algebraicToClosed_algebraicMk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) (a : A) : ρ.algebraicToClosed (ρ.algebraicMk a) = ρ.coinvariantsMk a
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `algebraicToClosed_algebraicMk` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L177) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicToClosed_surjective

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.algebraicToClosed_surjective {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : Function.Surjective ⇑ρ.algebraicToClosed
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `algebraicToClosed_surjective` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L182) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup_eq_differenceSubgroup

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.closedDifferenceSubgroup_eq_differenceSubgroup {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) (hρ : IsClosed ↑ρ.differenceSubgroup) : ρ.closedDifferenceSubgroup = ρ.differenceSubgroup
```

**Native source docstring:** If the algebraic relation subgroup is already closed, taking its closure
does not enlarge it.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L189) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.KillsDifferences

Kind: `def`.

```lean
def PointwiseContinuousMulAction.KillsDifferences {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [Group B] (ρ : PointwiseContinuousMulAction G A) (f : A → B) : Prop
```

**Native source docstring:** A homomorphism kills every action difference precisely in the pointwise
form useful for the universal property.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L199) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.differenceSubgroup_le_ker

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.differenceSubgroup_le_ker {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [Group B] (ρ : PointwiseContinuousMulAction G A) (f : A →* B) (hf : ρ.KillsDifferences ⇑f) : ρ.differenceSubgroup ≤ f.ker
```

**Native source docstring:** Killing the generators kills their algebraic closure.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L206) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicLift

Kind: `def`.

```lean
def PointwiseContinuousMulAction.algebraicLift {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) : ρ.AlgebraicCoinvariants →ₜ* B
```

**Native source docstring:** Algebraic universal property, bundled continuously for the quotient
topology: a continuous homomorphism killing every action difference factors
through the unclosed algebraic coinvariants.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L214) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicLift_algebraicMk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.algebraicLift_algebraicMk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) (a : A) : (ρ.algebraicLift f hf) (ρ.algebraicMk a) = f a
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `algebraicLift_algebraicMk` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L227) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicHom_ext

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.algebraicHom_ext {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) {f f' : ρ.AlgebraicCoinvariants →ₜ* B} (h : f.comp ρ.algebraicMk = f'.comp ρ.algebraicMk) : f = f'
```

**Native source docstring:** Continuous homomorphisms out of the algebraic coinvariants are determined
on the canonical projection.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L235) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.liftOfClosed

Kind: `def`.

```lean
def PointwiseContinuousMulAction.liftOfClosed {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.closedDifferenceSubgroup ≤ f.ker) : ρ.Coinvariants →ₜ* B
```

**Native source docstring:** Raw topological universal property.  Without a separation assumption on
the target, the exact condition is that `f` kill the closed relation subgroup.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L246) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.liftOfClosed_mk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.liftOfClosed_mk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.closedDifferenceSubgroup ≤ f.ker) (a : A) : (ρ.liftOfClosed f hf) (ρ.coinvariantsMk a) = f a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `liftOfClosed_mk` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L256) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup_le_ker

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.closedDifferenceSubgroup_le_ker {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] [T1Space B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) : ρ.closedDifferenceSubgroup ≤ f.ker
```

**Native source docstring:** A continuous homomorphism to a T1 group which kills every action
difference kills their closed generated subgroup.  The T1 assumption makes
the target kernel closed; no separation hypothesis is imposed on `A` or `G`.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L262) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.lift

Kind: `def`.

```lean
def PointwiseContinuousMulAction.lift {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] [T1Space B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) : ρ.Coinvariants →ₜ* B
```

**Native source docstring:** Topological universal property for continuous homomorphisms to T1 groups
which kill every action difference.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L274) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.lift_mk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.lift_mk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] [T1Space B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) (a : A) : (ρ.lift f hf) (ρ.coinvariantsMk a) = f a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `lift_mk` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L281) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.algebraicLift_eq_lift_comp

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.algebraicLift_eq_lift_comp {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] [T1Space B] (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B) (hf : ρ.KillsDifferences ⇑f) : ρ.algebraicLift f hf = (ρ.lift f hf).comp ρ.algebraicToClosed
```

**Native source docstring:** The algebraic universal factorization agrees with the closed one through
the canonical algebraic-to-closed comparison whenever the T1 lift is
available.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L287) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.hom_ext

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.hom_ext {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [Group B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) {f f' : ρ.Coinvariants →ₜ* B} (h : f.comp ρ.coinvariantsMk = f'.comp ρ.coinvariantsMk) : f = f'
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `hom_ext` in closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L301) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.IsEquivariant

Kind: `def`.

```lean
def PointwiseContinuousMulAction.IsEquivariant {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [CommGroup B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (f : A → B) : Prop
```

**Native source docstring:** Equivariance of a multiplicative homomorphism for two pointwise
continuous actions of the same group.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L316) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map

Kind: `def`.

```lean
def PointwiseContinuousMulAction.map {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (f : A →ₜ* B) (hf : ρ.IsEquivariant σ ⇑f) : ρ.Coinvariants →ₜ* σ.Coinvariants
```

**Native source docstring:** A continuous equivariant homomorphism induces a continuous homomorphism
on closed topological coinvariants.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L322) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map_mk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.map_mk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (f : A →ₜ* B) (hf : ρ.IsEquivariant σ ⇑f) (a : A) : (ρ.map σ f hf) (ρ.coinvariantsMk a) = σ.coinvariantsMk (f a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `map_mk` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L345) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.isEquivariant_id

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.isEquivariant_id {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] (ρ : PointwiseContinuousMulAction G A) : ρ.IsEquivariant ρ ⇑(ContinuousMonoidHom.id A)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `isEquivariant_id` for closed versus algebraic action-difference quotients for pointwise-continuous actions; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L353) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map_id

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.map_id {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (ρ : PointwiseContinuousMulAction G A) : ρ.map ρ (ContinuousMonoidHom.id A) ⋯ = ContinuousMonoidHom.id ρ.Coinvariants
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `map_id` for closed versus algebraic action-difference quotients for pointwise-continuous actions; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L358) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.isEquivariant_comp

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.isEquivariant_comp {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} {C : Type uC} [CommGroup B] [CommGroup C] [TopologicalSpace B] [TopologicalSpace C] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (τ : PointwiseContinuousMulAction G C) (f : A →ₜ* B) (g : B →ₜ* C) (hf : ρ.IsEquivariant σ ⇑f) (hg : σ.IsEquivariant τ ⇑g) : ρ.IsEquivariant τ ⇑(g.comp f)
```

**Native source docstring:** The composite of equivariant continuous homomorphisms is equivariant.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L371) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.map_comp

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.map_comp {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} {C : Type uC} [CommGroup B] [CommGroup C] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup B] [IsTopologicalGroup C] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (τ : PointwiseContinuousMulAction G C) (f : A →ₜ* B) (g : B →ₜ* C) (hf : ρ.IsEquivariant σ ⇑f) (hg : σ.IsEquivariant τ ⇑g) : ρ.map τ (g.comp f) ⋯ = (σ.map τ g hg).comp (ρ.map σ f hf)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `map_comp` for closed versus algebraic action-difference quotients for pointwise-continuous actions; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L382) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.isEquivariant_symm

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.isEquivariant_symm {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] {B : Type uB} [CommGroup B] [TopologicalSpace B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (e : A ≃ₜ* B) (he : ρ.IsEquivariant σ ⇑e) : σ.IsEquivariant ρ ⇑e.symm
```

**Native source docstring:** Equivariance is preserved by taking the inverse of an equivariant
continuous multiplicative equivalence.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L400) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.congr

Kind: `def`.

```lean
def PointwiseContinuousMulAction.congr {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (e : A ≃ₜ* B) (he : ρ.IsEquivariant σ ⇑e) : ρ.Coinvariants ≃ₜ* σ.Coinvariants
```

**Native source docstring:** A continuous equivariant equivalence induces a continuous equivalence on
closed topological coinvariants.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L412) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.congr_mk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.congr_mk {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] {B : Type uB} [CommGroup B] [TopologicalSpace B] [IsTopologicalGroup B] (ρ : PointwiseContinuousMulAction G A) (σ : PointwiseContinuousMulAction G B) (e : A ≃ₜ* B) (he : ρ.IsEquivariant σ ⇑e) (a : A) : (ρ.congr σ e he) (ρ.coinvariantsMk a) = σ.coinvariantsMk (e a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `congr_mk` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L444) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.differenceSubgroup_trivial

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.differenceSubgroup_trivial {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] : trivial.differenceSubgroup = ⊥
```

**Native source docstring:** The algebraic relation subgroup of the trivial action is trivial.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L462) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup_trivial

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.closedDifferenceSubgroup_trivial {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] : trivial.closedDifferenceSubgroup = ⊥.topologicalClosure
```

**Native source docstring:** Without a T1 hypothesis, trivial-action closed coinvariants quotient by
the closure of `{1}` rather than silently identifying that closure with `{1}`.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L473) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup_trivial_of_t1

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.closedDifferenceSubgroup_trivial_of_t1 {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [T1Space A] : trivial.closedDifferenceSubgroup = ⊥
```

**Native source docstring:** For a T1 coefficient group, the closed relation subgroup of the trivial
action is trivial.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L482) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.differenceSubgroup_eq_bot_of_subsingleton

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.differenceSubgroup_eq_bot_of_subsingleton {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [Subsingleton G] (ρ : PointwiseContinuousMulAction G A) : ρ.differenceSubgroup = ⊥
```

**Native source docstring:** An action by a subsingleton acting group is algebraically trivial.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L494) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.closedDifferenceSubgroup_eq_bot_of_subsingleton

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.closedDifferenceSubgroup_eq_bot_of_subsingleton {G : Type uG} {A : Type uA} [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] [Subsingleton G] [T1Space A] (ρ : PointwiseContinuousMulAction G A) : ρ.closedDifferenceSubgroup = ⊥
```

**Native source docstring:** For a T1 coefficient group, any action by a subsingleton acting group has
trivial closed relation subgroup.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L504) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationAction

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.quotientConjActTopologicalAbelianizationAction {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : PointwiseContinuousMulAction Q (TopologicalAbelianization N)
```

**Native source docstring:** The quotient conjugation action on topological abelianization, packaged as
a pointwise continuous action.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L527) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariants

Kind: `def`.

```lean
abbrev ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariants {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : Type uN
```

**Native source docstring:** Closed topological coinvariants of the quotient conjugation action.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L536) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : TopologicalAbelianization N →ₜ* S.quotientConjActTopologicalAbelianizationCoinvariants
```

**Native source docstring:** The canonical continuous projection from topological abelianization to
closed quotient-conjugation coinvariants.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L541) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk_conjAct

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk_conjAct {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) (n : N) : S.quotientConjActTopologicalAbelianizationCoinvariantsMk ↑((S.conjAct e) n) = S.quotientConjActTopologicalAbelianizationCoinvariantsMk ↑n
```

**Native source docstring:** Arbitrary-lift formula: the coinvariant projection identifies a kernel
class with its conjugate by any chosen lift.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L549) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk_conjAct_eq_of_rightHom_eq

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.quotientConjActTopologicalAbelianizationCoinvariantsMk_conjAct_eq_of_rightHom_eq {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) {e e' : E} (h : S.rightHom e = S.rightHom e') (n : N) : S.quotientConjActTopologicalAbelianizationCoinvariantsMk ↑((S.conjAct e) n) = S.quotientConjActTopologicalAbelianizationCoinvariantsMk ↑((S.conjAct e') n)
```

**Native source docstring:** Lift independence remains explicit at the coinvariant projection.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L562) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationAction

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationAction {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') : S'.quotientConjActTopologicalAbelianizationAction = S.quotientConjActTopologicalAbelianizationAction
```

**Native source docstring:** A continuous equivalence of extensions preserves the packaged quotient
action with the accepted fixed-kernel/fixed-quotient orientation.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L578) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') : S.quotientConjActTopologicalAbelianizationCoinvariants ≃ₜ* S'.quotientConjActTopologicalAbelianizationCoinvariants
```

**Native source docstring:** The induced equivalence on closed coinvariants, in the accepted
source-to-target orientation of an extension equivalence.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L586) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv_mk {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (a : TopologicalAbelianization N) : equiv.quotientConjActTopologicalAbelianizationCoinvariantsEquiv (S.quotientConjActTopologicalAbelianizationCoinvariantsMk a) = S'.quotientConjActTopologicalAbelianizationCoinvariantsMk a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `quotientConjActTopologicalAbelianizationCoinvariantsEquiv_mk` for closed versus algebraic action-difference quotients for pointwise-continuous actions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ClosedTopologicalCoinvariants.lean#L600) (native source start line; generated entries may point to their parent).

#### Native instance table

- `PointwiseContinuousMulAction.instCoeFun`: `CoeFun`; type names: `PointwiseContinuousMulAction`

- `PointwiseContinuousMulAction.instNormalClosedDifferenceSubgroup`: `Subgroup.Normal`; type names: `PointwiseContinuousMulAction.closedDifferenceSubgroup`

- `PointwiseContinuousMulAction.instNormalDifferenceSubgroup`: `Subgroup.Normal`; type names: `PointwiseContinuousMulAction.differenceSubgroup`

### ContinuousGroupCohomology.CompactAddCommGroup

41 native named entries; 7 native instance-table rows.

#### CompHausAddCommGrp

Kind: `structure`.

```lean
structure CompHausAddCommGrp : Type (u + 1)
```

**Native source docstring:** The category of compact Hausdorff topological additive commutative groups.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L34) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.mk

Kind: `ctor`.

```lean
constructor CompHausAddCommGrp.mk : (toCompHaus : CompHaus) → [addCommGroup : AddCommGroup ↑toCompHaus.toTop] → [isTopologicalAddGroup : IsTopologicalAddGroup ↑toCompHaus.toTop] → CompHausAddCommGrp.{u}
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `CompHausAddCommGrp`; the structure fields and parameters are in the displayed signature and source declaration. The category of compact hausdorff additive commutative groups and continuous homomorphisms.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L34) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.toCompHaus

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.toCompHaus (self : CompHausAddCommGrp.{u}) : CompHaus
```

**Native source docstring:** The underlying compact Hausdorff space.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L38) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.addCommGroup

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.addCommGroup (self : CompHausAddCommGrp.{u}) : AddCommGroup ↑self.toCompHaus.toTop
```

**Native source docstring:** The additive commutative group structure.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L40) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.isTopologicalAddGroup

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.isTopologicalAddGroup (self : CompHausAddCommGrp.{u}) : IsTopologicalAddGroup ↑self.toCompHaus.toTop
```

**Native source docstring:** Addition and negation are continuous.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L42) (native source start line; generated entries may point to their parent).

#### instCoeSortCompHausAddCommGrpType

Kind: `instance`.

```lean
instance instCoeSortCompHausAddCommGrpType : CoeSort CompHausAddCommGrp.{u} (Type u)
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CoeSort` instance in the category of compact Hausdorff additive commutative groups and continuous homomorphisms (native type names: `CompHausAddCommGrp`, `_builtin_typeu`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L44) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.of

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.of (A : Type u) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] : CompHausAddCommGrp.{u}
```

**Native source docstring:** Bundle a compact Hausdorff topological additive commutative group.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L52) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.coe_of

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.coe_of (A : Type u) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] : ↑(of A).toCompHaus.toTop = A
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `coe_of` in the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L60) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom

Kind: `structure`.

```lean
structure CompHausAddCommGrp.Hom (A B : CompHausAddCommGrp.{u}) : Type u
```

**Native source docstring:** Morphisms of compact Hausdorff topological additive commutative groups.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L66) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom.mk

Kind: `ctor`.

```lean
constructor CompHausAddCommGrp.Hom.mk : {A B : CompHausAddCommGrp.{u}} → (↑A.toCompHaus.toTop →ₜ+ ↑B.toCompHaus.toTop) → A.Hom B
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `CompHausAddCommGrp.Hom`; the structure fields and parameters are in the displayed signature and source declaration. The category of compact hausdorff additive commutative groups and continuous homomorphisms.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L66) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom.ext

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.Hom.ext {A B : CompHausAddCommGrp.{u}} {x y : A.Hom B} (hom' : x.hom' = y.hom') : x = y
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `ext` in the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L67) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom.ext_iff

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.Hom.ext_iff {A B : CompHausAddCommGrp.{u}} {x y : A.Hom B} : x = y ↔ x.hom' = y.hom'
```

**Original catalogue explanation (not a Lean docstring):** The iff characterization named `ext_iff` in the category of compact Hausdorff additive commutative groups and continuous homomorphisms; use the full signature for both directions and their assumptions.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L67) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom.hom'

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.Hom.hom' {A B : CompHausAddCommGrp.{u}} (self : A.Hom B) : ↑A.toCompHaus.toTop →ₜ+ ↑B.toCompHaus.toTop
```

**Native source docstring:** The underlying continuous additive homomorphism.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L70) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instCategory

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instCategory : CategoryTheory.Category.{u_1, u_1 + 1} CompHausAddCommGrp.{u_1}
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Category` instance in the category of compact Hausdorff additive commutative groups and continuous homomorphisms (native type names: `CompHausAddCommGrp`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L72) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus : CategoryTheory.ConcreteCategory CompHausAddCommGrp.{u_1} fun (A B : CompHausAddCommGrp.{u_1}) => ↑A.toCompHaus.toTop →ₜ+ ↑B.toCompHaus.toTop
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.ConcreteCategory` instance in the category of compact Hausdorff additive commutative groups and continuous homomorphisms (native type names: `CompHausAddCommGrp`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L77) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.Hom.hom

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.Hom.hom {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : ↑A.toCompHaus.toTop →ₜ+ ↑B.toCompHaus.toTop
```

**Native source docstring:** The continuous additive homomorphism underlying a morphism.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L81) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.ofHom

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.ofHom {A B : Type u} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B] [CompactSpace B] [T2Space B] (f : A →ₜ+ B) : of A ⟶ of B
```

**Native source docstring:** Typecheck a continuous additive homomorphism as a categorical morphism.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L85) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus {A B : CompHausAddCommGrp.{u}} : CoeFun (A ⟶ B) fun (x : A ⟶ B) => ↑A.toCompHaus.toTop → ↑B.toCompHaus.toTop
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CoeFun` instance in the category of compact Hausdorff additive commutative groups and continuous homomorphisms (native type names: `Quiver.Hom`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L92) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.hom_id

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.hom_id {A : CompHausAddCommGrp.{u}} : Hom.hom (CategoryTheory.CategoryStruct.id A) = ContinuousAddMonoidHom.id ↑A.toCompHaus.toTop
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `hom_id` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L95) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.hom_comp

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.hom_comp {A B C : CompHausAddCommGrp.{u}} (f : A ⟶ B) (g : B ⟶ C) : Hom.hom (CategoryTheory.CategoryStruct.comp f g) = (Hom.hom g).comp (Hom.hom f)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `hom_comp` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L100) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.hom_ext

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.hom_ext {A B : CompHausAddCommGrp.{u}} {f g : A ⟶ B} (h : Hom.hom f = Hom.hom g) : f = g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `hom_ext` in the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L105) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.hom_ext_iff

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.hom_ext_iff {A B : CompHausAddCommGrp.{u}} {f g : A ⟶ B} : f = g ↔ Hom.hom f = Hom.hom g
```

**Original catalogue explanation (not a Lean docstring):** The iff characterization named `hom_ext_iff` in the category of compact Hausdorff additive commutative groups and continuous homomorphisms; use the full signature for both directions and their assumptions.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L105) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausCompHausContinuousMap

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausCompHausContinuousMap : CategoryTheory.HasForget₂ CompHausAddCommGrp.{u_1} CompHaus
```

**Native source docstring:** Forget a compact Hausdorff topological additive commutative group to its
underlying compact Hausdorff space.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L110) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap : (CategoryTheory.forget₂ CompHausAddCommGrp.{u_1} CompHaus).Faithful
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Faithful` instance in the category of compact Hausdorff additive commutative groups and continuous homomorphisms (native type names: `CategoryTheory.forget₂`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L117) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausAddCommGrpCatAddMonoidHomCarrier

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausAddCommGrpCatAddMonoidHomCarrier : CategoryTheory.HasForget₂ CompHausAddCommGrp.{u_1} AddCommGrpCat
```

**Native source docstring:** Forget to the underlying additive commutative group.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L123) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.ofClosedAddSubgroup

Kind: `def`.

```lean
noncomputable abbrev CompHausAddCommGrp.ofClosedAddSubgroup (A : CompHausAddCommGrp.{u}) (H : ClosedAddSubgroup ↑A.toCompHaus.toTop) : CompHausAddCommGrp.{u}
```

**Native source docstring:** A closed additive subgroup of a compact Hausdorff additive commutative
group is again a compact Hausdorff additive commutative group.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L129) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotient

Kind: `def`.

```lean
noncomputable abbrev CompHausAddCommGrp.quotient (A : CompHausAddCommGrp.{u}) (H : ClosedAddSubgroup ↑A.toCompHaus.toTop) : CompHausAddCommGrp.{u}
```

**Native source docstring:** The quotient by a closed additive subgroup, with its quotient topology.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L137) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelClosedAddSubgroup

Kind: `def`.

```lean
def CompHausAddCommGrp.kernelClosedAddSubgroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : ClosedAddSubgroup ↑A.toCompHaus.toTop
```

**Native source docstring:** The kernel of a continuous additive homomorphism as a closed additive
subgroup.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L143) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelGroup

Kind: `def`.

```lean
noncomputable abbrev CompHausAddCommGrp.kernelGroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : CompHausAddCommGrp.{u}
```

**Native source docstring:** The compact Hausdorff group carried by the kernel of a continuous additive
homomorphism.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L152) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.rangeClosedAddSubgroup

Kind: `def`.

```lean
def CompHausAddCommGrp.rangeClosedAddSubgroup {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : ClosedAddSubgroup ↑B.toCompHaus.toTop
```

**Native source docstring:** The range of a continuous homomorphism from a compact space is a closed
additive subgroup of the Hausdorff target.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L158) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRange

Kind: `def`.

```lean
noncomputable abbrev CompHausAddCommGrp.quotientRange {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : CompHausAddCommGrp.{u}
```

**Native source docstring:** The compact Hausdorff quotient of the target by the range of a continuous
additive homomorphism.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L167) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelι

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.kernelι {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : kernelGroup f ⟶ A
```

**Native source docstring:** The canonical inclusion of the compact Hausdorff kernel.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L173) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRangeπ

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.quotientRangeπ {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) : B ⟶ quotientRange f
```

**Native source docstring:** The canonical projection to the compact Hausdorff quotient by the range.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L182) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelι_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.kernelι_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : ↑(kernelGroup f).toCompHaus.toTop) : (Hom.hom (kernelι f)) x = ↑x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `kernelι_apply` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L189) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.comp_kernelι_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.comp_kernelι_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : ↑(kernelGroup f).toCompHaus.toTop) : (Hom.hom f) ((Hom.hom (kernelι f)) x) = 0
```

**Original catalogue explanation (not a Lean docstring):** The named computation `comp_kernelι_apply` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L194) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRangeπ_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.quotientRangeπ_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : ↑B.toCompHaus.toTop) : (Hom.hom (quotientRangeπ f)) x = ↑x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `quotientRangeπ_apply` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L199) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRangeπ_comp_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.quotientRangeπ_comp_apply {A B : CompHausAddCommGrp.{u}} (f : A ⟶ B) (x : ↑A.toCompHaus.toTop) : (Hom.hom (quotientRangeπ f)) ((Hom.hom f) x) = 0
```

**Original catalogue explanation (not a Lean docstring):** The named computation `quotientRangeπ_comp_apply` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L204) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelMap

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.kernelMap {X Y X' Y' : CompHausAddCommGrp.{u}} (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : ∀ (x : ↑X.toCompHaus.toTop), (Hom.hom g) ((Hom.hom p) x) = (Hom.hom q) ((Hom.hom f) x)) : kernelGroup f ⟶ kernelGroup g
```

**Native source docstring:** A continuous commutative square induces a continuous map on closed
kernels.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L211) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRangeMap

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.quotientRangeMap {X Y X' Y' : CompHausAddCommGrp.{u}} (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : ∀ (x : ↑X.toCompHaus.toTop), (Hom.hom g) ((Hom.hom p) x) = (Hom.hom q) ((Hom.hom f) x)) : quotientRange f ⟶ quotientRange g
```

**Native source docstring:** A continuous commutative square induces a continuous map on quotients by
the two compact ranges.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L228) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.kernelMap_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.kernelMap_apply {X Y X' Y' : CompHausAddCommGrp.{u}} (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : ∀ (x : ↑X.toCompHaus.toTop), (Hom.hom g) ((Hom.hom p) x) = (Hom.hom q) ((Hom.hom f) x)) (x : ↑(kernelGroup f).toCompHaus.toTop) : (Hom.hom (kernelMap p q f g h)) x = ⟨(Hom.hom p) ↑x, ⋯⟩
```

**Original catalogue explanation (not a Lean docstring):** The named computation `kernelMap_apply` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L247) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.quotientRangeMap_mk

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.quotientRangeMap_mk {X Y X' Y' : CompHausAddCommGrp.{u}} (p : X ⟶ X') (q : Y ⟶ Y') (f : X ⟶ Y) (g : X' ⟶ Y') (h : ∀ (x : ↑X.toCompHaus.toTop), (Hom.hom g) ((Hom.hom p) x) = (Hom.hom q) ((Hom.hom f) x)) (y : ↑Y.toCompHaus.toTop) : (Hom.hom (quotientRangeMap p q f g h)) ↑y = ↑((Hom.hom q) y)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `quotientRangeMap_mk` for the category of compact Hausdorff additive commutative groups and continuous homomorphisms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactAddCommGroup.lean#L258) (native source start line; generated entries may point to their parent).

#### Native instance table

- `CompHausAddCommGrp.instCategory`: `CategoryTheory.Category`; type names: `CompHausAddCommGrp`

- `CompHausAddCommGrp.instCoeFunHomForallCarrierToTopTrueToCompHaus`: `CoeFun`; type names: `Quiver.Hom`

- `CompHausAddCommGrp.instConcreteCategoryContinuousAddMonoidHomCarrierToTopTrueToCompHaus`: `CategoryTheory.ConcreteCategory`; type names: `CompHausAddCommGrp`

- `CompHausAddCommGrp.instFaithfulCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap`: `CategoryTheory.Functor.Faithful`; type names: `CategoryTheory.forget₂`

- `CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausAddCommGrpCatAddMonoidHomCarrier`: `CategoryTheory.HasForget₂`; type names: `CompHausAddCommGrp`, `AddCommGrpCat`

- `CompHausAddCommGrp.instHasForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausCompHausContinuousMap`: `CategoryTheory.HasForget₂`; type names: `CompHausAddCommGrp`, `CompHaus`

- `instCoeSortCompHausAddCommGrpType`: `CoeSort`; type names: `CompHausAddCommGrp`, `_builtin_typeu`

### ContinuousGroupCohomology.CompactAddCommGroupLimits

13 native named entries; 4 native instance-table rows.

#### CompHausAddCommGrp.limitConePtAux

Kind: `def`.

```lean
def CompHausAddCommGrp.limitConePtAux {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : AddSubgroup ((j : J) → ↑(F.obj j).toCompHaus.toTop)
```

**Native source docstring:** The compatible tuples underlying a limit of compact Hausdorff additive
commutative groups.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L41) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : AddCommGroup ↑(CompHaus.limitCone (F.comp (CategoryTheory.forget₂ CompHausAddCommGrp.{max u v} CompHaus))).pt.toTop
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `AddCommGroup` instance in limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses (native type names: `TopCat.carrier`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L49) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : IsTopologicalAddGroup ↑(CompHaus.limitCone (F.comp (CategoryTheory.forget₂ CompHausAddCommGrp.{max u v} CompHaus))).pt.toTop
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `IsTopologicalAddGroup` instance in limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses (native type names: `TopCat.carrier`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L53) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limitCone

Kind: `def`.

```lean
abbrev CompHausAddCommGrp.limitCone {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : CategoryTheory.Limits.Cone F
```

**Native source docstring:** The explicit limit cone in compact Hausdorff additive commutative groups.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L57) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limitConeIsLimit

Kind: `def`.

```lean
def CompHausAddCommGrp.limitConeIsLimit {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : CategoryTheory.Limits.IsLimit (limitCone F)
```

**Native source docstring:** The explicit cone is limiting.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L77) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instHasLimit

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instHasLimit {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : CategoryTheory.Limits.HasLimit F
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Limits.HasLimit` instance in limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses; the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L100) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap

Kind: `instance`.

```lean
instance CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) : CategoryTheory.Limits.PreservesLimit F (CategoryTheory.forget₂ CompHausAddCommGrp.{max u v} CompHaus)
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Limits.PreservesLimit` instance in limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses (native type names: `CategoryTheory.forget₂`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L103) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limit_π_range_eq_eventualRange

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.limit_π_range_eq_eventualRange {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) [CategoryTheory.IsCofilteredOrEmpty J] (j : J) : Set.range ⇑(Hom.hom (CategoryTheory.Limits.limit.π F j)) = (F.comp (CategoryTheory.forget CompHausAddCommGrp.{max u v})).eventualRange j
```

**Native source docstring:** In a cofiltered diagram of compact Hausdorff additive commutative groups,
the range of a canonical limit projection is exactly the intersection of the
ranges of all transition maps into that stage.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L233) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limit_π_surjective_of_eventualRange_eq_univ

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.limit_π_surjective_of_eventualRange_eq_univ {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) [CategoryTheory.IsCofilteredOrEmpty J] (j : J) (h : (F.comp (CategoryTheory.forget CompHausAddCommGrp.{max u v})).eventualRange j = Set.univ) : Function.Surjective ⇑(Hom.hom (CategoryTheory.Limits.limit.π F j))
```

**Native source docstring:** A canonical projection from a cofiltered compact Hausdorff additive-group
limit is surjective when the eventual range at that stage is the whole stage.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L249) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limit_π_surjective_of_maps_surjective

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.limit_π_surjective_of_maps_surjective {J : Type v} [CategoryTheory.SmallCategory J] (F : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) [CategoryTheory.IsCofilteredOrEmpty J] (j : J) (h : ∀ {i : J} (f : i ⟶ j), Function.Surjective ⇑(Hom.hom (F.map f))) : Function.Surjective ⇑(Hom.hom (CategoryTheory.Limits.limit.π F j))
```

**Native source docstring:** A canonical projection from a cofiltered compact Hausdorff additive-group
limit is surjective if every transition map into that stage is surjective.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L257) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.instHasLimitsOfShape

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.instHasLimitsOfShape {J : Type v} [CategoryTheory.SmallCategory J] : CategoryTheory.Limits.HasLimitsOfShape J CompHausAddCommGrp.{max u v}
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for limits of compact Hausdorff additive commutative groups, including the stated indexing hypotheses; local instance syntax does not by itself promise a global public instance.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L270) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limit_map_surjective

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.limit_map_surjective {J : Type v} [CategoryTheory.SmallCategory J] (F G : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) (η : F ⟶ G) [CategoryTheory.IsCofilteredOrEmpty J] (hη : ∀ (k : J), Function.Surjective ⇑(Hom.hom (η.app k))) : Function.Surjective ⇑(Hom.hom (CategoryTheory.Limits.lim.map η))
```

**Native source docstring:** A pointwise-surjective natural transformation between cofiltered diagrams
of compact Hausdorff additive commutative groups induces a surjective map on
their limits.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L440) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.limit_map_exact

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.limit_map_exact {J : Type v} [CategoryTheory.SmallCategory J] (F G : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) (η : F ⟶ G) (H : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) (θ : G ⟶ H) [CategoryTheory.IsCofilteredOrEmpty J] (h : ∀ (k : J), Function.Exact ⇑(Hom.hom (η.app k)) ⇑(Hom.hom (θ.app k))) : Function.Exact ⇑(Hom.hom (CategoryTheory.Limits.lim.map η)) ⇑(Hom.hom (CategoryTheory.Limits.lim.map θ))
```

**Native source docstring:** Pointwise exact natural transformations between cofiltered diagrams of
compact Hausdorff additive commutative groups induce exact maps on their
limits.

[Source](../ContinuousGroupCohomology/CompactAddCommGroupLimits.lean#L463) (native source start line; generated entries may point to their parent).

#### Native instance table

- `CompHausAddCommGrp.instAddCommGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap`: `AddCommGroup`; type names: `TopCat.carrier`

- `CompHausAddCommGrp.instHasLimit`: `CategoryTheory.Limits.HasLimit`; type names: none

- `CompHausAddCommGrp.instIsTopologicalAddGroupCarrierToTopTruePtCompHausLimitConeCompForget₂ContinuousAddMonoidHomToCompHausContinuousMap`: `IsTopologicalAddGroup`; type names: `TopCat.carrier`

- `CompHausAddCommGrp.instPreservesLimitCompHausForget₂ContinuousAddMonoidHomCarrierToTopTrueToCompHausContinuousMap`: `CategoryTheory.Limits.PreservesLimit`; type names: `CategoryTheory.forget₂`

### ContinuousGroupCohomology.CompactFiniteHomology

10 native named entries; 0 native instance-table rows.

#### CompHausAddCommGrp.finiteFinsuppTopology

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.finiteFinsuppTopology (X : CompHausAddCommGrp.{u}) (I : Type u) [Finite I] : TopologicalSpace (I →₀ ↑X.toCompHaus.toTop)
```

**Native source docstring:** The finite-product topology on finitely supported functions, transported
from the equivalent finite function space.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L33) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.finiteFinsuppHomeomorph

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.finiteFinsuppHomeomorph (X : CompHausAddCommGrp.{u}) (I : Type u) [Finite I] : (I →₀ ↑X.toCompHaus.toTop) ≃ₜ (I → ↑X.toCompHaus.toTop)
```

**Native source docstring:** The defining homeomorphism from finite-support functions to the finite
function space.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L40) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.finiteFinsupp

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.finiteFinsupp (X : CompHausAddCommGrp.{u}) (I : Type u) [Finite I] : CompHausAddCommGrp.{u}
```

**Native source docstring:** A finite product of a compact Hausdorff additive commutative group,
presented as a `Finsupp`.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L49) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.finiteFinsuppMap

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.finiteFinsuppMap (X Y : CompHausAddCommGrp.{u}) (I J : Type u) [Fintype I] [Fintype J] (f : (I →₀ ↑X.toCompHaus.toTop) →+ J →₀ ↑Y.toCompHaus.toTop) (hf : ∀ (i : I) (j : J), Continuous fun (x : ↑X.toCompHaus.toTop) => (f (Finsupp.single i x)) j) : X.finiteFinsupp I ⟶ Y.finiteFinsupp J
```

**Native source docstring:** An additive map between finite products is continuous if every
single-input/single-output matrix coefficient is continuous.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L62) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.finiteFinsuppMap_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.finiteFinsuppMap_apply (X Y : CompHausAddCommGrp.{u}) (I J : Type u) [Fintype I] [Fintype J] (f : (I →₀ ↑X.toCompHaus.toTop) →+ J →₀ ↑Y.toCompHaus.toTop) (hf : ∀ (i : I) (j : J), Continuous fun (x : ↑X.toCompHaus.toTop) => (f (Finsupp.single i x)) j) (x : I →₀ ↑X.toCompHaus.toTop) : (Hom.hom (X.finiteFinsuppMap Y I J f hf)) x = f x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteFinsuppMap_apply` for finite-stage homology maps for compact additive-group constructions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L105) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.boundaryToKernel

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.boundaryToKernel {X₂ X₁ X₀ : CompHausAddCommGrp.{u}} (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀) (hd : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom d₁) ((Hom.hom d₂) x) = 0) : X₂ ⟶ kernelGroup d₁
```

**Native source docstring:** Restrict the first boundary of a continuous three-term complex to the
closed kernel of the second boundary.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L113) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.boundaryToKernel_apply

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.boundaryToKernel_apply {X₂ X₁ X₀ : CompHausAddCommGrp.{u}} (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀) (hd : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom d₁) ((Hom.hom d₂) x) = 0) (x : ↑X₂.toCompHaus.toTop) : (Hom.hom (boundaryToKernel d₂ d₁ hd)) x = ⟨(Hom.hom d₂) x, ⋯⟩
```

**Original catalogue explanation (not a Lean docstring):** The named computation `boundaryToKernel_apply` for finite-stage homology maps for compact additive-group constructions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L127) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.homology

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.homology {X₂ X₁ X₀ : CompHausAddCommGrp.{u}} (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀) (hd : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom d₁) ((Hom.hom d₂) x) = 0) : CompHausAddCommGrp.{u}
```

**Native source docstring:** Compact Hausdorff homology of a continuous three-term complex.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L135) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.homologyMap

Kind: `def`.

```lean
noncomputable def CompHausAddCommGrp.homologyMap {X₂ X₁ X₀ Y₂ Y₁ Y₀ : CompHausAddCommGrp.{u}} (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀) (e₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ Y₀) (hd : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom d₁) ((Hom.hom d₂) x) = 0) (he : ∀ (x : ↑Y₂.toCompHaus.toTop), (Hom.hom e₁) ((Hom.hom e₂) x) = 0) (p₂ : X₂ ⟶ Y₂) (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀) (h₁ : ∀ (x : ↑X₁.toCompHaus.toTop), (Hom.hom e₁) ((Hom.hom p₁) x) = (Hom.hom p₀) ((Hom.hom d₁) x)) (h₂ : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom e₂) ((Hom.hom p₂) x) = (Hom.hom p₁) ((Hom.hom d₂) x)) : homology d₂ d₁ hd ⟶ homology e₂ e₁ he
```

**Native source docstring:** A commuting map of continuous three-term complexes induces a continuous
map on compact Hausdorff homology.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L142) (native source start line; generated entries may point to their parent).

#### CompHausAddCommGrp.homologyMap_mk

Kind: `theorem`.

```lean
theorem CompHausAddCommGrp.homologyMap_mk {X₂ X₁ X₀ Y₂ Y₁ Y₀ : CompHausAddCommGrp.{u}} (d₂ : X₂ ⟶ X₁) (d₁ : X₁ ⟶ X₀) (e₂ : Y₂ ⟶ Y₁) (e₁ : Y₁ ⟶ Y₀) (hd : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom d₁) ((Hom.hom d₂) x) = 0) (he : ∀ (x : ↑Y₂.toCompHaus.toTop), (Hom.hom e₁) ((Hom.hom e₂) x) = 0) (p₂ : X₂ ⟶ Y₂) (p₁ : X₁ ⟶ Y₁) (p₀ : X₀ ⟶ Y₀) (h₁ : ∀ (x : ↑X₁.toCompHaus.toTop), (Hom.hom e₁) ((Hom.hom p₁) x) = (Hom.hom p₀) ((Hom.hom d₁) x)) (h₂ : ∀ (x : ↑X₂.toCompHaus.toTop), (Hom.hom e₂) ((Hom.hom p₂) x) = (Hom.hom p₁) ((Hom.hom d₂) x)) (x : ↑(kernelGroup d₁).toCompHaus.toTop) : (Hom.hom (homologyMap d₂ d₁ e₂ e₁ hd he p₂ p₁ p₀ h₁ h₂)) ↑x = ↑((Hom.hom (kernelMap p₁ p₀ d₁ e₁ h₁)) x)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `homologyMap_mk` for finite-stage homology maps for compact additive-group constructions; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/CompactFiniteHomology.lean#L162) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.CompactTopModuleLimits

4 native named entries; 0 native instance-table rows.

#### TopModuleCat.compHausDiagram

Kind: `def`.

```lean
noncomputable def TopModuleCat.compHausDiagram {J : Type v} [CategoryTheory.SmallCategory J] {R : Type u} [Ring R] [TopologicalSpace R] (F : CategoryTheory.Functor J (TopModuleCat R)) [∀ (j : J), CompactSpace ↑(F.obj j).toModuleCat] [∀ (j : J), T2Space ↑(F.obj j).toModuleCat] : CategoryTheory.Functor J CompHaus
```

**Native source docstring:** A diagram of compact Hausdorff spaces obtained by forgetting the module
structure from a diagram of compact Hausdorff topological modules.

[Source](../ContinuousGroupCohomology/CompactTopModuleLimits.lean#L38) (native source start line; generated entries may point to their parent).

#### TopModuleCat.limitCompHausHomeomorph

Kind: `def`.

```lean
noncomputable def TopModuleCat.limitCompHausHomeomorph {J : Type v} [CategoryTheory.SmallCategory J] {R : Type u} [Ring R] [TopologicalSpace R] (F : CategoryTheory.Functor J (TopModuleCat R)) [∀ (j : J), CompactSpace ↑(F.obj j).toModuleCat] [∀ (j : J), T2Space ↑(F.obj j).toModuleCat] : ↑(CategoryTheory.Limits.limit F).toModuleCat ≃ₜ ↑(CompHaus.limitCone (compHausDiagram F)).pt.toTop
```

**Native source docstring:** The canonical homeomorphism from the underlying space of a
`TopModuleCat` limit to the underlying space of the same limit formed in
`CompHaus`.

[Source](../ContinuousGroupCohomology/CompactTopModuleLimits.lean#L47) (native source start line; generated entries may point to their parent).

#### TopModuleCat.compactSpace_limit_of_compact_t2

Kind: `theorem`.

```lean
theorem TopModuleCat.compactSpace_limit_of_compact_t2 {J : Type v} [CategoryTheory.SmallCategory J] {R : Type u} [Ring R] [TopologicalSpace R] (F : CategoryTheory.Functor J (TopModuleCat R)) [∀ (j : J), CompactSpace ↑(F.obj j).toModuleCat] [∀ (j : J), T2Space ↑(F.obj j).toModuleCat] : CompactSpace ↑(CategoryTheory.Limits.limit F).toModuleCat
```

**Native source docstring:** A limit of compact Hausdorff topological modules is compact.

[Source](../ContinuousGroupCohomology/CompactTopModuleLimits.lean#L59) (native source start line; generated entries may point to their parent).

#### TopModuleCat.t2Space_limit_of_compact_t2

Kind: `theorem`.

```lean
theorem TopModuleCat.t2Space_limit_of_compact_t2 {J : Type v} [CategoryTheory.SmallCategory J] {R : Type u} [Ring R] [TopologicalSpace R] (F : CategoryTheory.Functor J (TopModuleCat R)) [∀ (j : J), CompactSpace ↑(F.obj j).toModuleCat] [∀ (j : J), T2Space ↑(F.obj j).toModuleCat] : T2Space ↑(CategoryTheory.Limits.limit F).toModuleCat
```

**Native source docstring:** A limit of compact Hausdorff topological modules is Hausdorff.

[Source](../ContinuousGroupCohomology/CompactTopModuleLimits.lean#L65) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.Composition

38 native named entries; 1 native instance-table rows.

#### OpenSubgroup.trans

Kind: `def`.

```lean
def OpenSubgroup.trans {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : OpenSubgroup G
```

**Native source docstring:** Flatten an open subgroup of an open subgroup into the ambient group.
Its underlying subgroup computes as the image of the nested subgroup.

[Source](../ContinuousGroupCohomology/Composition.lean#L40) (native source start line; generated entries may point to their parent).

#### OpenSubgroup.trans_toSubgroup

Kind: `theorem`.

```lean
theorem OpenSubgroup.trans_toSubgroup {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : ↑(H.trans K) = Subgroup.map (↑H).subtype ↑K
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `trans_toSubgroup` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L50) (native source start line; generated entries may point to their parent).

#### OpenSubgroup.transEquiv

Kind: `def`.

```lean
noncomputable def OpenSubgroup.transEquiv {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : ↥K ≃ₜ* ↥(H.trans K)
```

**Native source docstring:** The flattened subgroup has the same topological group as the nested subgroup.
The equivalence computes on subgroup elements.

[Source](../ContinuousGroupCohomology/Composition.lean#L54) (native source start line; generated entries may point to their parent).

#### OpenSubgroup.transEquiv_apply

Kind: `theorem`.

```lean
theorem OpenSubgroup.transEquiv_apply {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (x : ↥K) : ↑((H.transEquiv K) x) = ↑↑x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transEquiv_apply` for composition of degree-one transfer over towers of open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Composition.lean#L72) (native source start line; generated entries may point to their parent).

#### OpenSubgroup.transEquiv_symm_apply

Kind: `theorem`.

```lean
theorem OpenSubgroup.transEquiv_symm_apply {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (x : ↥(H.trans K)) : ↑↑((H.transEquiv K).symm x) = ↑x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transEquiv_symm_apply` for composition of degree-one transfer over towers of open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Composition.lean#L77) (native source start line; generated entries may point to their parent).

#### OpenSubgroup.transFiniteIndex

Kind: `instance`.

```lean
instance OpenSubgroup.transFiniteIndex {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] : (↑(H.trans K)).FiniteIndex
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `Subgroup.FiniteIndex` instance in composition of degree-one transfer over towers of open finite-index subgroups (native type names: `OpenSubgroup.toSubgroup`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/Composition.lean#L88) (native source start line; generated entries may point to their parent).

#### TopRep.jointlyContinuous_res_trans

Kind: `theorem`.

```lean
theorem TopRep.jointlyContinuous_res_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (X : TopRep k G) [X.JointlyContinuous] : (res (↑K).subtype (res (↑H).subtype X)).JointlyContinuous
```

**Native source docstring:** Joint continuity of an action persists under two nested open-subgroup
restrictions. This proof is the existing private local instance, made available
to exported compositions without changing the instance search of importers.

[Source](../ContinuousGroupCohomology/Composition.lean#L110) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.transContinuousHom

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.transContinuousHom {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : ↥K →ₜ* ↥(H.trans K)
```

**Native source docstring:** The continuous homomorphism identifying a nested open subgroup with its
flattening in the ambient group. Its value computes via `transEquiv`.

[Source](../ContinuousGroupCohomology/Composition.lean#L126) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.transCoeffHom

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.transCoeffHom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : TopRep.res (↑(transContinuousHom H K)) (TopRep.res (↑(H.trans K)).subtype X) ⟶ TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X)
```

**Native source docstring:** Identity on coefficients, comparing direct and iterated restriction.

[Source](../ContinuousGroupCohomology/Composition.lean#L133) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedTrans

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.crossedTrans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) : ↥(continuousCrossedHom (TopRep.res (↑(H.trans K)).subtype X)) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X)))
```

**Native source docstring:** Pull a crossed homomorphism for the flattened subgroup back to the nested
subgroup through the canonical equivalence. Evaluation computes by pullback.

[Source](../ContinuousGroupCohomology/Composition.lean#L142) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedTrans_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedTrans_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (f : ↥(continuousCrossedHom (TopRep.res (↑(H.trans K)).subtype X))) (g : ↥K) : ↑((crossedTrans X H K) f) g = ↑f ((H.transEquiv K) g)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedTrans_apply` for composition of degree-one transfer over towers of open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Composition.lean#L162) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.towerRep

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.towerRep {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) : G
```

**Native source docstring:** The representative `u * t` obtained from nested right transversals.
Its multiplication computes in the transversal product equivalence.

[Source](../ContinuousGroupCohomology/Composition.lean#L170) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.towerRep_injective

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.towerRep_injective {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : Function.Injective (towerRep H K U T)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `towerRep_injective` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L179) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.towerRepEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.towerRepEquiv {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : ↑↑U × ↑↑T ≃ ↑(Set.range (towerRep H K U T))
```

**Native source docstring:** The canonical indexing equivalence for the product transversal.
Evaluation computes to the product representative.

[Source](../ContinuousGroupCohomology/Composition.lean#L188) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.towerRepEquiv_apply_coe

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.towerRepEquiv_apply_coe {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) : ↑((towerRepEquiv H K U T) p) = towerRep H K U T p
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `towerRepEquiv_apply_coe` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L197) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.towerDecompositionEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.towerDecompositionEquiv {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : G ≃ ↥K × ↑↑U × ↑↑T
```

**Native source docstring:** Decomposition of the ambient group through two nested right transversals.
The inverse computes when constructing the composite right transversal.

[Source](../ContinuousGroupCohomology/Composition.lean#L203) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transRightTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transRightTransversal {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : (↑(H.trans K)).RightTransversal
```

**Native source docstring:** Products of representatives for `K` in `H` and `H` in `G` form a
right transversal for the flattened copy of `K` in `G`. Its carrier computes
as the range of the representative-product map.

[Source](../ContinuousGroupCohomology/Composition.lean#L213) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.coe_transRightTransversal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.coe_transRightTransversal {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : ↑(transRightTransversal H K U T) = Set.range (towerRep H K U T)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `coe_transRightTransversal` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L247) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transRightRepEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transRightRepEquiv {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) : ↑↑U × ↑↑T ≃ ↑↑(transRightTransversal H K U T)
```

**Native source docstring:** The product indexing equivalence with the actual composite transversal.
Its application computes the representative product.

[Source](../ContinuousGroupCohomology/Composition.lean#L253) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transRightRepEquiv_apply_coe

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transRightRepEquiv_apply_coe {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) : ↑((transRightRepEquiv H K U T) p) = towerRep H K U T p
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transRightRepEquiv_apply_coe` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L275) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transRightTransversal_equiv

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transRightTransversal_equiv {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) (g : G) : ⋯.equiv (↑((transRightRepEquiv H K U T) p) * g) = ((H.transEquiv K) (factor U p.1 (factor T p.2 g)), (transRightRepEquiv H K U T) (next U p.1 (factor T p.2 g), next T p.2 g))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transRightTransversal_equiv` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L282) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor_transRightTransversal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.factor_transRightTransversal {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) (g : G) : factor (transRightTransversal H K U T) ((transRightRepEquiv H K U T) p) g = (H.transEquiv K) (factor U p.1 (factor T p.2 g))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factor_transRightTransversal` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L305) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.next_transRightTransversal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.next_transRightTransversal {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) (K : OpenSubgroup ↥H) (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (p : ↑↑U × ↑↑T) (g : G) : next (transRightTransversal H K U T) ((transRightRepEquiv H K U T) p) g = (transRightRepEquiv H K U T) (next U p.1 (factor T p.2 g), next T p.2 g)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `next_transRightTransversal` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L313) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑(H.trans K)).subtype X))) : (transferCrossed X H T) ((transferCrossed (TopRep.res (↑H).subtype X) K U) ((crossedTrans X H K) f)) = (transferCrossed X (H.trans K) (transRightTransversal H K U T)) f
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferCrossed_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L321) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedTrans_principal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedTrans_principal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] (x : ↑X) : (crossedTrans X H K) ((principalToCrossed (TopRep.res (↑(H.trans K)).subtype X)) x) = (principalToCrossed (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedTrans_principal` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L368) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedQuotientTrans

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.crossedQuotientTrans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑(H.trans K)).subtype X)) ⧸ principalCocycles (TopRep.res (↑(H.trans K)).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))) ⧸ principalCocycles (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))
```

**Native source docstring:** Pullback along the nested/flattened equivalence descends modulo principal
cocycles. Its lift computes on quotient representatives.

[Source](../ContinuousGroupCohomology/Composition.lean#L378) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedQuotientTrans_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedQuotientTrans_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑(H.trans K)).subtype X))) : (crossedQuotientTrans X H K) ((principalCocycles (TopRep.res (↑(H.trans K)).subtype X)).mkQ f) = (principalCocycles (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).mkQ ((crossedTrans X H K) f)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedQuotientTrans_mk` for composition of degree-one transfer over towers of open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Composition.lean#L410) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedTrans_comp_mkQL

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedTrans_comp_mkQL {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedTrans X H K)) (TopModuleCat.ofHom (principalCocycles (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).mkQL) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (principalCocycles (TopRep.res (↑(H.trans K)).subtype X)).mkQL) (TopModuleCat.ofHom (crossedQuotientTrans X H K))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedTrans_comp_mkQL` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L423) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) [X.JointlyContinuous] : transferQuotient X H T ∘SL transferQuotient (TopRep.res (↑H).subtype X) K U ∘SL crossedQuotientTrans X H K = transferQuotient X (H.trans K) (transRightTransversal H K U T)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferQuotient_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L437) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] : CategoryTheory.CategoryStruct.comp (cocyclesMap (transContinuousHom H K) (transCoeffHom X H K) 1) (cocyclesOneCrossedIso (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).hom = CategoryTheory.CategoryStruct.comp (cocyclesOneCrossedIso (TopRep.res (↑(H.trans K)).subtype X)).hom (TopModuleCat.ofHom (crossedTrans X H K))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `cocyclesOneCrossedIso_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L460) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] : CategoryTheory.CategoryStruct.comp (map (transContinuousHom H K) (transCoeffHom X H K) 1) (homologyQuotientIso (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).hom = CategoryTheory.CategoryStruct.comp (homologyQuotientIso (TopRep.res (↑(H.trans K)).subtype X)).hom (TopModuleCat.ofHom (crossedQuotientTrans X H K))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `homologyQuotientIso_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L487) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))) ⧸ principalCocycles (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))) ⟶ Z) : CategoryTheory.CategoryStruct.comp (map (transContinuousHom H K) (transCoeffHom X H K) 1) (CategoryTheory.CategoryStruct.comp (homologyQuotientIso (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).hom h) = CategoryTheory.CategoryStruct.comp (homologyQuotientIso (TopRep.res (↑(H.trans K)).subtype X)).hom (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientTrans X H K)) h)
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated reassociated statement associated with `ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the original `@[reassoc]` source anchor is shown below.

[Source](../ContinuousGroupCohomology/Composition.lean#L487) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.degreeOneIso_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.degreeOneIso_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientTrans X H K)) (degreeOneIso (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))).hom = CategoryTheory.CategoryStruct.comp (degreeOneIso (TopRep.res (↑(H.trans K)).subtype X)).hom (map (transContinuousHom H K) (transCoeffHom X H K) 1)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `degreeOneIso_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L507) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transDegreeOne

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transDegreeOne {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] : continuousCohomology 1 (TopRep.res (↑(H.trans K)).subtype X) ⟶ continuousCohomology 1 (TopRep.res (↑K).subtype (TopRep.res (↑H).subtype X))
```

**Native source docstring:** Degree-one transport from a flattened subgroup to the corresponding
nested subgroup, expressed through crossed homomorphisms.

[Source](../ContinuousGroupCohomology/Composition.lean#L524) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transDegreeOne_eq_map

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transDegreeOne_eq_map {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [X.JointlyContinuous] [LocallyCompactSpace ↥(H.trans K)] [LocallyCompactSpace ↥K] : transDegreeOne X H K = map (transContinuousHom H K) (transCoeffHom X H K) 1
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transDegreeOne_eq_map` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L540) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] (U : (↑K).RightTransversal) (T : (↑H).RightTransversal) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(H.trans K)] : CategoryTheory.CategoryStruct.comp (transDegreeOne X H K) (CategoryTheory.CategoryStruct.comp (corestrictionOneWithTransversal (TopRep.res (↑H).subtype X) K U) (corestrictionOneWithTransversal X H T)) = corestrictionOneWithTransversal X (H.trans K) (transRightTransversal H K U T)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `corestrictionOneWithTransversal_trans` in composition of degree-one transfer over towers of open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Composition.lean#L550) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_trans_crossed

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_trans_crossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(H.trans K)] : CategoryTheory.CategoryStruct.comp (transDegreeOne X H K) (CategoryTheory.CategoryStruct.comp (corestrictionOne (TopRep.res (↑H).subtype X) K) (corestrictionOne X H)) = corestrictionOne X (H.trans K)
```

**Native source docstring:** Degree-one corestriction is transitive through nested open finite-index
subgroups, after the canonical flattened/nested identification.

[Source](../ContinuousGroupCohomology/Composition.lean#L581) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_trans

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_trans {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (K : OpenSubgroup ↥H) [(↑H).FiniteIndex] [(↑K).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(H.trans K)] : CategoryTheory.CategoryStruct.comp (map (transContinuousHom H K) (transCoeffHom X H K) 1) (CategoryTheory.CategoryStruct.comp (corestrictionOne (TopRep.res (↑H).subtype X) K) (corestrictionOne X H)) = corestrictionOne X (H.trans K)
```

**Native source docstring:** Degree-one corestriction is transitive through nested open finite-index
subgroups, using native continuous-cohomology transport along the canonical
equivalence with the flattened subgroup.

[Source](../ContinuousGroupCohomology/Composition.lean#L602) (native source start line; generated entries may point to their parent).

#### Native instance table

- `OpenSubgroup.transFiniteIndex`: `Subgroup.FiniteIndex`; type names: `OpenSubgroup.toSubgroup`

### ContinuousGroupCohomology.ContinuousCohomologyUlift

8 native named entries; 0 native instance-table rows.

#### TopRep.continuousCohomologyUliftIsoSameUniverse

Kind: `def`.

```lean
noncomputable def TopRep.continuousCohomologyUliftIsoSameUniverse {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : (TopModuleCat.uliftFunctor.{v, v, u} k).obj (continuousCohomology n X) ≅ continuousCohomology n X.ulift
```

**Native source docstring:** In one common small universe, continuous cohomology commutes with raising
the acting group and coefficient carrier.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L31) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftIsoSameUniverse_naturality

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftIsoSameUniverse_naturality {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) : CategoryTheory.CategoryStruct.comp ((TopModuleCat.uliftFunctor.{v, v, u} k).map (ContinuousCohomology.map (ContinuousMonoidHom.id G) f n)) (Y.continuousCohomologyUliftIsoSameUniverse n).hom = CategoryTheory.CategoryStruct.comp (X.continuousCohomologyUliftIsoSameUniverse n).hom (ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f) n)
```

**Native source docstring:** The same-universe continuous-cohomology comparison is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L45) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftIsoSameUniverse_naturality_assoc

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftIsoSameUniverse_naturality_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) {Z : TopModuleCat k} (h : continuousCohomology n Y.ulift ⟶ Z) : CategoryTheory.CategoryStruct.comp ((TopModuleCat.uliftFunctor.{v, v, u} k).map (ContinuousCohomology.map (ContinuousMonoidHom.id G) f n)) (CategoryTheory.CategoryStruct.comp (Y.continuousCohomologyUliftIsoSameUniverse n).hom h) = CategoryTheory.CategoryStruct.comp (X.continuousCohomologyUliftIsoSameUniverse n).hom (CategoryTheory.CategoryStruct.comp (ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f) n) h)
```

**Native source docstring:** The same-universe continuous-cohomology comparison is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L47) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftMapSameUniverse

Kind: `def`.

```lean
noncomputable def TopRep.continuousCohomologyUliftMapSameUniverse {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) : continuousCohomology n X.ulift ⟶ continuousCohomology n Y.ulift
```

**Native source docstring:** Transport a coefficient map through the same-universe continuous-
cohomology comparison.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L78) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftMapSameUniverse_eq_map

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftMapSameUniverse_eq_map {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) : continuousCohomologyUliftMapSameUniverse f n = ContinuousCohomology.map (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f) n
```

**Native source docstring:** The transported same-universe coefficient map is exactly mathlib's native
continuous-cohomology map on the raised representations.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L89) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftMapSameUniverse_id

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftMapSameUniverse_id {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : continuousCohomologyUliftMapSameUniverse (CategoryTheory.CategoryStruct.id X) n = CategoryTheory.CategoryStruct.id (continuousCohomology n X.ulift)
```

**Native source docstring:** The transported same-universe coefficient map preserves identities.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L102) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftMapSameUniverse_comp

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftMapSameUniverse_comp {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y Z : TopRep k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : continuousCohomologyUliftMapSameUniverse (CategoryTheory.CategoryStruct.comp f g) n = CategoryTheory.CategoryStruct.comp (continuousCohomologyUliftMapSameUniverse f n) (continuousCohomologyUliftMapSameUniverse g n)
```

**Native source docstring:** The transported same-universe coefficient map preserves composition.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L113) (native source start line; generated entries may point to their parent).

#### TopRep.continuousCohomologyUliftMapSameUniverse_comp_assoc

Kind: `theorem`.

```lean
theorem TopRep.continuousCohomologyUliftMapSameUniverse_comp_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y Z : TopRep k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) {Z✝ : TopModuleCat k} (h : continuousCohomology n Z.ulift ⟶ Z✝) : CategoryTheory.CategoryStruct.comp (continuousCohomologyUliftMapSameUniverse (CategoryTheory.CategoryStruct.comp f g) n) h = CategoryTheory.CategoryStruct.comp (continuousCohomologyUliftMapSameUniverse f n) (CategoryTheory.CategoryStruct.comp (continuousCohomologyUliftMapSameUniverse g n) h)
```

**Native source docstring:** The transported same-universe coefficient map preserves composition.

[Source](../ContinuousGroupCohomology/ContinuousCohomologyUlift.lean#L114) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.ContinuousGroupExtension

31 native named entries; 3 native instance-table rows.

#### ContinuousGroupExtension

Kind: `structure`.

```lean
structure ContinuousGroupExtension (N : Type uN) (E : Type uE) (Q : Type uQ) [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] extends GroupExtension N E Q : Type (max (max uE uN) uQ)
```

**Native source docstring:** A group extension whose inclusion and projection form a short exact
sequence of topological groups in the strong sense of
`TopologicalGroup.IsSES`.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L30) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupExtension.mk : {N : Type uN} → {E : Type uE} → {Q : Type uQ} → [inst : Group N] → [inst_1 : Group E] → [inst_2 : Group Q] → [inst_3 : TopologicalSpace N] → [inst_4 : TopologicalSpace E] → [inst_5 : TopologicalSpace Q] → [inst_6 : IsTopologicalGroup N] → [inst_7 : IsTopologicalGroup E] → [inst_8 : IsTopologicalGroup Q] → (toGroupExtension : GroupExtension N E Q) → TopologicalGroup.IsSES toGroupExtension.inl toGroupExtension.rightHom → ContinuousGroupExtension N E Q
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupExtension`; the structure fields and parameters are in the displayed signature and source declaration. Topological group extensions with the strong short-exact-sequence condition.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L30) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.toGroupExtension

Kind: `def`.

```lean
abbrev ContinuousGroupExtension.toGroupExtension {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (self : ContinuousGroupExtension N E Q) : GroupExtension N E Q
```

**Original catalogue explanation (not a Lean docstring):** Defines `toGroupExtension` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L33) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.isSES

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.isSES {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (self : ContinuousGroupExtension N E Q) : TopologicalGroup.IsSES self.inl self.rightHom
```

**Native source docstring:** The inclusion is a closed embedding, the projection is an open quotient
map, and their underlying homomorphisms are exact.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L40) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.mk'

Kind: `def`.

```lean
def ContinuousGroupExtension.mk' {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : GroupExtension N E Q) (hS : TopologicalGroup.IsSES S.inl S.rightHom) : ContinuousGroupExtension N E Q
```

**Native source docstring:** Construct a continuous group extension from an abstract extension and the
strong topological short-exactness witness.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L49) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.mk'_toGroupExtension

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.mk'_toGroupExtension {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : GroupExtension N E Q) (hS : TopologicalGroup.IsSES S.inl S.rightHom) : (mk' S hS).toGroupExtension = S
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mk'_toGroupExtension` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L57) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.inlContinuous

Kind: `def`.

```lean
def ContinuousGroupExtension.inlContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : N →ₜ* E
```

**Native source docstring:** The inclusion, bundled as a continuous homomorphism.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L62) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.inlContinuous_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.inlContinuous_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : N) : S.inlContinuous n = S.inl n
```

**Original catalogue explanation (not a Lean docstring):** The named computation `inlContinuous_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L67) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.rightHomContinuous

Kind: `def`.

```lean
def ContinuousGroupExtension.rightHomContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : E →ₜ* Q
```

**Native source docstring:** The projection, bundled as a continuous homomorphism.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L71) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.rightHomContinuous_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.rightHomContinuous_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : S.rightHomContinuous e = S.rightHom e
```

**Original catalogue explanation (not a Lean docstring):** The named computation `rightHomContinuous_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L76) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift

Kind: `def`.

```lean
def ContinuousGroupExtension.ulift {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : ContinuousGroupExtension (ULift.{uN', uN} N) (ULift.{uE', uE} E) (ULift.{uQ', uQ} Q)
```

**Native source docstring:** Raise the kernel, middle group, and quotient of a continuous extension
through independently chosen universes.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L80) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift_toGroupExtension

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ulift_toGroupExtension {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : S.ulift.toGroupExtension = S.ulift
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `ulift_toGroupExtension` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L88) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift_inl_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ulift_inl_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : ULift.{uN', uN} N) : S.ulift.inl n = { down := S.inl n.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_inl_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L93) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift_rightHom_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ulift_rightHom_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : ULift.{uE', uE} E) : S.ulift.rightHom e = { down := S.rightHom e.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_rightHom_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L98) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift_inlContinuous_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ulift_inlContinuous_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : ULift.{uN', uN} N) : S.ulift.inlContinuous n = { down := S.inl n.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_inlContinuous_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L103) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ulift_rightHomContinuous_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ulift_rightHomContinuous_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : ULift.{uE', uE} E) : S.ulift.rightHomContinuous e = { down := S.rightHom e.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_rightHomContinuous_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L108) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.commonUniverseUlift

Kind: `def`.

```lean
def ContinuousGroupExtension.commonUniverseUlift {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : ContinuousGroupExtension (ULift.{max uE uQ, uN} N) (ULift.{max uN uQ, uE} E) (ULift.{max uN uE, uQ} Q)
```

**Native source docstring:** The canonical common-universe lift of an independently universe-polymorphic
continuous extension.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L113) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.commonUniverseUlift_toGroupExtension

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.commonUniverseUlift_toGroupExtension {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : S.commonUniverseUlift.toGroupExtension = S.ulift
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `commonUniverseUlift_toGroupExtension` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L122) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.commonUniverseUlift_inl_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.commonUniverseUlift_inl_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : ULift.{max uE uQ, uN} N) : S.commonUniverseUlift.inl n = { down := S.inl n.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `commonUniverseUlift_inl_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L128) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.commonUniverseUlift_rightHom_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.commonUniverseUlift_rightHom_apply {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : ULift.{max uN uQ, uE} E) : S.commonUniverseUlift.rightHom e = { down := S.rightHom e.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `commonUniverseUlift_rightHom_apply` for topological group extensions with the strong short-exact-sequence condition; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L133) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv

Kind: `structure`.

```lean
structure ContinuousGroupExtension.Equiv {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] (S' : ContinuousGroupExtension N E' Q) extends E ≃ₜ* E' : Type (max uE uE')
```

**Native source docstring:** An equivalence of continuous extensions with fixed kernel and quotient.
The equivalence of middle groups is required to be a homeomorphism.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L138) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupExtension.Equiv.mk : {N : Type uN} → {E : Type uE} → {Q : Type uQ} → [inst : Group N] → [inst_1 : Group E] → [inst_2 : Group Q] → [inst_3 : TopologicalSpace N] → [inst_4 : TopologicalSpace E] → [inst_5 : TopologicalSpace Q] → [inst_6 : IsTopologicalGroup N] → [inst_7 : IsTopologicalGroup E] → [inst_8 : IsTopologicalGroup Q] → {S : ContinuousGroupExtension N E Q} → {E' : Type uE'} → [inst_9 : Group E'] → [inst_10 : TopologicalSpace E'] → [inst_11 : IsTopologicalGroup E'] → {S' : ContinuousGroupExtension N E' Q} → (toContinuousMulEquiv : E ≃ₜ* E') → ⇑toContinuousMulEquiv ∘ ⇑S.inl = ⇑S'.inl → ⇑S'.rightHom ∘ ⇑toContinuousMulEquiv = ⇑S.rightHom → S.Equiv S'
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupExtension.Equiv`; the structure fields and parameters are in the displayed signature and source declaration. Topological group extensions with the strong short-exact-sequence condition.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L138) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.toContinuousMulEquiv

Kind: `def`.

```lean
abbrev ContinuousGroupExtension.Equiv.toContinuousMulEquiv {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {S : ContinuousGroupExtension N E Q} {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S' : ContinuousGroupExtension N E' Q} (self : S.Equiv S') : E ≃ₜ* E'
```

**Original catalogue explanation (not a Lean docstring):** Defines `toContinuousMulEquiv` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L140) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.inl_comm

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.inl_comm {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {S : ContinuousGroupExtension N E Q} {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S' : ContinuousGroupExtension N E' Q} (self : S.Equiv S') : ⇑self.toContinuousMulEquiv ∘ ⇑S.inl = ⇑S'.inl
```

**Native source docstring:** Compatibility with the kernel inclusions.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L144) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.rightHom_comm

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.rightHom_comm {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {S : ContinuousGroupExtension N E Q} {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S' : ContinuousGroupExtension N E' Q} (self : S.Equiv S') : ⇑S'.rightHom ∘ ⇑self.toContinuousMulEquiv = ⇑S.rightHom
```

**Native source docstring:** Compatibility with the quotient projections.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L146) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.toGroupExtensionEquiv

Kind: `def`.

```lean
def ContinuousGroupExtension.Equiv.toGroupExtensionEquiv {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') : S.Equiv S'.toGroupExtension
```

**Native source docstring:** Forget topology from an equivalence of continuous extensions.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L154) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.instEquivLike

Kind: `instance`.

```lean
instance ContinuousGroupExtension.Equiv.instEquivLike {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} : EquivLike (S.Equiv S') E E'
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `EquivLike` instance in topological group extensions with the strong short-exact-sequence condition (native type names: `ContinuousGroupExtension.Equiv`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L161) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.instMulEquivClass

Kind: `instance`.

```lean
instance ContinuousGroupExtension.Equiv.instMulEquivClass {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} : MulEquivClass (S.Equiv S') E E'
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `MulEquivClass` instance in topological group extensions with the strong short-exact-sequence condition (native type names: `ContinuousGroupExtension.Equiv`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L172) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.instHomeomorphClass

Kind: `instance`.

```lean
instance ContinuousGroupExtension.Equiv.instHomeomorphClass {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} : HomeomorphClass (S.Equiv S') E E'
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `HomeomorphClass` instance in topological group extensions with the strong short-exact-sequence condition (native type names: `ContinuousGroupExtension.Equiv`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L175) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.map_inl

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.map_inl {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (n : N) : equiv (S.inl n) = S'.inl n
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `map_inl` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L179) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.rightHom_map

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.rightHom_map {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (e : E) : S'.rightHom (equiv e) = S.rightHom e
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `rightHom_map` in topological group extensions with the strong short-exact-sequence condition; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/ContinuousGroupExtension.lean#L184) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ContinuousGroupExtension.Equiv.instEquivLike`: `EquivLike`; type names: `ContinuousGroupExtension.Equiv`

- `ContinuousGroupExtension.Equiv.instHomeomorphClass`: `HomeomorphClass`; type names: `ContinuousGroupExtension.Equiv`

- `ContinuousGroupExtension.Equiv.instMulEquivClass`: `MulEquivClass`; type names: `ContinuousGroupExtension.Equiv`

### ContinuousGroupCohomology.Corestriction

76 native named entries; 4 native instance-table rows.

#### TopRep.jointlyContinuous_res

Kind: `instance`.

```lean
instance TopRep.jointlyContinuous_res {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (H : Subgroup G) (X : TopRep k G) [X.JointlyContinuous] : (res H.subtype X).JointlyContinuous
```

**Native source docstring:** Joint continuity is preserved when a representation is restricted to a subgroup.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L46) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.factor {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g : G) : ↥H
```

**Native source docstring:** The `H`-factor in the unique decomposition `t * g = η(t,g) * (t ⋆ g)`.
Its representative calculation is used in composition of transversals.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L63) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.next

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.next {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g : G) : ↑↑T
```

**Native source docstring:** The new transversal representative in `t * g = η(t,g) * (t ⋆ g)`.
Its representative calculation is used in composition of transversals.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L68) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor_mul_next

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.factor_mul_next {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g : G) : ↑(factor T t g) * ↑(next T t g) = ↑t * g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factor_mul_next` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L75) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.next_one

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.next_one {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) : next T t 1 = t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `next_one` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L80) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor_one

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.factor_one {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) : factor T t 1 = 1
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factor_one` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L86) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.equiv_mul

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.equiv_mul {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g g' : G) : ⋯.equiv (↑t * (g * g')) = (factor T t g * factor T (next T t g) g', next T (next T t g) g')
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `equiv_mul` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L91) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor_mul

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.factor_mul {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g g' : G) : factor T t (g * g') = factor T t g * factor T (next T t g) g'
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factor_mul` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L98) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.next_mul

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.next_mul {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g g' : G) : next T t (g * g') = next T (next T t g) g'
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `next_mul` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L103) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.inv_mul_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.inv_mul_factor {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (t : ↑↑T) (g : G) : (↑t)⁻¹ * ↑(factor T t g) = g * (↑(next T t g))⁻¹
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `inv_mul_factor` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L110) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.nextEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.nextEquiv {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (g : G) : ↑↑T ≃ ↑↑T
```

**Native source docstring:** Right multiplication permutes the chosen right-transversal representatives.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L120) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.continuous_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.continuous_factor {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : OpenSubgroup G) (T : (↑H).RightTransversal) (t : ↑↑T) : Continuous (factor T t)
```

**Native source docstring:** Openness of the subgroup makes the transversal factor locally continuous.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L132) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeFactor

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.changeFactor {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) : ↥H
```

**Native source docstring:** The subgroup correction matching a representative in `T` with one in `S`.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L155) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeRep

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.changeRep {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) : ↑↑S
```

**Native source docstring:** The representative in `S` of the same right coset as a representative in `T`.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L159) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeFactor_mul_changeRep

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.changeFactor_mul_changeRep {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) : ↑(changeFactor T S t) * ↑(changeRep T S t) = ↑t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `changeFactor_mul_changeRep` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L164) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeRep_rightCoset

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.changeRep_rightCoset {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) : RightCosetEquivalence ↑H ↑(changeRep T S t) ↑t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `changeRep_rightCoset` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L169) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeRepEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.changeRepEquiv {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) : ↑↑T ≃ ↑↑S
```

**Native source docstring:** Matching representatives of two right transversals gives an equivalence.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L176) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeRep_next

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.changeRep_next {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) (g : G) : changeRep T S (next T t g) = next S (changeRep T S t) g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `changeRep_next` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L196) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factor_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.factor_change {G : Type v} [Group G] {H : Subgroup G} (T S : H.RightTransversal) (t : ↑↑T) (g : G) : factor T t g = changeFactor T S t * factor S (changeRep T S t) g * (changeFactor T S (next T t g))⁻¹
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factor_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L218) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.factorC

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.factorC {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : OpenSubgroup G) (T : (↑H).RightTransversal) (t : ↑↑T) : C(G, ↥H)
```

**Native source docstring:** The subgroup factor as a continuous map.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L248) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossed_one

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossed_one {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {H : Subgroup G} (X : TopRep k G) (f : ↥(continuousCrossedHom (TopRep.res H.subtype X))) : ↑f 1 = 0
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossed_one` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L256) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossed_inv

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossed_inv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {H : Subgroup G} (X : TopRep k G) (f : ↥(continuousCrossedHom (TopRep.res H.subtype X))) (a : ↥H) : ↑f a⁻¹ = -(X.ρ (↑a)⁻¹) (↑f a)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossed_inv` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L262) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.rho_mul_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.rho_mul_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (X : TopRep k G) (a b : G) (x : ↑X) : (X.ρ a) ((X.ρ b) x) = (X.ρ (a * b)) x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `rho_mul_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L270) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.rho_inv_changeFactor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.rho_inv_changeFactor {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (X : TopRep k G) (S : H.RightTransversal) (t : ↑↑T) (x : ↑X) : (X.ρ (↑t)⁻¹) ((X.ρ ↑(changeFactor T S t)) x) = (X.ρ (↑(changeRep T S t))⁻¹) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `rho_inv_changeFactor` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L277) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transversalFintype

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transversalFintype {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) : Fintype ↑↑T
```

**Original catalogue explanation (not a Lean docstring):** Defines `transversalFintype` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L285) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.changeCoefficient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.changeCoefficient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : ↑X
```

**Native source docstring:** The coefficient measuring the change from `T` to `S`.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L290) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.rho_inv_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.rho_inv_factor {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {H : Subgroup G} (X : TopRep k G) (T : H.RightTransversal) (t : ↑↑T) (g : G) (x : ↑X) : (X.ρ (↑t)⁻¹) ((X.ρ ↑(factor T t g)) x) = (X.ρ g) ((X.ρ (↑(next T t g))⁻¹) x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `rho_inv_factor` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L298) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.rho_factor_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.rho_factor_change {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {H : Subgroup G} (T : H.RightTransversal) (X : TopRep k G) (S : H.RightTransversal) (t : ↑↑T) (g : G) (x : ↑X) : (X.ρ (↑t)⁻¹) ((X.ρ ↑(changeFactor T S t * factor S (changeRep T S t) g)) ((X.ρ (↑(changeFactor T S (next T t g)))⁻¹) x)) = (X.ρ g) ((X.ρ (↑(next T t g))⁻¹) x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `rho_factor_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L311) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transfer_term_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transfer_term_change {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {H : Subgroup G} (T : H.RightTransversal) (X : TopRep k G) (S : H.RightTransversal) (t : ↑↑T) (f : ↥(continuousCrossedHom (TopRep.res H.subtype X))) (g : G) : (X.ρ (↑t)⁻¹) (↑f (factor T t g)) = (X.ρ (↑(changeRep T S t))⁻¹) (↑f (factor S (changeRep T S t) g)) + (X.ρ (↑t)⁻¹) (↑f (changeFactor T S t)) - (X.ρ g) ((X.ρ (↑(next T t g))⁻¹) (↑f (changeFactor T S (next T t g))))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transfer_term_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L329) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferTerm

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transferTerm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) (T : (↑H).RightTransversal) (t : ↑↑T) : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) →L[k] C(G, ↑X)
```

**Native source docstring:** The contribution of one transversal representative to transfer.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L357) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferRaw

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transferRaw {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) →L[k] C(G, ↑X)
```

**Native source docstring:** The finite-coordinate transfer formula, before verifying the crossed identity.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L366) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferRaw_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferRaw_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (g : G) : ((transferRaw X H T) f) g = ∑ t : ↑↑T, (X.ρ (↑t)⁻¹) (↑f (factor T t g))
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transferRaw_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L372) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferRaw_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferRaw_change {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (g : G) : ((transferRaw X H T) f) g = ((transferRaw X H S) f) g + changeCoefficient X H T S f - (X.ρ g) (changeCoefficient X H T S f)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferRaw_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L383) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferRaw_crossed

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferRaw_crossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (g g' : G) : ((transferRaw X H T) f) (g * g') = (X.ρ g) (((transferRaw X H T) f) g') + ((transferRaw X H T) f) g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferRaw_crossed` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L441) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transferCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) →L[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** Transfer on continuous crossed homomorphisms for a fixed right transversal.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L490) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (g : G) : ↑((transferCrossed X H T) f) g = ∑ t : ↑↑T, (X.ρ (↑t)⁻¹) (↑f (factor T t g))
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transferCrossed_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L497) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {Y : TopRep k G} (q : X ⟶ Y) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (crossedMap q) ((transferCrossed X H T) f) = (transferCrossed Y H T) ((crossedMap ((TopRep.resFunctor (↑H).subtype).map q)) f)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferCrossed_natural` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L504) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_change {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (transferCrossed X H T) f = (transferCrossed X H S) f - (principalToCrossed X) (changeCoefficient X H T S f)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferCrossed_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L518) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCoefficient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transferCoefficient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) : ↑X →L[k] ↑X
```

**Native source docstring:** The coefficient trace associated to the chosen transversal.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L532) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCoefficient_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCoefficient_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (x : ↑X) : (transferCoefficient X H T) x = ∑ t : ↑↑T, (X.ρ (↑t)⁻¹) x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transferCoefficient_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L538) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_principal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_principal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] (x : ↑X) : (transferCrossed X H T) ((principalToCrossed (TopRep.res (↑H).subtype X)) x) = (principalToCrossed X) ((transferCoefficient X H T) x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferCrossed_principal` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L545) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.transferQuotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom X) ⧸ principalCocycles X
```

**Native source docstring:** Transfer descends continuously through principal cocycles.
Its lift computes on representatives in the transitivity comparison.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L577) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transfer_mkQL_change

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transfer_mkQL_change {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (principalCocycles X).mkQL ((transferCrossed X H T) f) = (principalCocycles X).mkQL ((transferCrossed X H S) f)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transfer_mkQL_change` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L597) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_eq

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_eq {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) [X.JointlyContinuous] : transferQuotient X H T = transferQuotient X H S
```

**Native source docstring:** Transfer on the quotient is independent of the chosen right transversal.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L612) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {Y : TopRep k G} (q : X ⟶ Y) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [Y.JointlyContinuous] : crossedQuotientMap q ∘SL transferQuotient X H T = transferQuotient Y H T ∘SL crossedQuotientMap ((TopRep.resFunctor (↑H).subtype).map q)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferQuotient_natural` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L625) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural_hom

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural_hom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {Y : TopRep k G} (q : X ⟶ Y) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [Y.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient X H T)) (TopModuleCat.ofHom (crossedQuotientMap q)) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap ((TopRep.resFunctor (↑H).subtype).map q))) (TopModuleCat.ofHom (transferQuotient Y H T))
```

**Native source docstring:** The categorical form of coefficient naturality for fixed-transversal
transfer on crossed-homomorphism quotients.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L642) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural_hom_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_natural_hom_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {Y : TopRep k G} (q : X ⟶ Y) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [Y.JointlyContinuous] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom Y) ⧸ principalCocycles Y) ⟶ Z) : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient X H T)) (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap q)) h) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap (TopRep.ofHom (ContIntertwiningMap.restrict (↑H).subtype (TopRep.Hom.hom q))))) (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient Y H T)) h)
```

**Native source docstring:** The categorical form of coefficient naturality for fixed-transversal
transfer on crossed-homomorphism quotients.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L644) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : continuousCohomology 1 (TopRep.res (↑H).subtype X) ⟶ continuousCohomology 1 X
```

**Native source docstring:** The degree-one corestriction morphism determined by a right transversal.
Its crossed-quotient formula is used by the composition and Mackey laws.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L657) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal_eq

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOneWithTransversal_eq {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T S : (↑H).RightTransversal) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : corestrictionOneWithTransversal X H T = corestrictionOneWithTransversal X H S
```

**Native source docstring:** Degree-one corestriction is independent of the chosen right transversal.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L669) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.corestrictionOne {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : continuousCohomology 1 (TopRep.res (↑H).subtype X) ⟶ continuousCohomology 1 X
```

**Native source docstring:** Canonical degree-one corestriction for an open finite-index subgroup.
Its default-transversal formula is used by the Mackey comparison.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L679) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_eq_withTransversal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_eq_withTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : corestrictionOne X H = corestrictionOneWithTransversal X H T
```

**Native source docstring:** The canonical map may be computed using any chosen right transversal.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L688) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) {Y : TopRep k G} (q : X ⟶ Y) (H : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [Y.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : CategoryTheory.CategoryStruct.comp (map (ContinuousMonoidHom.id ↥↑H) ((TopRep.resFunctor (↑H).subtype).map q) 1) (corestrictionOne Y H) = CategoryTheory.CategoryStruct.comp (corestrictionOne X H) (map (ContinuousMonoidHom.id G) q 1)
```

**Native source docstring:** Canonical degree-one corestriction commutes with coefficient morphisms.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L697) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedRestrict

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.crossedRestrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) : ↥(continuousCrossedHom X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))
```

**Native source docstring:** Restriction of continuous crossed homomorphisms to an open subgroup.
Its value on subgroup elements is computed by evaluation in the ambient group.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L711) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedRestrict_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedRestrict_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (f : ↥(continuousCrossedHom X)) (h : ↥H) : ↑((crossedRestrict X H) f) h = ↑f ↑h
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedRestrict_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L725) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedRestrict_principal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedRestrict_principal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] (x : ↑X) : (crossedRestrict X H) ((principalToCrossed X) x) = (principalToCrossed (TopRep.res (↑H).subtype X)) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedRestrict_principal` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L731) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] : ↥(continuousCrossedHom X) ⧸ principalCocycles X →L[k] ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X)
```

**Native source docstring:** Restriction descends to continuous crossed homomorphisms modulo principal
cocycles. Its application computes on quotient representatives.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L738) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] (f : ↥(continuousCrossedHom X)) : (crossedQuotientRestrict X H) ((principalCocycles X).mkQ f) = (principalCocycles (TopRep.res (↑H).subtype X)).mkQ ((crossedRestrict X H) f)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedQuotientRestrict_mk` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L760) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupInclusion

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.openSubgroupInclusion {G : Type v} [Group G] [TopologicalSpace G] (H : OpenSubgroup G) : ↥H →ₜ* G
```

**Native source docstring:** The continuous inclusion of an open subgroup.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L767) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.restrictionCoeffHom

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.restrictionCoeffHom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) : TopRep.res (↑(openSubgroupInclusion H)) X ⟶ TopRep.res (↑H).subtype X
```

**Native source docstring:** The identity coefficient map comparing restriction along the continuous
inclusion with the representation restricted along the underlying subgroup
inclusion.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L772) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedRestrict_comp_mkQL

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedRestrict_comp_mkQL {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedRestrict X H)) (TopModuleCat.ofHom (principalCocycles (TopRep.res (↑H).subtype X)).mkQL) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (principalCocycles X).mkQL) (TopModuleCat.ofHom (crossedQuotientRestrict X H))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedRestrict_comp_mkQL` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L783) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupIsTopologicalGroup

Kind: `instance`.

```lean
instance ContinuousCohomology.CorestrictionTransversal.openSubgroupIsTopologicalGroup {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : OpenSubgroup G) : IsTopologicalGroup ↥H
```

**Native source docstring:** An open subgroup inherits the ambient topological-group structure.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L793) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_restrict

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_restrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : CategoryTheory.CategoryStruct.comp (cocyclesMap (openSubgroupInclusion H) (restrictionCoeffHom X H) 1) (cocyclesOneCrossedIso (TopRep.res (↑H).subtype X)).hom = CategoryTheory.CategoryStruct.comp (cocyclesOneCrossedIso X).hom (TopModuleCat.ofHom (crossedRestrict X H))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `cocyclesOneCrossedIso_restrict` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L800) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : CategoryTheory.CategoryStruct.comp (map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1) (homologyQuotientIso (TopRep.res (↑H).subtype X)).hom = CategoryTheory.CategoryStruct.comp (homologyQuotientIso X).hom (TopModuleCat.ofHom (crossedQuotientRestrict X H))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `homologyQuotientIso_restrict` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L822) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X)) ⟶ Z) : CategoryTheory.CategoryStruct.comp (map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1) (CategoryTheory.CategoryStruct.comp (homologyQuotientIso (TopRep.res (↑H).subtype X)).hom h) = CategoryTheory.CategoryStruct.comp (homologyQuotientIso X).hom (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientRestrict X H)) h)
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated reassociated statement associated with `ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_restrict` in transfer in continuous degree-one cohomology for open finite-index subgroups; the original `@[reassoc]` source anchor is shown below.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L822) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.degreeOneIso_restrict

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.degreeOneIso_restrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientRestrict X H)) (degreeOneIso (TopRep.res (↑H).subtype X)).hom = CategoryTheory.CategoryStruct.comp (degreeOneIso X).hom (map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1)
```

**Native source docstring:** The crossed-homomorphism restriction map agrees with mathlib's native
continuous-cohomology restriction in degree one.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L839) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transfer_restrict_term

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transfer_restrict_term {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom X)) (t : ↑↑T) (g : G) : (X.ρ (↑t)⁻¹) (↑f ↑(factor T t g)) = ↑f g + (X.ρ (↑t)⁻¹) (↑f ↑t) - (X.ρ g) ((X.ρ (↑(next T t g))⁻¹) (↑f ↑(next T t g)))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transfer_restrict_term` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L856) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.restrictionTransferCoefficient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.restrictionTransferCoefficient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom X)) : ↑X
```

**Native source docstring:** The coefficient of the principal cocycle appearing when transfer is
applied to a restricted crossed homomorphism.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L875) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) (f : ↥(continuousCrossedHom X)) (g : G) : ↑((transferCrossed X H T) ((crossedRestrict X H) f)) g = (↑H).index • ↑f g + restrictionTransferCoefficient X H T f - (X.ρ g) (restrictionTransferCoefficient X H T f)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `transferCrossed_restrict_apply` for transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L882) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_restrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom X)) : (transferCrossed X H T) ((crossedRestrict X H) f) = (↑H).index • f - (principalToCrossed X) (restrictionTransferCoefficient X H T f)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferCrossed_restrict` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L929) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] : transferQuotient X H T ∘SL crossedQuotientRestrict X H = (↑H).index • ContinuousLinearMap.id k (↥(continuousCrossedHom X) ⧸ principalCocycles X)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferQuotient_comp_restrict` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L945) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientRestrict X H)) (TopModuleCat.ofHom (transferQuotient X H T)) = (↑H).index • CategoryTheory.CategoryStruct.id ↧(↥(continuousCrossedHom X) ⧸ principalCocycles X)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transferQuotient_comp_restrict_hom` in transfer in continuous degree-one cohomology for open finite-index subgroups; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L967) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom X) ⧸ principalCocycles X) ⟶ Z) : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientRestrict X H)) (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient X H T)) h) = CategoryTheory.CategoryStruct.comp ((↑H).index • CategoryTheory.CategoryStruct.id ↧(↥(continuousCrossedHom X) ⧸ principalCocycles X)) h
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated reassociated statement associated with `ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_restrict_hom` in transfer in continuous degree-one cohomology for open finite-index subgroups; the original `@[reassoc]` source anchor is shown below.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L967) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.restriction_corestrictionOne

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.restriction_corestrictionOne {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H : OpenSubgroup G) [(↑H).FiniteIndex] (T : (↑H).RightTransversal) [X.JointlyContinuous] [LocallyCompactSpace G] [LocallyCompactSpace ↥H] : CategoryTheory.CategoryStruct.comp (map (openSubgroupInclusion H) (restrictionCoeffHom X H) 1) (corestrictionOne X H) = (↑H).index • CategoryTheory.CategoryStruct.id (continuousCohomology 1 X)
```

**Native source docstring:** Restriction followed by degree-one corestriction is multiplication by the
subgroup index.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L979) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupTopFiniteIndex

Kind: `instance`.

```lean
instance ContinuousCohomology.CorestrictionTransversal.openSubgroupTopFiniteIndex {G : Type v} [Group G] [TopologicalSpace G] : (↑⊤).FiniteIndex
```

**Native source docstring:** The top open subgroup has finite index.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L996) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupTopLocallyCompact

Kind: `instance`.

```lean
instance ContinuousCohomology.CorestrictionTransversal.openSubgroupTopLocallyCompact {G : Type v} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] : LocallyCompactSpace ↥⊤
```

**Native source docstring:** The top open subgroup of a locally compact group is locally compact.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L1002) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_top

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_top {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (map (openSubgroupInclusion ⊤) (restrictionCoeffHom X ⊤) 1) (corestrictionOne X ⊤) = CategoryTheory.CategoryStruct.id (continuousCohomology 1 X)
```

**Native source docstring:** Corestriction from the whole group is the identity after the canonical
restriction identification between `G` and its top open subgroup.

[Source](../ContinuousGroupCohomology/Corestriction.lean#L1007) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ContinuousCohomology.CorestrictionTransversal.openSubgroupIsTopologicalGroup`: `IsTopologicalGroup`; type names: `Subtype`

- `ContinuousCohomology.CorestrictionTransversal.openSubgroupTopFiniteIndex`: `Subgroup.FiniteIndex`; type names: `OpenSubgroup.toSubgroup`

- `ContinuousCohomology.CorestrictionTransversal.openSubgroupTopLocallyCompact`: `LocallyCompactSpace`; type names: `Subtype`

- `TopRep.jointlyContinuous_res`: `TopRep.JointlyContinuous`; type names: `TopRep.res`

### ContinuousGroupCohomology.DegreeOne

47 native named entries; 0 native instance-table rows.

#### ContinuousCohomology.continuousCrossedHom

Kind: `def`.

```lean
def ContinuousCohomology.continuousCrossedHom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) : Submodule k C(G, ↑X)
```

**Native source docstring:** Continuous additive crossed homomorphisms for the action carried by `X`.
The defining relation is needed to construct functorial crossed maps.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L38) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.principalMap

Kind: `def`.

```lean
def ContinuousCohomology.principalMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : ↑X →ₗ[k] C(G, ↑X)
```

**Native source docstring:** The continuous principal crossed homomorphism attached to a coefficient.
Its orbit-map formula is needed by the continuous principal-cocycle comparison.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L54) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.principalToCrossed

Kind: `def`.

```lean
def ContinuousCohomology.principalToCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : ↑X →ₗ[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** Principal crossed homomorphisms, regarded inside all continuous crossed homomorphisms.
The underlying map is used to establish continuity of `principalToCrossedL`.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L72) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.principalCocycles

Kind: `def`.

```lean
def ContinuousCohomology.principalCocycles {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : Submodule k ↥(continuousCrossedHom X)
```

**Native source docstring:** The submodule of principal continuous crossed homomorphisms.
Its range presentation reduces when comparing quotient maps.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L94) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap

Kind: `def`.

```lean
def ContinuousCohomology.crossedMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) : ↥(continuousCrossedHom A) →L[k] ↥(continuousCrossedHom B)
```

**Native source docstring:** A coefficient morphism sends continuous crossed homomorphisms forward.
Its application to a cocycle computes pointwise in external clients.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L103) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedMap_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) (f : ↥(continuousCrossedHom A)) (g : G) : ↑((crossedMap q) f) g = (CategoryTheory.ConcreteCategory.hom q) (↑f g)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedMap_apply` for crossed degree-one cocycles, principal cocycles and homology quotients; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L115) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap_principal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedMap_principal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] (x : ↑A) : (crossedMap q) ((principalToCrossed A) x) = (principalToCrossed B) ((CategoryTheory.ConcreteCategory.hom q) x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedMap_principal` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L120) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedQuotientMap

Kind: `def`.

```lean
def ContinuousCohomology.crossedQuotientMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] : ↥(continuousCrossedHom A) ⧸ principalCocycles A →L[k] ↥(continuousCrossedHom B) ⧸ principalCocycles B
```

**Native source docstring:** A coefficient morphism descends to continuous crossed homomorphisms modulo principals.
Its lift computes on quotient representatives.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L127) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedQuotientMap_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedQuotientMap_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] (f : ↥(continuousCrossedHom A)) : (crossedQuotientMap q) ((principalCocycles A).mkQ f) = (principalCocycles B).mkQ ((crossedMap q) f)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `crossedQuotientMap_mk` for crossed degree-one cocycles, principal cocycles and homology quotients; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L145) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap_id

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedMap_id {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A : TopRep k G} : crossedMap (CategoryTheory.CategoryStruct.id A) = ContinuousLinearMap.id k ↥(continuousCrossedHom A)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `crossedMap_id` for crossed degree-one cocycles, principal cocycles and homology quotients; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L152) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap_comp

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedMap_comp {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B C : TopRep k G} (q : A ⟶ B) (r : B ⟶ C) : crossedMap (CategoryTheory.CategoryStruct.comp q r) = crossedMap r ∘SL crossedMap q
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `crossedMap_comp` for crossed degree-one cocycles, principal cocycles and homology quotients; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L157) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedQuotientMap_id

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedQuotientMap_id {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A : TopRep k G} [A.JointlyContinuous] : crossedQuotientMap (CategoryTheory.CategoryStruct.id A) = ContinuousLinearMap.id k (↥(continuousCrossedHom A) ⧸ principalCocycles A)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `crossedQuotientMap_id` for crossed degree-one cocycles, principal cocycles and homology quotients; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L163) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedQuotientMap_comp

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedQuotientMap_comp {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B C : TopRep k G} (q : A ⟶ B) (r : B ⟶ C) [A.JointlyContinuous] [B.JointlyContinuous] [C.JointlyContinuous] : crossedQuotientMap (CategoryTheory.CategoryStruct.comp q r) = crossedQuotientMap r ∘SL crossedQuotientMap q
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `crossedQuotientMap_comp` for crossed degree-one cocycles, principal cocycles and homology quotients; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L172) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.orbitMap

Kind: `def`.

```lean
def ContinuousCohomology.orbitMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : ↑X →L[k] C(G, ↑X)
```

**Native source docstring:** The orbit map of a coefficient, regarded as a continuous map on the group.
Its pointwise action formula identifies continuous principal cocycles.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L183) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cochainsZeroEquiv

Kind: `def`.

```lean
def ContinuousCohomology.cochainsZeroEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] : ↑(X.homogeneousCochains.X 0).toModuleCat ≃L[k] ↑X
```

**Native source docstring:** Evaluation at the identity identifies homogeneous degree-zero cochains
with their coefficient representation when the represented action is jointly
continuous.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L196) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homogeneousOne

Kind: `def`.

```lean
def ContinuousCohomology.homogeneousOne {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] (f : ↥(continuousCrossedHom X)) : C(G, C(G, ↑X))
```

**Native source docstring:** The homogeneous degree-one cochain associated to a continuous crossed
homomorphism.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L229) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homogeneousOne_mem_invariants

Kind: `theorem`.

```lean
theorem ContinuousCohomology.homogeneousOne_mem_invariants {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] (f : ↥(continuousCrossedHom X)) : homogeneousOne X f ∈ (X.resolution'.X 1).ρ.invariants
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `homogeneousOne_mem_invariants` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L239) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homogeneousOne_mem_ker

Kind: `theorem`.

```lean
theorem ContinuousCohomology.homogeneousOne_mem_ker {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] (f : ↥(continuousCrossedHom X)) : ⟨homogeneousOne X f, ⋯⟩ ∈ (↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `homogeneousOne_mem_ker` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L257) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.oneKer_isCrossed

Kind: `theorem`.

```lean
theorem ContinuousCohomology.oneKer_isCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (σ : ↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker) (g h : G) : (↑↑σ 1) (g * h) = (X.ρ g) ((↑↑σ 1) h) + (↑↑σ 1) g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `oneKer_isCrossed` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L284) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.oneKerToCrossed

Kind: `def`.

```lean
def ContinuousCohomology.oneKerToCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : ↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker →ₗ[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** Evaluation at `(1, ·)` sends homogeneous degree-one cocycles to continuous
crossed homomorphisms.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L300) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedToOneKer

Kind: `def`.

```lean
def ContinuousCohomology.crossedToOneKer {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] : ↥(continuousCrossedHom X) →ₗ[k] ↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker
```

**Native source docstring:** A continuous crossed homomorphism, regarded as a homogeneous degree-one
cocycle.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L308) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.oneKerLinearEquiv

Kind: `def`.

```lean
def ContinuousCohomology.oneKerLinearEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] : ↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker ≃ₗ[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** Algebraically, homogeneous degree-one cocycles are continuous crossed
homomorphisms.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L332) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.continuous_homogeneousOne

Kind: `theorem`.

```lean
theorem ContinuousCohomology.continuous_homogeneousOne {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : Continuous fun (f : ↥(continuousCrossedHom X)) => homogeneousOne X f
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `continuous_homogeneousOne` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L355) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.oneKerEquiv

Kind: `def`.

```lean
def ContinuousCohomology.oneKerEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : ↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker ≃L[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** For a locally compact group, homogeneous degree-one cocycles and continuous
crossed homomorphisms are continuously linearly equivalent.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L367) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cochainsZeroIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.cochainsZeroIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] : X.homogeneousCochains.X 0 ≅ ↧↑X
```

**Original catalogue explanation (not a Lean docstring):** Defines `cochainsZeroIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L377) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.oneKerCrossedIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.oneKerCrossedIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : ↧↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker ≅ ↧↥(continuousCrossedHom X)
```

**Original catalogue explanation (not a Lean docstring):** Defines `oneKerCrossedIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L381) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.principalToCrossedL

Kind: `def`.

```lean
def ContinuousCohomology.principalToCrossedL {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : ↑X →L[k] ↥(continuousCrossedHom X)
```

**Native source docstring:** The principal-cocycle map as a continuous linear map.
Its underlying linear map reduces to `principalToCrossed`.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L387) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.principalToCrossedL_toLinearMap

Kind: `theorem`.

```lean
theorem ContinuousCohomology.principalToCrossedL_toLinearMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : ↑(principalToCrossedL X) = principalToCrossed X
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `principalToCrossedL_toLinearMap` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L397) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.crossedMap_comp_mkQL

Kind: `theorem`.

```lean
theorem ContinuousCohomology.crossedMap_comp_mkQL {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedMap q)) (TopModuleCat.ofHom (principalCocycles B).mkQL) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (principalCocycles A).mkQL) (TopModuleCat.ofHom (crossedQuotientMap q))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `crossedMap_comp_mkQL` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L401) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cocyclesOneIso

Kind: `def`.

```lean
noncomputable abbrev ContinuousCohomology.cocyclesOneIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : cocycles X 1 ≅ ↧↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker
```

**Native source docstring:** The abstract degree-one cocycles of the homogeneous complex, identified
with the explicit kernel of its degree-one differential.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L410) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cocyclesOneCrossedIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.cocyclesOneCrossedIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : cocycles X 1 ≅ ↧↥(continuousCrossedHom X)
```

**Native source docstring:** Degree-one homogeneous cocycles and continuous crossed homomorphisms as
topological modules.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L418) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.boundaryToOneKer

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.boundaryToOneKer {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : X.homogeneousCochains.X 0 ⟶ ↧↥(↑(TopModuleCat.Hom.hom (X.homogeneousCochains.d 1 2))).ker
```

**Native source docstring:** The degree-zero differential, with codomain restricted to the explicit
kernel of the degree-one differential.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L424) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cocyclesOneIso_hom_comp_kerι

Kind: `theorem`.

```lean
theorem ContinuousCohomology.cocyclesOneIso_hom_comp_kerι {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : CategoryTheory.CategoryStruct.comp (cocyclesOneIso X).hom (TopModuleCat.kerι (X.homogeneousCochains.d 1 2)) = HomologicalComplex.iCycles X.homogeneousCochains 1
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `cocyclesOneIso_hom_comp_kerι` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L436) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cocyclesOneCrossedIso_hom_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.cocyclesOneCrossedIso_hom_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] (σ : ↑(cocycles X 1).toModuleCat) (g : G) : ↑((CategoryTheory.ConcreteCategory.hom (cocyclesOneCrossedIso X).hom) σ) g = (↑((CategoryTheory.ConcreteCategory.hom (HomologicalComplex.iCycles X.homogeneousCochains 1)) σ) 1) g
```

**Original catalogue explanation (not a Lean docstring):** The named computation `cocyclesOneCrossedIso_hom_apply` for crossed degree-one cocycles, principal cocycles and homology quotients; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L442) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.cocyclesOneCrossedIso_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.cocyclesOneCrossedIso_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (cocyclesMap (ContinuousMonoidHom.id G) q 1) (cocyclesOneCrossedIso B).hom = CategoryTheory.CategoryStruct.comp (cocyclesOneCrossedIso A).hom (TopModuleCat.ofHom (crossedMap q))
```

**Native source docstring:** The identification of homogeneous one-cocycles with continuous crossed
homomorphisms commutes with coefficient morphisms.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L450) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.toCycles_comp_cocyclesOneIso

Kind: `theorem`.

```lean
theorem ContinuousCohomology.toCycles_comp_cocyclesOneIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.toCycles X.homogeneousCochains 0 1) (cocyclesOneIso X).hom = boundaryToOneKer X
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `toCycles_comp_cocyclesOneIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L465) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.boundaryToOneKer_comm

Kind: `theorem`.

```lean
theorem ContinuousCohomology.boundaryToOneKer_comm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (boundaryToOneKer X) (oneKerCrossedIso X).hom = CategoryTheory.CategoryStruct.comp (cochainsZeroIso X).hom (TopModuleCat.ofHom (principalToCrossedL X))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `boundaryToOneKer_comm` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L473) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.toCycles_comp_cocyclesOneCrossedIso

Kind: `theorem`.

```lean
theorem ContinuousCohomology.toCycles_comp_cocyclesOneCrossedIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (HomologicalComplex.toCycles X.homogeneousCochains 0 1) (cocyclesOneCrossedIso X).hom = CategoryTheory.CategoryStruct.comp (cochainsZeroIso X).hom (TopModuleCat.ofHom (principalToCrossedL X))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `toCycles_comp_cocyclesOneCrossedIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L484) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.boundaryArrowIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.boundaryArrowIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.Arrow.mk (HomologicalComplex.toCycles X.homogeneousCochains 0 1) ≅ CategoryTheory.Arrow.mk (TopModuleCat.ofHom (principalToCrossedL X))
```

**Original catalogue explanation (not a Lean docstring):** Defines `boundaryArrowIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L491) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homologyQuotientIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.homologyQuotientIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : continuousCohomology 1 X ≅ ↧(↥(continuousCrossedHom X) ⧸ principalCocycles X)
```

**Native source docstring:** The first continuous cohomology object, identified with the quotient of
continuous crossed homomorphisms by principal cocycles. The canonical inverse
computes in the corestriction comparison.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L498) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.π_comp_homologyQuotientIso

Kind: `theorem`.

```lean
theorem ContinuousCohomology.π_comp_homologyQuotientIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (π X 1) (homologyQuotientIso X).hom = CategoryTheory.CategoryStruct.comp (cocyclesOneCrossedIso X).hom (TopModuleCat.ofHom (principalCocycles X).mkQL)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `π_comp_homologyQuotientIso` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L512) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homologyQuotientIso_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.homologyQuotientIso_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (map (ContinuousMonoidHom.id G) q 1) (homologyQuotientIso B).hom = CategoryTheory.CategoryStruct.comp (homologyQuotientIso A).hom (TopModuleCat.ofHom (crossedQuotientMap q))
```

**Native source docstring:** The degree-one cohomology-to-crossed-quotient identification commutes with
mathlib's native coefficient map.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L526) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.homologyQuotientIso_natural_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.homologyQuotientIso_natural_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] [LocallyCompactSpace G] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom B) ⧸ principalCocycles B) ⟶ Z) : CategoryTheory.CategoryStruct.comp (map (ContinuousMonoidHom.id G) q 1) (CategoryTheory.CategoryStruct.comp (homologyQuotientIso B).hom h) = CategoryTheory.CategoryStruct.comp (homologyQuotientIso A).hom (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap q)) h)
```

**Native source docstring:** The degree-one cohomology-to-crossed-quotient identification commutes with
mathlib's native coefficient map.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L528) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.degreeOneIso

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.degreeOneIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : ↧(↥(continuousCrossedHom X) ⧸ principalCocycles X) ≅ continuousCohomology 1 X
```

**Native source docstring:** Continuous crossed homomorphisms modulo principal cocycles compute first
continuous cohomology. Its inverse computes as `homologyQuotientIso`.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L539) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.degreeOneIso_inv

Kind: `theorem`.

```lean
theorem ContinuousCohomology.degreeOneIso_inv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : (degreeOneIso X).inv = (homologyQuotientIso X).hom
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `degreeOneIso_inv` in crossed degree-one cocycles, principal cocycles and homology quotients; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L547) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.degreeOneIso_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.degreeOneIso_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap q)) (degreeOneIso B).hom = CategoryTheory.CategoryStruct.comp (degreeOneIso A).hom (map (ContinuousMonoidHom.id G) q 1)
```

**Native source docstring:** The crossed-quotient-to-degree-one-cohomology identification commutes with
mathlib's native coefficient map.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L551) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.degreeOneIso_natural_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.degreeOneIso_natural_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B : TopRep k G} (q : A ⟶ B) [A.JointlyContinuous] [B.JointlyContinuous] [LocallyCompactSpace G] {Z : TopModuleCat k} (h : continuousCohomology 1 B ⟶ Z) : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientMap q)) (CategoryTheory.CategoryStruct.comp (degreeOneIso B).hom h) = CategoryTheory.CategoryStruct.comp (degreeOneIso A).hom (CategoryTheory.CategoryStruct.comp (map (ContinuousMonoidHom.id G) q 1) h)
```

**Native source docstring:** The crossed-quotient-to-degree-one-cohomology identification commutes with
mathlib's native coefficient map.

[Source](../ContinuousGroupCohomology/DegreeOne.lean#L553) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.FiniteCoinvariants

24 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.finiteOrbitDifference

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteOrbitDifference {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) : (Fin (Fintype.card H) → M) →ₗ[R] M
```

**Native source docstring:** The finite orbit-difference map
`(x_g)_g ↦ ∑ g, (g x_g - x_g)`.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L41) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifference_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteOrbitDifference_apply {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) (x : Fin (Fintype.card H) → M) : (finiteOrbitDifference ρ) x = ∑ i : Fin (Fintype.card H), ((ρ ((Fintype.equivFin H).symm i)) (x i) - x i)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteOrbitDifference_apply` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L56) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifference_single

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteOrbitDifference_single {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) (g : H) (x : M) : (finiteOrbitDifference ρ) (Pi.single ((Fintype.equivFin H) g) x) = (ρ g) x - x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `finiteOrbitDifference_single` in finite acting groups, orbit-difference relations, coinvariants and norms; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L63) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifference_range

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteOrbitDifference_range {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) : (finiteOrbitDifference ρ).range = Representation.Coinvariants.ker ρ
```

**Native source docstring:** The range of the finite orbit-difference map is exactly the relation
submodule defining algebraic coinvariants.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L74) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifferenceContinuousHom

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteOrbitDifferenceContinuousHom {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : (Fin (Fintype.card H) → M) →ₜ+ M
```

**Native source docstring:** The orbit-difference map as a continuous additive homomorphism.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L96) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifferenceHom

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteOrbitDifferenceHom {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : CompHausAddCommGrp.of (Fin (Fintype.card H) → M) ⟶ CompHausAddCommGrp.of M
```

**Native source docstring:** The orbit-difference map in the category of compact Hausdorff additive
commutative groups.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L109) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteOrbitDifferenceHom_range

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteOrbitDifferenceHom_range {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : (CompHausAddCommGrp.Hom.hom (finiteOrbitDifferenceHom ρ hρ)).range = (Representation.Coinvariants.ker ρ).toAddSubgroup
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `finiteOrbitDifferenceHom_range` in finite acting groups, orbit-difference relations, coinvariants and norms; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L117) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.coinvariantsClosedAddSubgroup

Kind: `def`.

```lean
def ContinuousGroupCohomology.coinvariantsClosedAddSubgroup {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : ClosedAddSubgroup M
```

**Native source docstring:** The coinvariant relation subgroup is closed: it is the range of the
continuous finite orbit-difference map from a compact source.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L126) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariants

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.finiteCoinvariants {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : CompHausAddCommGrp.{uM}
```

**Native source docstring:** Algebraic coinvariants equipped with their compact Hausdorff quotient
topology.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L136) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsMk

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteCoinvariantsMk {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : CompHausAddCommGrp.of M ⟶ finiteCoinvariants ρ hρ
```

**Native source docstring:** The canonical continuous projection to finite coinvariants.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L143) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsMk_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteCoinvariantsMk_apply {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (x : M) : (CompHausAddCommGrp.Hom.hom (finiteCoinvariantsMk ρ hρ)) x = (Representation.Coinvariants.mk ρ) x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteCoinvariantsMk_apply` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L152) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsDesc

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteCoinvariantsDesc {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (f : M →ₗ[R] N) (hf : Continuous ⇑f) (hinv : ∀ (g : H), f ∘ₗ ρ g = f) : finiteCoinvariants ρ hρ ⟶ CompHausAddCommGrp.of N
```

**Native source docstring:** A continuous invariant linear map out of a finite-group representation
descends continuously to its compact coinvariants.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L161) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsDesc_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteCoinvariantsDesc_mk {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (f : M →ₗ[R] N) (hf : Continuous ⇑f) (hinv : ∀ (g : H), f ∘ₗ ρ g = f) (x : M) : (CompHausAddCommGrp.Hom.hom (finiteCoinvariantsDesc ρ hρ f hf hinv)) ((Representation.Coinvariants.mk ρ) x) = f x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteCoinvariantsDesc_mk` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L174) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsMap

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteCoinvariantsMap {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (τ : Representation R H N) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (hτ : ∀ (g : H), Continuous ⇑(τ g)) (f : ρ.IntertwiningMap τ) (hf : Continuous ⇑f) : finiteCoinvariants ρ hρ ⟶ finiteCoinvariants τ hτ
```

**Native source docstring:** A continuous intertwining map between finite-group representations induces
a continuous map on their compact coinvariants.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L182) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteCoinvariantsMap_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteCoinvariantsMap_mk {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (τ : Representation R H N) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (hτ : ∀ (g : H), Continuous ⇑(τ g)) (f : ρ.IntertwiningMap τ) (hf : Continuous ⇑f) (x : M) : (CompHausAddCommGrp.Hom.hom (finiteCoinvariantsMap ρ τ hρ hτ f hf)) ((Representation.Coinvariants.mk ρ) x) = (Representation.Coinvariants.mk τ) (f x)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteCoinvariantsMap_mk` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L196) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.group

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.group {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) (U : OpenSubgroup G) : CompHausAddCommGrp.{uA}
```

**Native source docstring:** The compact Hausdorff additive group at one level of a `LevelCompact`
coefficient system.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L245) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.continuous_quotientToInvariants_action

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.continuous_quotientToInvariants_action {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) (S : OpenNormalSubgroup G) (q : G ⧸ ↑S.toOpenSubgroup) : Continuous ⇑((A.quotientToInvariants ↑S.toOpenSubgroup).ρ q)
```

**Native source docstring:** The residual `G / S`-action on `A^S` is continuous for the level topology.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L255) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_eq_quotientToInvariants_norm

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_eq_quotientToInvariants_norm {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) [Fintype (G ⧸ ↑S.toOpenSubgroup)] (x : ↥(openSubgroupInvariants A S.toOpenSubgroup)) : ↑((relativeNorm A ⊤ S.toOpenSubgroup ⋯) x) = ↑((A.quotientToInvariants ↑S.toOpenSubgroup).ρ.norm x)
```

**Native source docstring:** The relative norm from `A^S` to `A^G` is the ordinary finite-group norm
for the residual `G / S`-action, after forgetting the redundant outer
invariance proof in its target.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L374) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_quotientToInvariants_action

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_quotientToInvariants_action {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) (q : G ⧸ ↑S.toOpenSubgroup) (x : ↥(openSubgroupInvariants A S.toOpenSubgroup)) : (relativeNorm A ⊤ S.toOpenSubgroup ⋯) (((A.quotientToInvariants ↑S.toOpenSubgroup).ρ q) x) = (relativeNorm A ⊤ S.toOpenSubgroup ⋯) x
```

**Native source docstring:** The accepted continuous relative norm from `A^S` to `A^G` is invariant
under the residual finite quotient action on its source.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L450) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.finiteCoinvariants

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.finiteCoinvariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) : CompHausAddCommGrp.{uA}
```

**Native source docstring:** The algebraic coinvariants `(A^S)_{G/S}` with the compact Hausdorff
quotient topology supplied by the level-compact structure.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L479) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.finiteCoinvariantsMk

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.finiteCoinvariantsMk {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) : group A L S.toOpenSubgroup ⟶ finiteCoinvariants A L S
```

**Native source docstring:** The canonical continuous map `A^S → (A^S)_{G/S}`.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L495) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.finiteCoinvariantsMk_apply

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.finiteCoinvariantsMk_apply {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) (x : ↥(openSubgroupInvariants A S.toOpenSubgroup)) : (CompHausAddCommGrp.Hom.hom (finiteCoinvariantsMk A L S)) x = (Representation.Coinvariants.mk (A.quotientToInvariants ↑S.toOpenSubgroup).ρ) x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `finiteCoinvariantsMk_apply` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L511) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) : finiteCoinvariants A L S ⟶ group A L ⊤
```

**Native source docstring:** The accepted continuous relative norm `A^S → A^G`, descended to the
compact Hausdorff coinvariants `(A^S)_{G/S}`.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L519) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants_mk {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) [IsTopologicalGroup G] [CompactSpace G] (S : OpenNormalSubgroup G) (x : ↥(openSubgroupInvariants A S.toOpenSubgroup)) : (CompHausAddCommGrp.Hom.hom (normFromFiniteCoinvariants A L S)) ((Representation.Coinvariants.mk (A.quotientToInvariants ↑S.toOpenSubgroup).ρ) x) = (relativeNorm A ⊤ S.toOpenSubgroup ⋯) x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `normFromFiniteCoinvariants_mk` for finite acting groups, orbit-difference relations, coinvariants and norms; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/FiniteCoinvariants.lean#L551) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.FiniteNegativeDeflation

7 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.nestedQuotientInvariantsHomologyNatTrans

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.nestedQuotientInvariantsHomologyNatTrans {R G : Type u} [CommRing R] [Group G] (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) : (Rep.quotientToInvariantsFunctor R S).comp ((Rep.quotientToInvariantsFunctor R (Subgroup.map (QuotientGroup.mk' S) T)).comp (groupHomology.functor R ((G ⧸ S) ⧸ Subgroup.map (QuotientGroup.mk' S) T) n)) ⟶ (Rep.quotientToInvariantsFunctor R T).comp (groupHomology.functor R (G ⧸ T) n)
```

**Native source docstring:** Homology transport from iterated invariants to direct invariants through
the third-isomorphism equivalence.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L42) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsHomologyNatTrans_app

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsHomologyNatTrans_app {R G : Type u} [CommRing R] [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) : (nestedQuotientInvariantsHomologyNatTrans S T hST n).app A = groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (nestedQuotientInvariantsRepIso A S T hST).hom n
```

**Native source docstring:** The homology transport component is the single map induced by the
third-isomorphism equivalence and the nested-invariants representation map.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L78) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteNegativeDeflationNatTrans

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteNegativeDeflationNatTrans {R G : Type u} [CommRing R] [Group G] (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : (Rep.quotientToInvariantsFunctor R S).comp (groupHomology.functor R (G ⧸ S) n) ⟶ (Rep.quotientToInvariantsFunctor R T).comp (groupHomology.functor R (G ⧸ T) n)
```

**Native source docstring:** Finite-level negative deflation, natural in the coefficient
representation. In positive homological degree `n`, its components model Tate
deflation in degree `-n-1`.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L91) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteNegativeDeflation

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.finiteNegativeDeflation {R G : Type u} [CommRing R] [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : groupHomology (A.quotientToInvariants S) n ⟶ groupHomology (A.quotientToInvariants T) n
```

**Native source docstring:** The component of finite-level negative deflation at `A`.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L112) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteNegativeDeflation_formula

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteNegativeDeflation_formula {R G : Type u} [CommRing R] [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : finiteNegativeDeflation A S T hST n = CategoryTheory.CategoryStruct.comp ((groupHomology.coinfNatTrans R (Subgroup.map (QuotientGroup.mk' S) T) n).app (A.quotientToInvariants S)) (CategoryTheory.CategoryStruct.comp ((groupHomology.functor R ((G ⧸ S) ⧸ Subgroup.map (QuotientGroup.mk' S) T) n).map (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants S) (Subgroup.map (QuotientGroup.mk' S) T))) (groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (nestedQuotientInvariantsRepIso A S T hST).hom n))
```

**Native source docstring:** Finite-level negative deflation is coinflation, followed by the quotient
norm, followed by transport through the third-isomorphism equivalence.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L120) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteNegativeDeflation_naturality

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteNegativeDeflation_naturality {R G : Type u} [CommRing R] [Group G] {A B : Rep R G} (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : CategoryTheory.CategoryStruct.comp ((groupHomology.functor R (G ⧸ S) n).map ((Rep.quotientToInvariantsFunctor R S).map f)) (finiteNegativeDeflation B S T hST n) = CategoryTheory.CategoryStruct.comp (finiteNegativeDeflation A S T hST n) ((groupHomology.functor R (G ⧸ T) n).map ((Rep.quotientToInvariantsFunctor R T).map f))
```

**Native source docstring:** Finite-level negative deflation commutes with coefficient morphisms.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L144) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.finiteNegativeDeflation_naturality_assoc

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.finiteNegativeDeflation_naturality_assoc {R G : Type u} [CommRing R] [Group G] {A B : Rep R G} (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) {Z : ModuleCat R} (h : groupHomology (B.quotientToInvariants T) n ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((groupHomology.functor R (G ⧸ S) n).map ((Rep.quotientToInvariantsFunctor R S).map f)) (finiteNegativeDeflation B S T hST n)) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (finiteNegativeDeflation A S T hST n) ((groupHomology.functor R (G ⧸ T) n).map ((Rep.quotientToInvariantsFunctor R T).map f))) h
```

**Native source docstring:** Finite-level negative deflation commutes with coefficient morphisms.

[Source](../ContinuousGroupCohomology/FiniteNegativeDeflation.lean#L145) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.GroupExtensionUlift

7 native named entries; 0 native instance-table rows.

#### ContinuousMulEquiv.ulift

Kind: `def`.

```lean
def ContinuousMulEquiv.ulift {G : Type uG} [Group G] [TopologicalSpace G] : ULift.{vG, uG} G ≃ₜ* G
```

**Native source docstring:** The canonical continuous multiplicative equivalence from a universe lift
of a group to the original group.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L30) (native source start line; generated entries may point to their parent).

#### ContinuousMulEquiv.ulift_apply

Kind: `theorem`.

```lean
theorem ContinuousMulEquiv.ulift_apply {G : Type uG} [Group G] [TopologicalSpace G] (x : ULift.{vG, uG} G) : ulift x = x.down
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_apply` for universe transport of the named topological group-extension maps; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L35) (native source start line; generated entries may point to their parent).

#### ContinuousMulEquiv.ulift_symm_apply

Kind: `theorem`.

```lean
theorem ContinuousMulEquiv.ulift_symm_apply {G : Type uG} [Group G] [TopologicalSpace G] (x : G) : ulift.symm x = { down := x }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_symm_apply` for universe transport of the named topological group-extension maps; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L38) (native source start line; generated entries may point to their parent).

#### GroupExtension.ulift

Kind: `def`.

```lean
def GroupExtension.ulift {N : Type uN} {E : Type uE} {G : Type uG} [Group N] [Group E] [Group G] (S : GroupExtension N E G) : GroupExtension (ULift.{vN, uN} N) (ULift.{vE, uE} E) (ULift.{vG, uG} G)
```

**Native source docstring:** Raise all three groups in a group extension through independently chosen
universes.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L48) (native source start line; generated entries may point to their parent).

#### GroupExtension.ulift_inl_apply

Kind: `theorem`.

```lean
theorem GroupExtension.ulift_inl_apply {N : Type uN} {E : Type uE} {G : Type uG} [Group N] [Group E] [Group G] (S : GroupExtension N E G) (n : ULift.{vN, uN} N) : S.ulift.inl n = { down := S.inl n.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_inl_apply` for universe transport of the named topological group-extension maps; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L74) (native source start line; generated entries may point to their parent).

#### GroupExtension.ulift_rightHom_apply

Kind: `theorem`.

```lean
theorem GroupExtension.ulift_rightHom_apply {N : Type uN} {E : Type uE} {G : Type uG} [Group N] [Group E] [Group G] (S : GroupExtension N E G) (e : ULift.{vE, uE} E) : S.ulift.rightHom e = { down := S.rightHom e.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_rightHom_apply` for universe transport of the named topological group-extension maps; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L78) (native source start line; generated entries may point to their parent).

#### GroupExtension.isSES_ulift

Kind: `theorem`.

```lean
theorem GroupExtension.isSES_ulift {N : Type uN} {E : Type uE} {G : Type uG} [Group N] [Group E] [Group G] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace G] (S : GroupExtension N E G) (hS : TopologicalGroup.IsSES S.inl S.rightHom) : TopologicalGroup.IsSES S.ulift.inl S.ulift.rightHom
```

**Native source docstring:** A topological short exact sequence remains short exact after independently
raising the universes of all three groups.

[Source](../ContinuousGroupCohomology/GroupExtensionUlift.lean#L84) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.HomogeneousCochainsUlift

13 native named entries; 0 native instance-table rows.

#### ContinuousMap.uliftContinuousLinearEquiv

Kind: `def`.

```lean
noncomputable def ContinuousMap.uliftContinuousLinearEquiv {k : Type u} [Semiring k] [TopologicalSpace k] {G : Type v} [TopologicalSpace G] {M : Type w} [TopologicalSpace M] [AddCommMonoid M] [Module k M] [ContinuousAdd M] [ContinuousSMul k M] : ULift.{max v' w', max w v} C(G, M) ≃L[k] C(ULift.{v', v} G, ULift.{w', w} M)
```

**Native source docstring:** Raising a continuous-function space is continuously linearly equivalent to
the continuous-function space between independently raised source and target
types.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L40) (native source start line; generated entries may point to their parent).

#### TopRep.coind₁UliftEquiv

Kind: `def`.

```lean
noncomputable def TopRep.coind₁UliftEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : X.coind₁.ulift.ρ.Equiv X.ulift.coind₁.ρ
```

**Native source docstring:** Coinduction by continuous functions commutes with independently raising
the acting group and coefficient carrier.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L78) (native source start line; generated entries may point to their parent).

#### TopRep.coind₁UliftIso

Kind: `def`.

```lean
noncomputable def TopRep.coind₁UliftIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : X.coind₁.ulift ≅ X.ulift.coind₁
```

**Native source docstring:** The topological representations obtained by coinducing before or after
independent universe lifts are isomorphic.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L90) (native source start line; generated entries may point to their parent).

#### TopRep.invariantsUliftContinuousLinearEquiv

Kind: `def`.

```lean
noncomputable def TopRep.invariantsUliftContinuousLinearEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (X : TopRep k G) : ULift.{w', w} ↥X.ρ.invariants ≃L[k] ↥X.ulift.ρ.invariants
```

**Native source docstring:** Invariants commute with independently raising the acting group and
coefficient carrier.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L144) (native source start line; generated entries may point to their parent).

#### TopRep.invariantsUliftIso

Kind: `def`.

```lean
noncomputable def TopRep.invariantsUliftIso {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (X : TopRep k G) : (TopModuleCat.uliftFunctor.{w', w, u} k).obj X.invariants ≅ X.ulift.invariants
```

**Native source docstring:** The invariant topological modules before and after independent universe
lifts are isomorphic.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L169) (native source start line; generated entries may point to their parent).

#### TopRep.resolutionUliftIsoSameUniverse

Kind: `def`.

```lean
noncomputable def TopRep.resolutionUliftIsoSameUniverse {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : (X.resolutionX n).ulift ≅ X.ulift.resolutionX n
```

**Native source docstring:** In one common small universe, every term of the recursive coinduced
resolution is isomorphic to the corresponding term after raising the acting
group and coefficient carrier.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L197) (native source start line; generated entries may point to their parent).

#### TopRep.resolutionUliftIsoSameUniverse_naturality

Kind: `theorem`.

```lean
theorem TopRep.resolutionUliftIsoSameUniverse_naturality {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) : CategoryTheory.CategoryStruct.comp (uliftMap (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id G) f n)) (Y.resolutionUliftIsoSameUniverse n).hom = CategoryTheory.CategoryStruct.comp (X.resolutionUliftIsoSameUniverse n).hom (ContinuousCohomology.resolutionMap (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f) n)
```

**Native source docstring:** The termwise same-universe resolution isomorphisms are natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L210) (native source start line; generated entries may point to their parent).

#### TopRep.resolutionUliftIsoSameUniverse_d_comm

Kind: `theorem`.

```lean
theorem TopRep.resolutionUliftIsoSameUniverse_d_comm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : CategoryTheory.CategoryStruct.comp (uliftMap (X.d n)) (X.resolutionUliftIsoSameUniverse (n + 1)).hom = CategoryTheory.CategoryStruct.comp (X.resolutionUliftIsoSameUniverse n).hom (X.ulift.d n)
```

**Native source docstring:** The termwise same-universe resolution isomorphisms commute with the
recursive resolution differential.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L228) (native source start line; generated entries may point to their parent).

#### TopRep.homogeneousCochainsUliftXIsoSameUniverse

Kind: `def`.

```lean
noncomputable def TopRep.homogeneousCochainsUliftXIsoSameUniverse {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : (TopModuleCat.uliftFunctor.{v, v, u} k).obj (X.homogeneousCochains.X n) ≅ X.ulift.homogeneousCochains.X n
```

**Native source docstring:** Degreewise isomorphism between the raised homogeneous cochains and the
homogeneous cochains of the raised representation, in one small universe.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L253) (native source start line; generated entries may point to their parent).

#### TopRep.homogeneousCochainsUliftXIsoSameUniverse_comm

Kind: `theorem`.

```lean
theorem TopRep.homogeneousCochainsUliftXIsoSameUniverse_comm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : CategoryTheory.CategoryStruct.comp ((TopModuleCat.uliftFunctor.{v, v, u} k).map (X.homogeneousCochains.d n (n + 1))) (X.homogeneousCochainsUliftXIsoSameUniverse (n + 1)).hom = CategoryTheory.CategoryStruct.comp (X.homogeneousCochainsUliftXIsoSameUniverse n).hom (X.ulift.homogeneousCochains.d n (n + 1))
```

**Native source docstring:** The degreewise same-universe homogeneous-cochain isomorphisms commute with
the cochain differential.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L263) (native source start line; generated entries may point to their parent).

#### TopRep.homogeneousCochainsUliftIsoSameUniverse

Kind: `def`.

```lean
noncomputable def TopRep.homogeneousCochainsUliftIsoSameUniverse {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : ((TopModuleCat.uliftFunctor.{v, v, u} k).mapHomologicalComplex (ComplexShape.up ℕ)).obj X.homogeneousCochains ≅ X.ulift.homogeneousCochains
```

**Native source docstring:** In one common small universe, raising the homogeneous cochain complex is
isomorphic to taking homogeneous cochains after raising the acting group and
coefficient carrier.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L282) (native source start line; generated entries may point to their parent).

#### TopRep.homogeneousCochainsUliftIsoSameUniverse_naturality

Kind: `theorem`.

```lean
theorem TopRep.homogeneousCochainsUliftIsoSameUniverse_naturality {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) : CategoryTheory.CategoryStruct.comp (((TopModuleCat.uliftFunctor.{v, v, u} k).mapHomologicalComplex (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f)) Y.homogeneousCochainsUliftIsoSameUniverse.hom = CategoryTheory.CategoryStruct.comp X.homogeneousCochainsUliftIsoSameUniverse.hom (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f))
```

**Native source docstring:** The same-universe homogeneous-cochain comparison is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L295) (native source start line; generated entries may point to their parent).

#### TopRep.homogeneousCochainsUliftIsoSameUniverse_naturality_assoc

Kind: `theorem`.

```lean
theorem TopRep.homogeneousCochainsUliftIsoSameUniverse_naturality_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) {Z : HomologicalComplex (TopModuleCat k) (ComplexShape.up ℕ)} (h : Y.ulift.homogeneousCochains ⟶ Z) : CategoryTheory.CategoryStruct.comp (((TopModuleCat.uliftFunctor.{v, v, u} k).mapHomologicalComplex (ComplexShape.up ℕ)).map (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G) f)) (CategoryTheory.CategoryStruct.comp Y.homogeneousCochainsUliftIsoSameUniverse.hom h) = CategoryTheory.CategoryStruct.comp X.homogeneousCochainsUliftIsoSameUniverse.hom (CategoryTheory.CategoryStruct.comp (ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id (ULift.{v, v} G)) (uliftMap f)) h)
```

**Native source docstring:** The same-universe homogeneous-cochain comparison is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/HomogeneousCochainsUlift.lean#L297) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.LevelCompact

18 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.openSubgroupInvariants

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.openSubgroupInvariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U : OpenSubgroup G) : Submodule R ↑A
```

**Native source docstring:** The submodule of vectors fixed by an open subgroup.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L38) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.openSubgroupInvariantsTransport

Kind: `def`.

```lean
def ContinuousGroupCohomology.openSubgroupInvariantsTransport {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V : OpenSubgroup G) (σ : G) (h : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U) : ↥(openSubgroupInvariants A U) →ₗ[R] ↥(openSubgroupInvariants A V)
```

**Native source docstring:** Transport open-subgroup invariants by the ambient group action.

The containment has the source-to-target orientation: if
`V ≤ σ U σ⁻¹`, then `a ↦ σ • a` sends `A^U` to `A^V`.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L42) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.openSubgroupInvariantsTransport_coe

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.openSubgroupInvariantsTransport_coe {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V : OpenSubgroup G) (σ : G) (h : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U) (x : ↥(openSubgroupInvariants A U)) : ↑((openSubgroupInvariantsTransport A U V σ h) x) = (A.ρ σ) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `openSubgroupInvariantsTransport_coe` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L57) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.openSubgroupInvariantsTransport_comp_le

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.openSubgroupInvariantsTransport_comp_le {G : Type uG} [Group G] [TopologicalSpace G] (U V W : OpenSubgroup G) (σ τ : G) (hUV : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U) (hVW : ↑W ≤ Subgroup.map ↑(MulAut.conj τ) ↑V) : ↑W ≤ Subgroup.map ↑(MulAut.conj (τ * σ)) ↑U
```

**Native source docstring:** The containment needed to compose two open-subgroup invariant transports.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L65) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.openSubgroupInvariantsTransport_comp

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.openSubgroupInvariantsTransport_comp {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V W : OpenSubgroup G) (σ τ : G) (hUV : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U) (hVW : ↑W ≤ Subgroup.map ↑(MulAut.conj τ) ↑V) : openSubgroupInvariantsTransport A V W τ hVW ∘ₗ openSubgroupInvariantsTransport A U V σ hUV = openSubgroupInvariantsTransport A U W (τ * σ) ⋯
```

**Native source docstring:** Transport through two subgroup containments composes by multiplying the
transporting elements in target-to-source order.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L75) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact

Kind: `structure`.

```lean
structure ContinuousGroupCohomology.LevelCompact {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) : Type (max uA uG)
```

**Native source docstring:** Compact Hausdorff additive-group topologies on the invariants under every
open subgroup, compatible with transport by the ambient group action.

This is additional levelwise topology data.  It does not impose a topology on
the ambient coefficient module or on the coefficient ring.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L88) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupCohomology.LevelCompact.mk : {R : Type uR} → [inst : CommRing R] → {G : Type uG} → [inst_1 : Group G] → [inst_2 : TopologicalSpace G] → {A : Rep R G} → (topology : (U : OpenSubgroup G) → TopologicalSpace ↥(ContinuousGroupCohomology.openSubgroupInvariants A U)) → (∀ (U : OpenSubgroup G), CompactSpace ↥(ContinuousGroupCohomology.openSubgroupInvariants A U)) → (∀ (U : OpenSubgroup G), T2Space ↥(ContinuousGroupCohomology.openSubgroupInvariants A U)) → (∀ (U : OpenSubgroup G), IsTopologicalAddGroup ↥(ContinuousGroupCohomology.openSubgroupInvariants A U)) → (∀ (U V : OpenSubgroup G) (σ : G) (h : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U), Continuous ⇑(ContinuousGroupCohomology.openSubgroupInvariantsTransport A U V σ h)) → ContinuousGroupCohomology.LevelCompact A
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupCohomology.LevelCompact`; the structure fields and parameters are in the displayed signature and source declaration. Compact hausdorff models of open-subgroup invariant levels.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L88) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.topology

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompact.topology {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A : Rep R G} (self : LevelCompact A) (U : OpenSubgroup G) : TopologicalSpace ↥(openSubgroupInvariants A U)
```

**Original catalogue explanation (not a Lean docstring):** Defines `topology` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L94) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.compact

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.compact {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A : Rep R G} (self : LevelCompact A) (U : OpenSubgroup G) : CompactSpace ↥(openSubgroupInvariants A U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `compact` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L95) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.t2

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.t2 {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A : Rep R G} (self : LevelCompact A) (U : OpenSubgroup G) : T2Space ↥(openSubgroupInvariants A U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `t2` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L96) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.topologicalAddGroup

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.topologicalAddGroup {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A : Rep R G} (self : LevelCompact A) (U : OpenSubgroup G) : IsTopologicalAddGroup ↥(openSubgroupInvariants A U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `topologicalAddGroup` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L97) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.continuous_transport

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.continuous_transport {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A : Rep R G} (self : LevelCompact A) (U V : OpenSubgroup G) (σ : G) (h : ↑V ≤ Subgroup.map ↑(MulAut.conj σ) ↑U) : Continuous ⇑(openSubgroupInvariantsTransport A U V σ h)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `continuous_transport` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L99) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.inclusion

Kind: `def`.

```lean
def ContinuousGroupCohomology.LevelCompact.inclusion {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) : ↥(openSubgroupInvariants A U) →ₗ[R] ↥(openSubgroupInvariants A V)
```

**Native source docstring:** Inclusion of invariant submodules for an inclusion of open subgroups.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L106) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.inclusion_coe

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.inclusion_coe {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (x : ↥(openSubgroupInvariants A U)) : ↑((inclusion A U V h) x) = ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `inclusion_coe` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L113) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.inclusion_self

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.inclusion_self {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U : OpenSubgroup G) : inclusion A U U ⋯ = LinearMap.id
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `inclusion_self` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L119) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.inclusion_injective

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.inclusion_injective {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) : Function.Injective ⇑(inclusion A U V h)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `inclusion_injective` in compact Hausdorff models of open-subgroup invariant levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L125) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.continuous_inclusion

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.continuous_inclusion {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) : Continuous ⇑(inclusion A U V h)
```

**Native source docstring:** The inclusion `A^U → A^V` is continuous whenever `V ≤ U`.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L132) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.inclusion_isClosedEmbedding

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.inclusion_isClosedEmbedding {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) : Topology.IsClosedEmbedding ⇑(inclusion A U V h)
```

**Native source docstring:** The natural inclusion between two levels is a closed embedding.  In
particular, the topology on `A^U` is the topology induced from `A^V`.

[Source](../ContinuousGroupCohomology/LevelCompact.lean#L141) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.LevelCompactFunctoriality

20 native named entries; 2 native instance-table rows.

#### ContinuousGroupCohomology.LevelCompactRep

Kind: `structure`.

```lean
structure ContinuousGroupCohomology.LevelCompactRep (R : Type uR) [CommRing R] (G : Type uG) [Group G] [TopologicalSpace G] : Type (max (max (uA + 1) uG) uR)
```

**Native source docstring:** A representation together with compact Hausdorff additive-group
topologies on all of its open-subgroup invariants.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L35) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupCohomology.LevelCompactRep.mk : {R : Type uR} → [inst : CommRing R] → {G : Type uG} → [inst_1 : Group G] → [inst_2 : TopologicalSpace G] → (rep : Rep R G) → ContinuousGroupCohomology.LevelCompact rep → ContinuousGroupCohomology.LevelCompactRep.{uR, uG, uA} R G
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupCohomology.LevelCompactRep`; the structure fields and parameters are in the displayed signature and source declaration. Functoriality of compact level systems and their invariant maps.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L35) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.rep

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompactRep.rep {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (self : LevelCompactRep.{uR, uG, uA} R G) : Rep R G
```

**Native source docstring:** The underlying representation.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L40) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.levelCompact

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompactRep.levelCompact {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (self : LevelCompactRep.{uR, uG, uA} R G) : LevelCompact self.rep
```

**Native source docstring:** The levelwise compact topology data.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L42) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.invariantsMap

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.LevelCompactRep.invariantsMap {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : Rep R G} (f : A ⟶ B) (U : OpenSubgroup G) : ↥(openSubgroupInvariants A U) →ₗ[R] ↥(openSubgroupInvariants B U)
```

**Native source docstring:** The map on open-subgroup invariants induced by a representation
morphism.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L48) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom

Kind: `structure`.

```lean
structure ContinuousGroupCohomology.LevelCompactRep.Hom {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A B : LevelCompactRep.{uR, uG, uA} R G) : Type uA
```

**Native source docstring:** A morphism of level-compact representations is a representation morphism
whose restriction to invariants at every open subgroup is continuous for the
specified level topologies.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L55) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupCohomology.LevelCompactRep.Hom.mk : {R : Type uR} → [inst : CommRing R] → {G : Type uG} → [inst_1 : Group G] → [inst_2 : TopologicalSpace G] → {A B : ContinuousGroupCohomology.LevelCompactRep.{uR, uG, uA} R G} → (hom : A.rep ⟶ B.rep) → (∀ (U : OpenSubgroup G), Continuous ⇑(ContinuousGroupCohomology.LevelCompactRep.invariantsMap hom U)) → A.Hom B
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupCohomology.LevelCompactRep.Hom`; the structure fields and parameters are in the displayed signature and source declaration. Functoriality of compact level systems and their invariant maps.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L55) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom.ext

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.Hom.ext {R : Type uR} {inst✝ : CommRing R} {G : Type uG} {inst✝¹ : Group G} {inst✝² : TopologicalSpace G} {A B : LevelCompactRep.{uR, uG, uA} R G} {x y : A.Hom B} (hom : x.hom = y.hom) : x = y
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `ext` in functoriality of compact level systems and their invariant maps; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L58) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom.ext_iff

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.Hom.ext_iff {R : Type uR} {inst✝ : CommRing R} {G : Type uG} {inst✝¹ : Group G} {inst✝² : TopologicalSpace G} {A B : LevelCompactRep.{uR, uG, uA} R G} {x y : A.Hom B} : x = y ↔ x.hom = y.hom
```

**Original catalogue explanation (not a Lean docstring):** The iff characterization named `ext_iff` in functoriality of compact level systems and their invariant maps; use the full signature for both directions and their assumptions.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L58) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom.hom

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompactRep.Hom.hom {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (self : A.Hom B) : A.rep ⟶ B.rep
```

**Native source docstring:** The underlying representation morphism.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L61) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.Hom.continuous_invariants

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.Hom.continuous_invariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (self : A.Hom B) (U : OpenSubgroup G) : Continuous ⇑(invariantsMap self.hom U)
```

**Native source docstring:** Continuity at every open-subgroup invariant level.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L63) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.instCategory

Kind: `instance`.

```lean
instance ContinuousGroupCohomology.LevelCompactRep.instCategory {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] : CategoryTheory.Category.{uA, max (max (uA + 1) uG) uR} (LevelCompactRep.{uR, uG, uA} R G)
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Category` instance in functoriality of compact level systems and their invariant maps (native type names: `ContinuousGroupCohomology.LevelCompactRep`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L69) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.forget

Kind: `def`.

```lean
def ContinuousGroupCohomology.LevelCompactRep.forget {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] : CategoryTheory.Functor (LevelCompactRep.{uR, uG, uA} R G) (Rep R G)
```

**Native source docstring:** Forget a level-compact representation to its underlying representation.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L98) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.forget_map

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.forget_map {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {X✝ Y✝ : LevelCompactRep.{uR, uG, uA} R G} (f : X✝ ⟶ Y✝) : forget.map f = f.hom
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `forget_map` in functoriality of compact level systems and their invariant maps; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L99) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.forget_obj

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.forget_obj {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : LevelCompactRep.{uR, uG, uA} R G) : forget.obj A = A.rep
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `forget_obj` in functoriality of compact level systems and their invariant maps; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L99) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget

Kind: `instance`.

```lean
instance ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] : forget.Faithful
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Faithful` instance in functoriality of compact level systems and their invariant maps (native type names: `ContinuousGroupCohomology.LevelCompactRep.forget`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L104) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.toRepHom

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompactRep.toRepHom {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B) : A.rep ⟶ B.rep
```

**Native source docstring:** The representation morphism underlying a level-compact morphism.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L107) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.mapInvariants

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.LevelCompactRep.mapInvariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B) (U : OpenSubgroup G) : ↥(openSubgroupInvariants A.rep U) →ₗ[R] ↥(openSubgroupInvariants B.rep U)
```

**Native source docstring:** The map on invariants induced by a level-compact morphism.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L112) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.mapInvariants_coe

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.mapInvariants_coe {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B) (U : OpenSubgroup G) (x : ↥(openSubgroupInvariants A.rep U)) : ↑((mapInvariants f U) x) = (CategoryTheory.ConcreteCategory.hom f.hom) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mapInvariants_coe` in functoriality of compact level systems and their invariant maps; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L118) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompactRep.continuous_mapInvariants

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompactRep.continuous_mapInvariants {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {A B : LevelCompactRep.{uR, uG, uA} R G} (f : A ⟶ B) (U : OpenSubgroup G) : Continuous ⇑(mapInvariants f U)
```

**Native source docstring:** The invariant-level map of a level-compact morphism is continuous.

[Source](../ContinuousGroupCohomology/LevelCompactFunctoriality.lean#L124) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ContinuousGroupCohomology.LevelCompactRep.instCategory`: `CategoryTheory.Category`; type names: `ContinuousGroupCohomology.LevelCompactRep`

- `ContinuousGroupCohomology.LevelCompactRep.instFaithfulRepForget`: `CategoryTheory.Functor.Faithful`; type names: `ContinuousGroupCohomology.LevelCompactRep.forget`

### ContinuousGroupCohomology.LevelCompactNorm

14 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup

Kind: `def`.

```lean
def ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup {G : Type uG} [Group G] [TopologicalSpace G] (U V : OpenSubgroup G) : OpenSubgroup ↥U
```

**Native source docstring:** The pullback of `V` to the open subgroup `U`.  When `V ≤ U`, this is the
copy of `V` used to choose relative norm representatives inside `U`.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L43) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup_finiteIndex

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup_finiteIndex {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U V : OpenSubgroup G) : (↑(relativeNormSubgroup U V)).FiniteIndex
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `relativeNormSubgroup_finiteIndex` in relative norm maps between compact open-subgroup levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L48) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNormTransversalFintype

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.relativeNormTransversalFintype {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U V : OpenSubgroup G) (T : (↑(relativeNormSubgroup U V)).RightTransversal) : Fintype ↑↑T
```

**Original catalogue explanation (not a Lean docstring):** Defines `relativeNormTransversalFintype` in relative norm maps between compact open-subgroup levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L52) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (_h : V ≤ U) (T : (↑(relativeNormSubgroup U V)).RightTransversal) : ↥(openSubgroupInvariants A V) →ₗ[R] ↥(openSubgroupInvariants A U)
```

**Native source docstring:** The relative norm computed using a right transversal inside `U`.

The inverse in the summand matches the right-transversal convention.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L59) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal_coe

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal_coe {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T : (↑(relativeNormSubgroup U V)).RightTransversal) (x : ↥(openSubgroupInvariants A V)) : ↑((relativeNormWithTransversal A U V h T) x) = ∑ t : ↑↑T, (A.ρ (↑↑t)⁻¹) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `relativeNormWithTransversal_coe` in relative norm maps between compact open-subgroup levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L105) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal_eq

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal_eq {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T S : (↑(relativeNormSubgroup U V)).RightTransversal) : relativeNormWithTransversal A U V h T = relativeNormWithTransversal A U V h S
```

**Native source docstring:** The relative norm is independent of the chosen right transversal.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L114) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.relativeNorm {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) : ↥(openSubgroupInvariants A V) →ₗ[R] ↥(openSubgroupInvariants A U)
```

**Native source docstring:** The canonical relative norm from `V`-invariants to `U`-invariants.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L149) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_eq_withTransversal

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_eq_withTransversal {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T : (↑(relativeNormSubgroup U V)).RightTransversal) : relativeNorm A U V h = relativeNormWithTransversal A U V h T
```

**Native source docstring:** The canonical relative norm can be computed with any right transversal.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L154) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_comp

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_comp {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V W : OpenSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) : relativeNorm A U V hVU ∘ₗ relativeNorm A V W hWV = relativeNorm A U W ⋯
```

**Native source docstring:** Relative norms compose through a tower of open subgroups.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L298) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_refl

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_refl {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenSubgroup G) : relativeNorm A U U ⋯ = LinearMap.id
```

**Native source docstring:** The relative norm from an open subgroup to itself is the identity.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L312) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_quotientToInvariants_action_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_quotientToInvariants_action_mk {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) (g : G) (x : ↥(openSubgroupInvariants A V.toOpenSubgroup)) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ ((QuotientGroup.mk' ↑U.toOpenSubgroup) g)) ((relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) x) = (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) (((A.quotientToInvariants ↑V.toOpenSubgroup).ρ ((QuotientGroup.mk' ↑V.toOpenSubgroup) g)) x)
```

**Native source docstring:** Relative norms between open normal levels commute with the residual quotient
actions, evaluated on representatives in the ambient group.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L464) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_range_quotientToInvariants_stable

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_range_quotientToInvariants_stable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) (q : G ⧸ ↑U.toOpenSubgroup) {y : ↥(openSubgroupInvariants A U.toOpenSubgroup)} (hy : y ∈ (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ q) y ∈ (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Native source docstring:** The range of a relative norm between open normal levels is stable under
the residual action on its target.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L490) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.continuous_relativeNormWithTransversal

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.continuous_relativeNormWithTransversal {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) (T : (↑(relativeNormSubgroup U V)).RightTransversal) : Continuous ⇑(relativeNormWithTransversal A U V h T)
```

**Native source docstring:** A relative norm computed with any right transversal is continuous for the
levelwise compact topologies.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L538) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.continuous_relativeNorm

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.continuous_relativeNorm {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) : Continuous ⇑(relativeNorm A U V h)
```

**Native source docstring:** The canonical relative norm is continuous for a `LevelCompact` system.

[Source](../ContinuousGroupCohomology/LevelCompactNorm.lean#L570) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.LowDegreeExact

57 native named entries; 0 native instance-table rows.

#### ContinuousCohomology.TopologicallySplitShortExact

Kind: `structure`.

```lean
structure ContinuousCohomology.TopologicallySplitShortExact {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (A B C : TopRep k G) : Type (max v w)
```

**Native source docstring:** A short exact sequence of topological representations equipped with
continuous linear splitting data on the underlying topological modules.

The retraction and section need not commute with the `G`-actions.  Requiring
them to be equivariant would make the low-degree connecting map trivial.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L30) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.mk

Kind: `ctor`.

```lean
constructor ContinuousCohomology.TopologicallySplitShortExact.mk : {k : Type u} → [inst : Ring k] → [inst_1 : TopologicalSpace k] → {G : Type v} → [inst_2 : Group G] → {A B C : TopRep k G} → (i : A ⟶ B) → (p : B ⟶ C) → Function.Exact ⇑(CategoryTheory.ConcreteCategory.hom i) ⇑(CategoryTheory.ConcreteCategory.hom p) → Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom i) → Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom p) → (retract : ↑B →L[k] ↑A) → (∀ (a : ↑A), retract ((CategoryTheory.ConcreteCategory.hom i) a) = a) → (section_ : ↑C →L[k] ↑B) → (∀ (c : ↑C), (CategoryTheory.ConcreteCategory.hom p) (section_ c) = c) → ContinuousCohomology.TopologicallySplitShortExact A B C
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousCohomology.TopologicallySplitShortExact`; the structure fields and parameters are in the displayed signature and source declaration. Connecting morphisms and low-degree exactness for topologically split sequences.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L30) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.i

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : A ⟶ B
```

**Native source docstring:** The equivariant inclusion of the kernel coefficient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L38) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.p

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.p {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : B ⟶ C
```

**Native source docstring:** The equivariant projection to the quotient coefficient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L40) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : Function.Exact ⇑(CategoryTheory.ConcreteCategory.hom self.i) ⇑(CategoryTheory.ConcreteCategory.hom self.p)
```

**Native source docstring:** Exactness of the underlying sequence.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L42) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.injective_i

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.injective_i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : Function.Injective ⇑(CategoryTheory.ConcreteCategory.hom self.i)
```

**Native source docstring:** Injectivity at the left endpoint.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L44) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.surjective_p

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.surjective_p {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : Function.Surjective ⇑(CategoryTheory.ConcreteCategory.hom self.p)
```

**Native source docstring:** Surjectivity at the right endpoint.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L46) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.retract

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.retract {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : ↑B →L[k] ↑A
```

**Native source docstring:** A continuous linear retraction of `i`, not necessarily equivariant.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L48) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.retract_i

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.retract_i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) (a : ↑A) : self.retract ((CategoryTheory.ConcreteCategory.hom self.i) a) = a
```

**Native source docstring:** The retraction is a left inverse to `i`.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L50) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.section_

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.section_ {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) : ↑C →L[k] ↑B
```

**Native source docstring:** A continuous linear section of `p`, not necessarily equivariant.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L52) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.p_section

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.p_section {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (self : TopologicallySplitShortExact A B C) (c : ↑C) : (CategoryTheory.ConcreteCategory.hom self.p) (self.section_ c) = c
```

**Native source docstring:** The section is a right inverse to `p`.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L54) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.p_i

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.p_i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (a : ↑A) : (CategoryTheory.ConcreteCategory.hom S.p) ((CategoryTheory.ConcreteCategory.hom S.i) a) = 0
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `p_i` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L60) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.retract_i_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.retract_i_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (a : ↑A) : S.retract ((CategoryTheory.ConcreteCategory.hom S.i) a) = a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `retract_i_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L64) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.p_section_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.p_section_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (c : ↑C) : (CategoryTheory.ConcreteCategory.hom S.p) (S.section_ c) = c
```

**Original catalogue explanation (not a Lean docstring):** The named computation `p_section_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L68) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.i_retract_of_p_eq_zero

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.i_retract_of_p_eq_zero {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) {b : ↑B} (hb : (CategoryTheory.ConcreteCategory.hom S.p) b = 0) : (CategoryTheory.ConcreteCategory.hom S.i) (S.retract b) = b
```

**Native source docstring:** On the kernel of `p`, applying the retraction and then `i` recovers the
original coefficient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L72) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exists_eq_i_of_p_eq_zero

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exists_eq_i_of_p_eq_zero {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) {b : ↑B} (hb : (CategoryTheory.ConcreteCategory.hom S.p) b = 0) : ∃ (a : ↑A), (CategoryTheory.ConcreteCategory.hom S.i) a = b
```

**Native source docstring:** Every element of the kernel of `p` has the canonical preimage supplied by
the chosen retraction.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L79) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.retract_eq_on_ker

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.retract_eq_on_ker {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (r : ↑B →L[k] ↑A) (hr : ∀ (a : ↑A), r ((CategoryTheory.ConcreteCategory.hom S.i) a) = a) {b : ↑B} (hb : (CategoryTheory.ConcreteCategory.hom S.p) b = 0) : r b = S.retract b
```

**Native source docstring:** Any two underlying continuous-linear retractions of `i` agree on
`ker p`.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L85) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.withRetract

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.withRetract {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (r : ↑B →L[k] ↑A) (hr : ∀ (a : ↑A), r ((CategoryTheory.ConcreteCategory.hom S.i) a) = a) : TopologicallySplitShortExact A B C
```

**Native source docstring:** Replace the chosen underlying retraction without changing the exact
coefficient sequence.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L92) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.withSection

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.withSection {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (s : ↑C →L[k] ↑B) (hs : ∀ (c : ↑C), (CategoryTheory.ConcreteCategory.hom S.p) (s c) = c) : TopologicallySplitShortExact A B C
```

**Native source docstring:** Replace the chosen underlying section without changing the exact
coefficient sequence.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L98) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom

Kind: `structure`.

```lean
structure ContinuousCohomology.TopologicallySplitShortExact.Hom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) {A' B' C' : TopRep k G} (T : TopologicallySplitShortExact A' B' C') : Type (max v w)
```

**Native source docstring:** A morphism of topologically split short exact sequences.  Compatibility
is required only for the equivariant coefficient maps, not for the chosen
underlying splittings.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L104) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.mk

Kind: `ctor`.

```lean
constructor ContinuousCohomology.TopologicallySplitShortExact.Hom.mk : {k : Type u} → [inst : Ring k] → [inst_1 : TopologicalSpace k] → {G : Type v} → [inst_2 : Group G] → {A B C : TopRep k G} → {S : ContinuousCohomology.TopologicallySplitShortExact A B C} → {A' B' C' : TopRep k G} → {T : ContinuousCohomology.TopologicallySplitShortExact A' B' C'} → (a : A ⟶ A') → (b : B ⟶ B') → (c : C ⟶ C') → CategoryTheory.CategoryStruct.comp S.i b = CategoryTheory.CategoryStruct.comp a T.i → CategoryTheory.CategoryStruct.comp S.p c = CategoryTheory.CategoryStruct.comp b T.p → S.Hom T
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousCohomology.TopologicallySplitShortExact.Hom`; the structure fields and parameters are in the displayed signature and source declaration. Connecting morphisms and low-degree exactness for topologically split sequences.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L104) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.a

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.Hom.a {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} {S : TopologicallySplitShortExact A B C} {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (self : S.Hom T) : A ⟶ A'
```

**Native source docstring:** The map on kernel coefficients.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L110) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.b

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.Hom.b {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} {S : TopologicallySplitShortExact A B C} {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (self : S.Hom T) : B ⟶ B'
```

**Native source docstring:** The map on middle coefficients.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L112) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.c

Kind: `def`.

```lean
abbrev ContinuousCohomology.TopologicallySplitShortExact.Hom.c {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} {S : TopologicallySplitShortExact A B C} {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (self : S.Hom T) : C ⟶ C'
```

**Native source docstring:** The map on quotient coefficients.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L114) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} {S : TopologicallySplitShortExact A B C} {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (self : S.Hom T) : CategoryTheory.CategoryStruct.comp S.i self.b = CategoryTheory.CategoryStruct.comp self.a T.i
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `i_comm` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L115) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} {S : TopologicallySplitShortExact A B C} {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (self : S.Hom T) : CategoryTheory.CategoryStruct.comp S.p self.c = CategoryTheory.CategoryStruct.comp self.b T.p
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `p_comm` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L116) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.Hom.i_comm_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (F : S.Hom T) (a : ↑A) : (CategoryTheory.ConcreteCategory.hom F.b) ((CategoryTheory.ConcreteCategory.hom S.i) a) = (CategoryTheory.ConcreteCategory.hom T.i) ((CategoryTheory.ConcreteCategory.hom F.a) a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `i_comm_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L123) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.Hom.p_comm_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) {A' B' C' : TopRep k G} {T : TopologicallySplitShortExact A' B' C'} (F : S.Hom T) (b : ↑B) : (CategoryTheory.ConcreteCategory.hom F.c) ((CategoryTheory.ConcreteCategory.hom S.p) b) = (CategoryTheory.ConcreteCategory.hom T.p) ((CategoryTheory.ConcreteCategory.hom F.b) b)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `p_comm_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L128) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.invariantsInclusion

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.invariantsInclusion {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) : ↥A.ρ.invariants →L[k] ↥B.ρ.invariants
```

**Native source docstring:** The inclusion induced on invariant coefficients.
The application formula computes using the underlying equivariant inclusion.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L135) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.invariantsProjection

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.invariantsProjection {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) : ↥B.ρ.invariants →L[k] ↥C.ρ.invariants
```

**Native source docstring:** The projection induced on invariant coefficients.
The application formula computes using the underlying equivariant projection.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L141) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.invariantsInclusion_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.invariantsInclusion_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (a : ↥A.ρ.invariants) : ↑(S.invariantsInclusion a) = (CategoryTheory.ConcreteCategory.hom S.i) ↑a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `invariantsInclusion_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L147) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.invariantsProjection_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.invariantsProjection_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (b : ↥B.ρ.invariants) : ↑(S.invariantsProjection b) = (CategoryTheory.ConcreteCategory.hom S.p) ↑b
```

**Original catalogue explanation (not a Lean docstring):** The named computation `invariantsProjection_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L151) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsInclusion_invariantsProjection

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsInclusion_invariantsProjection {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) : Function.Exact ⇑S.invariantsInclusion ⇑S.invariantsProjection
```

**Native source docstring:** Exactness of the invariant-coefficient sequence at the middle term.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L155) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.sectionOnInvariants

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.sectionOnInvariants {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) : ↥C.ρ.invariants →L[k] ↑B
```

**Native source docstring:** The chosen section, restricted to invariant quotient coefficients.
Its application evaluates the underlying continuous section.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L176) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.sectionOnInvariants_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.sectionOnInvariants_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (c : ↥C.ρ.invariants) : S.sectionOnInvariants c = S.section_ ↑c
```

**Original catalogue explanation (not a Lean docstring):** The named computation `sectionOnInvariants_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L183) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingRawMap

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.connectingRawMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [B.JointlyContinuous] : ↥C.ρ.invariants →L[k] C(G, ↑A)
```

**Native source docstring:** The continuous `A`-valued function obtained by applying the retraction to
the principal defect of a chosen lift. Its application computes this defect.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L187) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingRawMap_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingRawMap_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [B.JointlyContinuous] (c : ↥C.ρ.invariants) (g : G) : (S.connectingRawMap c) g = S.retract ((B.ρ g) (S.section_ ↑c) - S.section_ ↑c)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `connectingRawMap_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L197) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.p_section_defect_eq_zero

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.p_section_defect_eq_zero {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) (c : ↥C.ρ.invariants) (g : G) : (CategoryTheory.ConcreteCategory.hom S.p) ((B.ρ g) (S.section_ ↑c) - S.section_ ↑c) = 0
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `p_section_defect_eq_zero` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L204) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [B.JointlyContinuous] : ↥C.ρ.invariants →L[k] ↥(continuousCrossedHom A)
```

**Native source docstring:** The connecting construction before quotienting by principal crossed
homomorphisms. Its application computes the raw connecting cocycle.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L208) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [B.JointlyContinuous] (c : ↥C.ρ.invariants) (g : G) : ↑(S.connectingCrossed c) g = S.retract ((B.ρ g) (S.section_ ↑c) - S.section_ ↑c)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `connectingCrossed_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L230) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_withRetract

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_withRetract {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [B.JointlyContinuous] (r : ↑B →L[k] ↑A) (hr : ∀ (a : ↑A), r ((CategoryTheory.ConcreteCategory.hom S.i) a) = a) : (S.withRetract r hr).connectingCrossed = S.connectingCrossed
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `connectingCrossed_withRetract` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L237) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_change_section

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_change_section {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (s : ↑C →L[k] ↑B) (hs : ∀ (c : ↑C), (CategoryTheory.ConcreteCategory.hom S.p) (s c) = c) (c : ↥C.ρ.invariants) : S.connectingCrossed c - (S.withSection s hs).connectingCrossed c = (principalToCrossed A) (S.retract (S.section_ ↑c - s ↑c))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `connectingCrossed_change_section` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L246) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient

Kind: `def`.

```lean
def ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : ↥C.ρ.invariants →L[k] ↥(continuousCrossedHom A) ⧸ principalCocycles A
```

**Native source docstring:** The low-degree connecting map into continuous crossed homomorphisms modulo
principal crossed homomorphisms. Its application computes on representatives.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L272) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (c : ↥C.ρ.invariants) : S.connectingQuotient c = (principalCocycles A).mkQ (S.connectingCrossed c)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `connectingQuotient_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L281) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withRetract

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withRetract {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (r : ↑B →L[k] ↑A) (hr : ∀ (a : ↑A), r ((CategoryTheory.ConcreteCategory.hom S.i) a) = a) : (S.withRetract r hr).connectingQuotient = S.connectingQuotient
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `connectingQuotient_withRetract` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L288) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withSection

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_withSection {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (s : ↑C →L[k] ↑B) (hs : ∀ (c : ↑C), (CategoryTheory.ConcreteCategory.hom S.p) (s c) = c) : (S.withSection s hs).connectingQuotient = S.connectingQuotient
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `connectingQuotient_withSection` in connecting morphisms and low-degree exactness for topologically split sequences; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L296) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_invariantsProjection

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingCrossed_invariantsProjection {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (b : ↥B.ρ.invariants) : S.connectingCrossed (S.invariantsProjection b) = (principalToCrossed A) (S.retract (S.section_ ((CategoryTheory.ConcreteCategory.hom S.p) ↑b) - ↑b))
```

**Native source docstring:** If an invariant quotient coefficient already has an invariant lift, its
connecting crossed homomorphism is principal.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L310) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsProjection_connectingQuotient

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsProjection_connectingQuotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : Function.Exact ⇑S.invariantsProjection ⇑S.connectingQuotient
```

**Native source docstring:** Exactness at the quotient-invariant term of the low-degree sequence.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L335) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_connectingQuotient_crossedQuotientMap_i

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_connectingQuotient_crossedQuotientMap_i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : Function.Exact ⇑S.connectingQuotient ⇑(crossedQuotientMap S.i)
```

**Native source docstring:** Exactness at the first crossed-homomorphism quotient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L373) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_crossedQuotientMap_i_crossedQuotientMap_p

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_crossedQuotientMap_i_crossedQuotientMap_p {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [A.JointlyContinuous] [B.JointlyContinuous] [C.JointlyContinuous] : Function.Exact ⇑(crossedQuotientMap S.i) ⇑(crossedQuotientMap S.p)
```

**Native source docstring:** Exactness at the second crossed-homomorphism quotient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L433) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingQuotient_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] {A' B' C' : TopRep k G} (T : TopologicallySplitShortExact A' B' C') (F : S.Hom T) [A.JointlyContinuous] [B.JointlyContinuous] [A'.JointlyContinuous] [B'.JointlyContinuous] : crossedQuotientMap F.a ∘SL S.connectingQuotient = T.connectingQuotient ∘SL (TopRep.Hom.hom F.c).mapInvariants
```

**Native source docstring:** The quotient-level connecting map is natural for morphisms of split short
exact sequences; the chosen underlying splittings need not be compatible.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L498) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingMap

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.TopologicallySplitShortExact.connectingMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : ↧↥C.ρ.invariants ⟶ continuousCohomology 1 A
```

**Native source docstring:** The connecting map from invariant quotient coefficients to mathlib's
native first continuous cohomology object. Its application factors through
the crossed-homomorphism quotient.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L540) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingMap_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingMap_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] (c : ↥C.ρ.invariants) : (TopModuleCat.Hom.hom S.connectingMap) c = (TopModuleCat.Hom.hom (degreeOneIso A).hom) (S.connectingQuotient c)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `connectingMap_apply` for connecting morphisms and low-degree exactness for topologically split sequences; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L549) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.connectingMap_natural

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.connectingMap_natural {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] {A' B' C' : TopRep k G} (T : TopologicallySplitShortExact A' B' C') (F : S.Hom T) [A.JointlyContinuous] [B.JointlyContinuous] [A'.JointlyContinuous] [B'.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (TopRep.Hom.hom F.c).mapInvariants) T.connectingMap = CategoryTheory.CategoryStruct.comp S.connectingMap (map (ContinuousMonoidHom.id G) F.a 1)
```

**Native source docstring:** The native connecting map is natural for morphisms of topologically split
short exact sequences.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L555) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsProjection_connectingMap

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_invariantsProjection_connectingMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : Function.Exact ⇑S.invariantsProjection ⇑(TopModuleCat.Hom.hom S.connectingMap)
```

**Native source docstring:** Exactness at the quotient-invariant term, with the connecting map valued
in mathlib's native first continuous cohomology object.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L579) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_connectingMap_map_i

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_connectingMap_map_i {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : Function.Exact ⇑(TopModuleCat.Hom.hom S.connectingMap) ⇑(TopModuleCat.Hom.hom (map (ContinuousMonoidHom.id G) S.i 1))
```

**Native source docstring:** Exactness at the first native continuous-cohomology term.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L598) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.TopologicallySplitShortExact.exact_map_i_map_p

Kind: `theorem`.

```lean
theorem ContinuousCohomology.TopologicallySplitShortExact.exact_map_i_map_p {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {A B C : TopRep k G} (S : TopologicallySplitShortExact A B C) [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] [C.JointlyContinuous] : Function.Exact ⇑(TopModuleCat.Hom.hom (map (ContinuousMonoidHom.id G) S.i 1)) ⇑(TopModuleCat.Hom.hom (map (ContinuousMonoidHom.id G) S.p 1))
```

**Native source docstring:** Exactness at the second native continuous-cohomology term.

[Source](../ContinuousGroupCohomology/LowDegreeExact.lean#L618) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.Mackey

71 native named entries; 2 native instance-table rows.

#### ContinuousCohomology.CorestrictionTransversal.innerConjCrossed_formula

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.innerConjCrossed_formula {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] (X : TopRep k G) (H : OpenSubgroup G) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (h a : ↥H) : (X.ρ (↑h)⁻¹) (↑f (h * a * h⁻¹)) = ↑f a - (((TopRep.res (↑H).subtype X).ρ a) ((X.ρ (↑h)⁻¹) (↑f h)) - (X.ρ (↑h)⁻¹) (↑f h))
```

**Native source docstring:** Conjugating a crossed homomorphism by an element of its group changes it
by the negative of a principal crossed homomorphism, in the repository's
positive-principal convention.

[Source](../ContinuousGroupCohomology/Mackey.lean#L47) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateRightTransversal

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.conjugateRightTransversal {K : Type u_1} [Group K] (L : Subgroup K) (T : L.RightTransversal) (b : K) : (Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj b)) L).RightTransversal
```

**Native source docstring:** Transport a right transversal across conjugation of its subgroup.
Its carrier condition computes in the conjugation equivalence.

[Source](../ContinuousGroupCohomology/Mackey.lean#L82) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateTransversalEquiv

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.conjugateTransversalEquiv {K : Type u_1} [Group K] (L : Subgroup K) (T : L.RightTransversal) (b : K) : ↑↑(conjugateRightTransversal L T b) ≃ ↑↑T
```

**Native source docstring:** Multiplication by the conjugating element identifies the transported and
original right transversals. The equivalence computes on representatives.

[Source](../ContinuousGroupCohomology/Mackey.lean#L130) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateTransversalEquiv_coe

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.conjugateTransversalEquiv_coe {K : Type u_1} [Group K] (L : Subgroup K) (T : L.RightTransversal) (b : K) (t : ↑↑(conjugateRightTransversal L T b)) : ↑((conjugateTransversalEquiv L T b) t) = b * ↑t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `conjugateTransversalEquiv_coe` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L147) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateTransversal_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.conjugateTransversal_factor {K : Type u_1} [Group K] (L : Subgroup K) (T : L.RightTransversal) (b : K) (t : ↑↑(conjugateRightTransversal L T b)) (g : K) : b * ↑(factor (conjugateRightTransversal L T b) t g) * b⁻¹ = ↑(factor T ((conjugateTransversalEquiv L T b) t) g)
```

**Native source docstring:** The factors for conjugated right transversals agree after conjugation.

[Source](../ContinuousGroupCohomology/Mackey.lean#L152) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateTransversal_next

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.conjugateTransversal_next {K : Type u_1} [Group K] (L : Subgroup K) (T : L.RightTransversal) (b : K) (t : ↑↑(conjugateRightTransversal L T b)) (g : K) : (conjugateTransversalEquiv L T b) (next (conjugateRightTransversal L T b) t g) = next T ((conjugateTransversalEquiv L T b) t) g
```

**Native source docstring:** The next representatives for conjugated right transversals agree under the
transport equivalence.

[Source](../ContinuousGroupCohomology/Mackey.lean#L182) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyStabilizer

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyStabilizer {G : Type v} [Group G] (H K₀ : Subgroup G) (x : G) : Subgroup ↥K₀
```

**Native source docstring:** The subgroup of `K₀` stabilizing the right `H`-coset represented by `x`.
Its membership predicate computes in the open-stabilizer comparison.

[Source](../ContinuousGroupCohomology/Mackey.lean#L216) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyStabilizer_mul_left_mul_right

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyStabilizer_mul_left_mul_right {G : Type v} [Group G] (H K₀ : Subgroup G) (x : G) (h : ↥H) (b : ↥K₀) : mackeyStabilizer H K₀ (↑h * x * ↑b) = Subgroup.comap (MulEquiv.toMonoidHom (MulAut.conj b)) (mackeyStabilizer H K₀ x)
```

**Native source docstring:** Changing a double-coset representative by `h * x * b` conjugates its
stabilizer by `b` inside the right-hand subgroup.

[Source](../ContinuousGroupCohomology/Mackey.lean#L223) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.conjugateTransferSummand_formula

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.conjugateTransferSummand_formula {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (X : TopRep k G) (b s : G) (z : ↑X) : (X.ρ (b⁻¹ * s)⁻¹) ((X.ρ b⁻¹) z) = (X.ρ s⁻¹) z
```

**Native source docstring:** The coefficient action in the conjugated transfer summand has the literal
order needed for finite reindexing.

[Source](../ContinuousGroupCohomology/Mackey.lean#L255) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugationHom

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyConjugationHom {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : OpenSubgroup G) (x : G) : ↥K →ₜ* G
```

**Native source docstring:** Conjugation by `x`, restricted to the right-hand open subgroup.
Its value computes when using stabilizer membership.

[Source](../ContinuousGroupCohomology/Mackey.lean#L263) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) : OpenSubgroup ↥K
```

**Native source docstring:** The open stabilizer in `K` of the right `H`-coset represented by `x`.
Its underlying subgroup computes as the Mackey stabilizer.

[Source](../ContinuousGroupCohomology/Mackey.lean#L271) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer_toSubgroup

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer_toSubgroup {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) : ↑(mackeyOpenStabilizer H K x) = mackeyStabilizer (↑H) (↑K) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyOpenStabilizer_toSubgroup` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L277) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizerFiniteIndex

Kind: `instance`.

```lean
instance ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizerFiniteIndex {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) [(↑H).FiniteIndex] : (↑(mackeyOpenStabilizer H K x)).FiniteIndex
```

**Native source docstring:** The Mackey stabilizer has finite index in `K` as soon as `H` has finite
index in the ambient group.

[Source](../ContinuousGroupCohomology/Mackey.lean#L282) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.jointlyContinuous_mackeyStabilizer

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.jointlyContinuous_mackeyStabilizer {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] : (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X)).JointlyContinuous
```

**Native source docstring:** Joint continuity of the coefficient action persists upon restriction to a
Mackey stabilizer. This reuses the existing private local proof without adding
an instance to the API seen by importers.

[Source](../ContinuousGroupCohomology/Mackey.lean#L308) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyStabilizerToLeft

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyStabilizerToLeft {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) : ↥(mackeyOpenStabilizer H K x) →ₜ* ↥H
```

**Native source docstring:** Conjugation identifies a Mackey stabilizer with a subgroup of `H`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L320) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) →L[k] ↥(continuousCrossedHom (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X)))
```

**Native source docstring:** Conjugate and restrict a crossed homomorphism from `H` to the stabilizer
of the right `H`-coset represented by `x`. Its application computes by
conjugating the input cocycle.

[Source](../ContinuousGroupCohomology/Mackey.lean#L338) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (l : ↥(mackeyOpenStabilizer H K x)) : ↑((mackeyConjugateCrossed X H K x) f) l = (X.ρ x⁻¹) (↑f ((mackeyStabilizerToLeft H K x) l))
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mackeyConjugateCrossed_apply` for the double-coset decomposition of continuous degree-one transfer; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Mackey.lean#L375) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_principal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_principal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] (c : ↑X) : (mackeyConjugateCrossed X H K x) ((principalToCrossed (TopRep.res (↑H).subtype X)) c) = (principalToCrossed (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))) ((X.ρ x⁻¹) c)
```

**Native source docstring:** Conjugation and restriction send principal crossed homomorphisms to
principal crossed homomorphisms with the conjugated coefficient.

[Source](../ContinuousGroupCohomology/Mackey.lean#L382) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateQuotient

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyConjugateQuotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))) ⧸ principalCocycles (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))
```

**Native source docstring:** Conjugation and restriction descend to crossed homomorphisms modulo
principal crossed homomorphisms. Its lift computes on representatives.

[Source](../ContinuousGroupCohomology/Mackey.lean#L399) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateQuotient_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyConjugateQuotient_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (mackeyConjugateQuotient X H K x) ((principalCocycles (TopRep.res (↑H).subtype X)).mkQ f) = (principalCocycles (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).mkQ ((mackeyConjugateCrossed X H K x) f)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mackeyConjugateQuotient_mk` for the double-coset decomposition of continuous degree-one transfer; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Mackey.lean#L429) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyTransferCrossedWithTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyTransferCrossedWithTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) : ↥(continuousCrossedHom (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype X))
```

**Native source docstring:** Transfer from a Mackey stabilizer to `K`, with the finite-index witness
obtained from the ambient finite index of `H`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L440) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype X)) ⧸ principalCocycles (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The quotient-level Mackey summand attached to `x`, computed with a chosen
right transversal of its stabilizer in `K`. Its lift computes on cocycles.

[Source](../ContinuousGroupCohomology/Mackey.lean#L453) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_eq

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_eq {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (T S : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] : mackeySummandQuotientWithTransversal X H K x T = mackeySummandQuotientWithTransversal X H K x S
```

**Native source docstring:** A Mackey summand on crossed-homomorphism quotients is independent of the
right transversal used for its stabilizer.

[Source](../ContinuousGroupCohomology/Mackey.lean#L469) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype X)) ⧸ principalCocycles (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The quotient-level Mackey summand attached to an ambient representative.
Its apparent dependence on the representative is removed below by the
double-coset representative-change argument.

[Source](../ContinuousGroupCohomology/Mackey.lean#L482) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient_eq_withTransversal

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient_eq_withTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] : mackeySummandQuotient X H K x = mackeySummandQuotientWithTransversal X H K x T
```

**Native source docstring:** The canonical Mackey summand can be computed from any stabilizer
transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L495) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (mackeySummandQuotientWithTransversal X H K x T) ((principalCocycles (TopRep.res (↑H).subtype X)).mkQ f) = (principalCocycles (TopRep.res (↑K).subtype X)).mkQ ((mackeyTransferCrossedWithTransversal X H K x T) ((mackeyConjugateCrossed X H K x) f))
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mackeySummandQuotientWithTransversal_mk` for the double-coset decomposition of continuous degree-one transfer; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Mackey.lean#L507) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupConjugationHom

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.openSubgroupConjugationHom {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : OpenSubgroup G) (b : ↥K) : ↥K →ₜ* ↥K
```

**Native source docstring:** Conjugation by an element of an open subgroup, as a continuous
endomorphism of that open subgroup. It computes pointwise by conjugation.

[Source](../ContinuousGroupCohomology/Mackey.lean#L521) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.openSubgroupConjugationHom_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.openSubgroupConjugationHom_apply {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : OpenSubgroup G) (b l : ↥K) : (openSubgroupConjugationHom K b) l = b * l * b⁻¹
```

**Original catalogue explanation (not a Lean docstring):** The named computation `openSubgroupConjugationHom_apply` for the double-coset decomposition of continuous degree-one transfer; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Mackey.lean#L528) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer_mul_left_mul_right

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizer_mul_left_mul_right {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) : mackeyOpenStabilizer H K (↑h * x * ↑b) = OpenSubgroup.comap ↑(openSubgroupConjugationHom K b) ⋯ (mackeyOpenStabilizer H K x)
```

**Native source docstring:** The open Mackey stabilizer transforms by conjugation under a change of
ambient representative.

[Source](../ContinuousGroupCohomology/Mackey.lean#L532) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeRightTransversal

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeRightTransversal {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) : (↑(mackeyOpenStabilizer H K (↑h * x * ↑b))).RightTransversal
```

**Native source docstring:** The right transversal used after changing an ambient representative by
`h * x * b`. It computes as the conjugate transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L549) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversalEquiv

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversalEquiv {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) : ↑↑(mackeyRepresentativeRightTransversal H K x h b T) ≃ ↑↑T
```

**Native source docstring:** Multiplication by `b` identifies the changed-representative transversal
with the original stabilizer transversal. Its application computes to the
translated representative.

[Source](../ContinuousGroupCohomology/Mackey.lean#L562) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversalEquiv_coe

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversalEquiv_coe {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) (t : ↑↑(mackeyRepresentativeRightTransversal H K x h b T)) : ↑((mackeyRepresentativeTransversalEquiv H K x h b T) t) = b * ↑t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyRepresentativeTransversalEquiv_coe` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L574) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_factor {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) (t : ↑↑(mackeyRepresentativeRightTransversal H K x h b T)) (g : ↥K) : b * ↑(factor (mackeyRepresentativeRightTransversal H K x h b T) t g) * b⁻¹ = ↑(factor T ((mackeyRepresentativeTransversalEquiv H K x h b T) t) g)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyRepresentativeTransversal_factor` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L582) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_next

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeTransversal_next {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) (t : ↑↑(mackeyRepresentativeRightTransversal H K x h b T)) (g : ↥K) : (mackeyRepresentativeTransversalEquiv H K x h b T) (next (mackeyRepresentativeRightTransversal H K x h b T) t g) = next T ((mackeyRepresentativeTransversalEquiv H K x h b T) t) g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyRepresentativeTransversal_next` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L618) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentative_transferTerm

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyRepresentative_transferTerm {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (t : ↑↑(mackeyRepresentativeRightTransversal H K x h b T)) (g : ↥K) : ((TopRep.res (↑K).subtype X).ρ (↑t)⁻¹) (↑((mackeyConjugateCrossed X H K (↑h * x * ↑b)) f) (factor (mackeyRepresentativeRightTransversal H K x h b T) t g)) = ((TopRep.res (↑K).subtype X).ρ (↑((mackeyRepresentativeTransversalEquiv H K x h b T) t))⁻¹) (↑((mackeyConjugateCrossed X H K x) f) (factor T ((mackeyRepresentativeTransversalEquiv H K x h b T) t) g)) - ((TopRep.res (↑K).subtype X).ρ (↑((mackeyRepresentativeTransversalEquiv H K x h b T) t))⁻¹) (↑((principalToCrossed (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))) ((X.ρ x⁻¹) ((X.ρ (↑h)⁻¹) (↑f h)))) (factor T ((mackeyRepresentativeTransversalEquiv H K x h b T) t) g))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyRepresentative_transferTerm` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L655) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeCoefficient

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyRepresentativeCoefficient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (h : ↥H) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : ↑X
```

**Native source docstring:** The coefficient of the principal defect caused by changing the ambient
Mackey representative on the left.

[Source](../ContinuousGroupCohomology/Mackey.lean#L741) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyTransferCrossed_mul_left_mul_right

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyTransferCrossed_mul_left_mul_right {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (mackeyTransferCrossedWithTransversal X H K (↑h * x * ↑b) (mackeyRepresentativeRightTransversal H K x h b T)) ((mackeyConjugateCrossed X H K (↑h * x * ↑b)) f) = (mackeyTransferCrossedWithTransversal X H K x T) ((mackeyConjugateCrossed X H K x) f) - (principalToCrossed (TopRep.res (↑K).subtype X)) (mackeyRepresentativeCoefficient X H K x h T f)
```

**Native source docstring:** Changing an ambient Mackey representative from `x` to `h * x * b`, and
transporting the stabilizer transversal accordingly, changes the transferred
crossed homomorphism by one principal crossed homomorphism.

[Source](../ContinuousGroupCohomology/Mackey.lean#L753) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_mul_left_mul_right

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotientWithTransversal_mul_left_mul_right {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (h : ↥H) (b : ↥K) (T : (↑(mackeyOpenStabilizer H K x)).RightTransversal) [X.JointlyContinuous] : mackeySummandQuotientWithTransversal X H K (↑h * x * ↑b) (mackeyRepresentativeRightTransversal H K x h b T) = mackeySummandQuotientWithTransversal X H K x T
```

**Native source docstring:** Representative change is invisible on the quotient when the changed
stabilizer uses the transported transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L841) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient_mul_left_mul_right

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeySummandQuotient_mul_left_mul_right {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (x : G) (h : ↥H) (b : ↥K) [X.JointlyContinuous] : mackeySummandQuotient X H K (↑h * x * ↑b) = mackeySummandQuotient X H K x
```

**Native source docstring:** The canonical quotient-level Mackey summand depends only on the ambient
double coset represented by `x`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L874) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetFinite

Kind: `instance`.

```lean
instance ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetFinite {G : Type v} [Group G] [TopologicalSpace G] (H K : OpenSubgroup G) [(↑H).FiniteIndex] : Finite (DoubleCoset.Quotient ↑H ↑K)
```

**Native source docstring:** A finite left index gives finitely many double cosets.

[Source](../ContinuousGroupCohomology/Mackey.lean#L892) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSummand

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSummand {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] (q : DoubleCoset.Quotient ↑H ↑K) : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype X)) ⧸ principalCocycles (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The representative-independent quotient-level summand attached to a
double coset. It computes on canonical representatives.

[Source](../ContinuousGroupCohomology/Mackey.lean#L907) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSummand_mk

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSummand_mk {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] (x : G) : mackeyDoubleCosetSummand X H K (DoubleCoset.mk (↑H) (↑K) x) = mackeySummandQuotient X H K x
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mackeyDoubleCosetSummand_mk` for the double-coset decomposition of continuous degree-one transfer; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/Mackey.lean#L924) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSum

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetSum {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X)) ⧸ principalCocycles (TopRep.res (↑H).subtype X) →L[k] ↥(continuousCrossedHom (TopRep.res (↑K).subtype X)) ⧸ principalCocycles (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The finite sum of the quotient-level summands over `H \ G / K`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L933) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentative

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentative {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (p : (q : DoubleCoset.Quotient ↑H ↑K) × Subtype ↑(T q)) : G
```

**Native source docstring:** The ambient representative attached to a double coset and a representative
of a right coset of its Mackey stabilizer. Its product formula is used by the
assembled-transversal membership calculation.

[Source](../ContinuousGroupCohomology/Mackey.lean#L945) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRightTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRightTransversal {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) : (↑H).RightTransversal
```

**Native source docstring:** Double-coset representatives followed by stabilizer transversals assemble
to a right transversal of `H` in the ambient group. Its carrier computes as
the range of assembled representatives.

[Source](../ContinuousGroupCohomology/Mackey.lean#L955) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentativeMem

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentativeMem {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (q : DoubleCoset.Quotient ↑H ↑K) (t : Subtype ↑(T q)) : Subtype ↑(mackeyAssembledRightTransversal H K T)
```

**Native source docstring:** A double-coset representative followed by a local representative, viewed
inside the assembled ambient transversal. Its ambient value computes as a
product of representatives.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1066) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentativeMem_coe

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyAssembledRepresentativeMem_coe {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (q : DoubleCoset.Quotient ↑H ↑K) (t : Subtype ↑(T q)) : ↑(mackeyAssembledRepresentativeMem H K T q t) = Quotient.out q * ↑↑t
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `mackeyAssembledRepresentativeMem_coe` in the double-coset decomposition of continuous degree-one transfer; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1078) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembled_factor

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyAssembled_factor {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (q : DoubleCoset.Quotient ↑H ↑K) (t : Subtype ↑(T q)) (g : ↥K) : factor (mackeyAssembledRightTransversal H K T) (mackeyAssembledRepresentativeMem H K T q t) ↑g = ⟨Quotient.out q * ↑↑(factor (T q) t g) * (Quotient.out q)⁻¹, ⋯⟩
```

**Native source docstring:** The factor in the assembled ambient transversal is the conjugate of the
factor in the corresponding stabilizer transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1087) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembled_next

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyAssembled_next {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (q : DoubleCoset.Quotient ↑H ↑K) (t : Subtype ↑(T q)) (g : ↥K) : next (mackeyAssembledRightTransversal H K T) (mackeyAssembledRepresentativeMem H K T q t) ↑g = mackeyAssembledRepresentativeMem H K T q (next (T q) t g)
```

**Native source docstring:** The next representative in the assembled ambient transversal retains the
double coset and applies the local next-representative operation.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1137) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyAssembledTransversalEquiv

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyAssembledTransversalEquiv {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) : (q : DoubleCoset.Quotient ↑H ↑K) × Subtype ↑(T q) ≃ Subtype ↑(mackeyAssembledRightTransversal H K T)
```

**Native source docstring:** The sigma type of double cosets and local transversal representatives is
equivalent to the assembled ambient transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1185) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyCrossedSumWithTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyCrossedSumWithTransversal {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : ↥(continuousCrossedHom (TopRep.res (↑K).subtype X))
```

**Native source docstring:** The crossed-homomorphism sum of the Mackey stabilizer transfers, computed
from a chosen family of local right transversals.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1228) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferCrossed_mackey_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferCrossed_mackey_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) (g : ↥K) : ↑((transferCrossed X H (mackeyAssembledRightTransversal H K T)) f) ↑g = ↑(mackeyCrossedSumWithTransversal X H K T f) g
```

**Native source docstring:** Restricting a transfer computed with the assembled transversal is the sum
of the transfers from the Mackey stabilizers, at the crossed-homomorphism
level.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1241) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedRestrict_transferCrossed_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedRestrict_transferCrossed_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] (T : (q : DoubleCoset.Quotient ↑H ↑K) → (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal) (f : ↥(continuousCrossedHom (TopRep.res (↑H).subtype X))) : (crossedRestrict X K) ((transferCrossed X H (mackeyAssembledRightTransversal H K T)) f) = mackeyCrossedSumWithTransversal X H K T f
```

**Native source docstring:** Crossed-homomorphism form of the degree-one Mackey decomposition for the
assembled ambient transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1331) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyStabilizerRightTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyStabilizerRightTransversal {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) [(↑H).FiniteIndex] (q : DoubleCoset.Quotient ↑H ↑K) : (↑(mackeyOpenStabilizer H K (Quotient.out q))).RightTransversal
```

**Native source docstring:** A canonical right transversal for each Mackey stabilizer.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1344) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyRightTransversal

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyRightTransversal {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K : OpenSubgroup G) [(↑H).FiniteIndex] : (↑H).RightTransversal
```

**Native source docstring:** The ambient right transversal assembled from canonical double-coset
representatives and canonical stabilizer transversals.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1352) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict_comp_transferQuotient_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.crossedQuotientRestrict_comp_transferQuotient_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] : crossedQuotientRestrict X K ∘SL transferQuotient X H (mackeyRightTransversal H K) = mackeyDoubleCosetSum X H K
```

**Native source docstring:** Quotient-level degree-one Mackey formula.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1359) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_crossedQuotientRestrict_mackey_hom

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_crossedQuotientRestrict_mackey_hom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient X H (mackeyRightTransversal H K))) (TopModuleCat.ofHom (crossedQuotientRestrict X K)) = TopModuleCat.ofHom (mackeyDoubleCosetSum X H K)
```

**Native source docstring:** Categorical form of the quotient-level Mackey formula.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1428) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_crossedQuotientRestrict_mackey_hom_assoc

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.transferQuotient_comp_crossedQuotientRestrict_mackey_hom_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] {Z : TopModuleCat k} (h : ↧(↥(continuousCrossedHom (TopRep.res (↑K).subtype X)) ⧸ principalCocycles (TopRep.res (↑K).subtype X)) ⟶ Z) : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient X H (mackeyRightTransversal H K))) (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (crossedQuotientRestrict X K)) h) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (mackeyDoubleCosetSum X H K)) h
```

**Native source docstring:** Categorical form of the quotient-level Mackey formula.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1429) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyCoefficientHom

Kind: `def`.

```lean
def ContinuousCohomology.CorestrictionTransversal.mackeyCoefficientHom {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) : TopRep.res (↑(mackeyStabilizerToLeft H K x)) (TopRep.res (↑H).subtype X) ⟶ TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The coefficient comparison for the conjugation map from a Mackey
stabilizer to the left subgroup.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1440) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.cochainsMap_one_apply

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.cochainsMap_one_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] {A : TopRep k G} {B : TopRep k J} (phi : J →ₜ* G) (f : TopRep.res (↑phi) A ⟶ B) (sigma : ↑(A.homogeneousCochains.X 1).toModuleCat) (h : J) : (↑((CategoryTheory.ConcreteCategory.hom ((cochainsMap phi f).f 1)) sigma) 1) h = (TopRep.Hom.hom f) ((↑sigma 1) (phi h))
```

**Native source docstring:** Evaluation in degree one of the homogeneous-cochain map induced by a group
homomorphism and compatible coefficient morphism.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1460) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.cocyclesOneCrossedIso_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(mackeyOpenStabilizer H K x)] : CategoryTheory.CategoryStruct.comp (cocyclesMap (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1) (cocyclesOneCrossedIso (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).hom = CategoryTheory.CategoryStruct.comp (cocyclesOneCrossedIso (TopRep.res (↑H).subtype X)).hom (TopModuleCat.ofHom (mackeyConjugateCrossed X H K x))
```

**Native source docstring:** The explicit conjugation/restriction map on crossed homomorphisms agrees
with the map induced on degree-one cocycles.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1484) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_comp_mkQL

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyConjugateCrossed_comp_mkQL {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (mackeyConjugateCrossed X H K x)) (TopModuleCat.ofHom (principalCocycles (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).mkQL) = CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (principalCocycles (TopRep.res (↑H).subtype X)).mkQL) (TopModuleCat.ofHom (mackeyConjugateQuotient X H K x))
```

**Native source docstring:** The crossed-homomorphism conjugation map commutes with passage to principal
cocycle quotients.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1528) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.homologyQuotientIso_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(mackeyOpenStabilizer H K x)] : CategoryTheory.CategoryStruct.comp (map (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1) (homologyQuotientIso (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).hom = CategoryTheory.CategoryStruct.comp (homologyQuotientIso (TopRep.res (↑H).subtype X)).hom (TopModuleCat.ofHom (mackeyConjugateQuotient X H K x))
```

**Native source docstring:** The native cohomology map induced by conjugation and coefficient transport
agrees with the conjugation map on crossed-homomorphism quotients.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1545) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.degreeOneIso_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.degreeOneIso_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(mackeyOpenStabilizer H K x)] : CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (mackeyConjugateQuotient X H K x)) (degreeOneIso (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).hom = CategoryTheory.CategoryStruct.comp (degreeOneIso (TopRep.res (↑H).subtype X)).hom (map (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1)
```

**Native source docstring:** Conjugation and restriction commute with the crossed-quotient-to-degree-one
cohomology comparison.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1640) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.map_comp_degreeOneIso_inv_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.map_comp_degreeOneIso_inv_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) (x : G) [X.JointlyContinuous] [LocallyCompactSpace ↥H] [LocallyCompactSpace ↥K] [LocallyCompactSpace ↥(mackeyOpenStabilizer H K x)] : CategoryTheory.CategoryStruct.comp (map (mackeyStabilizerToLeft H K x) (mackeyCoefficientHom X H K x) 1) (degreeOneIso (TopRep.res (↑(mackeyOpenStabilizer H K x)).subtype (TopRep.res (↑K).subtype X))).inv = CategoryTheory.CategoryStruct.comp (degreeOneIso (TopRep.res (↑H).subtype X)).inv (TopModuleCat.ofHom (mackeyConjugateQuotient X H K x))
```

**Native source docstring:** A reassociated inverse form of `degreeOneIso_mackey`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1663) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_eq_degreeOne

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_eq_degreeOne {k : Type u} [Ring k] [TopologicalSpace k] {J : Type v} [Group J] [TopologicalSpace J] [IsTopologicalGroup J] (Y : TopRep k J) (L : OpenSubgroup J) [(↑L).FiniteIndex] [Y.JointlyContinuous] [LocallyCompactSpace J] [LocallyCompactSpace ↥L] : corestrictionOne Y L = CategoryTheory.CategoryStruct.comp (degreeOneIso (TopRep.res (↑L).subtype Y)).inv (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (transferQuotient Y L default)) (degreeOneIso Y).hom)
```

**Native source docstring:** Canonical degree-one corestriction unfolds through the crossed-quotient
comparison and the canonical stabilizer transversal.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1682) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSummand

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSummand {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] (q : DoubleCoset.Quotient ↑H ↑K) : continuousCohomology 1 (TopRep.res (↑H).subtype X) ⟶ continuousCohomology 1 (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The native degree-one summand attached to a double coset: conjugate and
restrict to its Mackey stabilizer, then corestrict to the right subgroup.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1695) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSummand_eq_quotient

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSummand_eq_quotient {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] (q : DoubleCoset.Quotient ↑H ↑K) : have x := ⋯; have x_1 := ⋯; mackeyDoubleCosetOneSummand X H K q = CategoryTheory.CategoryStruct.comp (degreeOneIso (TopRep.res (↑H).subtype X)).inv (CategoryTheory.CategoryStruct.comp (TopModuleCat.ofHom (mackeyDoubleCosetSummand X H K q)) (degreeOneIso (TopRep.res (↑K).subtype X)).hom)
```

**Native source docstring:** The native double-coset summand agrees with the representative-independent
crossed-quotient summand transported through the degree-one comparison.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1714) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSum

Kind: `def`.

```lean
noncomputable def ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSum {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] : continuousCohomology 1 (TopRep.res (↑H).subtype X) ⟶ continuousCohomology 1 (TopRep.res (↑K).subtype X)
```

**Native source docstring:** The finite native degree-one Mackey sum over `H \\ G / K`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1775) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSum_eq_sum

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetOneSum_eq_sum {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] : mackeyDoubleCosetOneSum X H K = Finset.univ.sum (mackeyDoubleCosetOneSummand X H K)
```

**Native source docstring:** The native Mackey sum is the finite sum of its double-coset summands.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1788) (native source start line; generated entries may point to their parent).

#### ContinuousCohomology.CorestrictionTransversal.corestrictionOne_comp_restriction_mackey

Kind: `theorem`.

```lean
theorem ContinuousCohomology.CorestrictionTransversal.corestrictionOne_comp_restriction_mackey {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (H K : OpenSubgroup G) [(↑H).FiniteIndex] [X.JointlyContinuous] [LocallyCompactSpace G] : have x := ⋯; have x_1 := ⋯; CategoryTheory.CategoryStruct.comp (corestrictionOne X H) (map (openSubgroupInclusion K) (restrictionCoeffHom X K) 1) = mackeyDoubleCosetOneSum X H K
```

**Native source docstring:** Restriction to `K` after canonical corestriction from `H` is the finite
degree-one Mackey sum over `H \\ G / K`.

[Source](../ContinuousGroupCohomology/Mackey.lean#L1839) (native source start line; generated entries may point to their parent).

#### Native instance table

- `ContinuousCohomology.CorestrictionTransversal.mackeyDoubleCosetFinite`: `Finite`; type names: `DoubleCoset.Quotient`

- `ContinuousCohomology.CorestrictionTransversal.mackeyOpenStabilizerFiniteIndex`: `Subgroup.FiniteIndex`; type names: `OpenSubgroup.toSubgroup`

### ContinuousGroupCohomology.NestedInvariants

9 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.nestedQuotientInvariantsEquiv

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.nestedQuotientInvariantsEquiv {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) : ↥(Representation.invariants (MonoidHom.comp (A.quotientToInvariants S).ρ (Subgroup.map (QuotientGroup.mk' S) T).subtype)) ≃ₗ[R] ↥(Representation.invariants (MonoidHom.comp A.ρ T.subtype))
```

**Native source docstring:** Taking invariants under `T / S` after taking invariants under `S` agrees
with taking invariants under `T`.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L34) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_apply_val

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_apply_val {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (x : ↥(Representation.invariants (MonoidHom.comp (A.quotientToInvariants S).ρ (Subgroup.map (QuotientGroup.mk' S) T).subtype))) : ↑((nestedQuotientInvariantsEquiv A S T hST) x) = ↑↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `nestedQuotientInvariantsEquiv_apply_val` in iterated invariants under a normal subgroup and its quotient; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L64) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_symm_apply_val

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsEquiv_symm_apply_val {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (x : ↥(Representation.invariants (MonoidHom.comp A.ρ T.subtype))) : ↑↑((nestedQuotientInvariantsEquiv A S T hST).symm x) = ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `nestedQuotientInvariantsEquiv_symm_apply_val` in iterated invariants under a normal subgroup and its quotient; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L71) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepIso

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.nestedQuotientInvariantsRepIso {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) : (A.quotientToInvariants S).quotientToInvariants (Subgroup.map (QuotientGroup.mk' S) T) ≅ Rep.res (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (A.quotientToInvariants T)
```

**Native source docstring:** The nested-invariants equivalence is equivariant after the third
isomorphism theorem identifies the two quotient groups.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L77) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_hom_apply_val

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_hom_apply_val {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (x : ↑((A.quotientToInvariants S).quotientToInvariants (Subgroup.map (QuotientGroup.mk' S) T))) : ↑((CategoryTheory.ConcreteCategory.hom (nestedQuotientInvariantsRepIso A S T hST).hom) x) = ↑↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `nestedQuotientInvariantsRepIso_hom_apply_val` in iterated invariants under a normal subgroup and its quotient; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L95) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_naturality

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_naturality {R : Type u} [CommRing R] {G : Type v} [Group G] {A B : Rep R G} (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) : CategoryTheory.CategoryStruct.comp ((Rep.quotientToInvariantsFunctor R (Subgroup.map (QuotientGroup.mk' S) T)).map ((Rep.quotientToInvariantsFunctor R S).map f)) (nestedQuotientInvariantsRepIso B S T hST).hom = CategoryTheory.CategoryStruct.comp (nestedQuotientInvariantsRepIso A S T hST).hom ((Rep.resFunctor (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom).map ((Rep.quotientToInvariantsFunctor R T).map f))
```

**Native source docstring:** The nested-invariants representation isomorphism is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L102) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_naturality_assoc

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsRepIso_naturality_assoc {R : Type u} [CommRing R] {G : Type v} [Group G] {A B : Rep R G} (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) {Z : Rep R ((G ⧸ S) ⧸ Subgroup.map (QuotientGroup.mk' S) T)} (h : Rep.res (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (B.quotientToInvariants T) ⟶ Z) : CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp ((Rep.quotientToInvariantsFunctor R (Subgroup.map (QuotientGroup.mk' S) T)).map ((Rep.quotientToInvariantsFunctor R S).map f)) (nestedQuotientInvariantsRepIso B S T hST).hom) h = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (nestedQuotientInvariantsRepIso A S T hST).hom (Rep.resMap (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom ((Rep.quotientToInvariantsFunctor R T).map f))) h
```

**Native source docstring:** The nested-invariants representation isomorphism is natural in the
coefficient representation.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L104) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepNatTrans

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.nestedQuotientInvariantsRepNatTrans {R : Type u} [CommRing R] {G : Type v} [Group G] (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) : (Rep.quotientToInvariantsFunctor R S).comp (Rep.quotientToInvariantsFunctor R (Subgroup.map (QuotientGroup.mk' S) T)) ⟶ (Rep.quotientToInvariantsFunctor R T).comp (Rep.resFunctor (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom)
```

**Native source docstring:** The natural transformation from iterated invariants to direct invariants,
after restriction along the third-isomorphism equivalence.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L117) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.nestedQuotientInvariantsRepNatTrans_app

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.nestedQuotientInvariantsRepNatTrans_app {R : Type u} [CommRing R] {G : Type v} [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) : (nestedQuotientInvariantsRepNatTrans S T hST).app A = (nestedQuotientInvariantsRepIso A S T hST).hom
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `nestedQuotientInvariantsRepNatTrans_app` in iterated invariants under a normal subgroup and its quotient; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/NestedInvariants.lean#L130) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.NormalizedCohomology

9 native named entries; 0 native instance-table rows.

#### TopRep.normalized

Kind: `def`.

```lean
abbrev TopRep.normalized {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] (X : TopRep k G) : TopRep k (ULift.{max v w, v} G)
```

**Native source docstring:** Raise both the acting group and coefficient carrier of a topological
representation into their canonical common maximum universe.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L38) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedFunctor

Kind: `def`.

```lean
abbrev TopRep.normalizedFunctor {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] : CategoryTheory.Functor (TopRep k G) (TopRep k (ULift.{max v w, v} G))
```

**Native source docstring:** The functor raising a topological representation into the canonical
common maximum of its fixed group and coefficient universes.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L44) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedMap

Kind: `def`.

```lean
abbrev TopRep.normalizedMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] {X Y : TopRep k G} (f : X ⟶ Y) : X.normalized ⟶ Y.normalized
```

**Native source docstring:** Raise a coefficient morphism into the canonical common maximum universe.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L50) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedHomogeneousCochains

Kind: `def`.

```lean
abbrev TopRep.normalizedHomogeneousCochains {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) : CochainComplex (TopModuleCat k) ℕ
```

**Native source docstring:** Homogeneous continuous cochains after canonical common-universe
normalization.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L55) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedContinuousCohomology

Kind: `def`.

```lean
noncomputable abbrev TopRep.normalizedContinuousCohomology {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : TopModuleCat k
```

**Native source docstring:** Continuous cohomology after canonical common-universe normalization.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L61) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedContinuousCohomologyMap

Kind: `def`.

```lean
noncomputable def TopRep.normalizedContinuousCohomologyMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y : TopRep k G} (f : X ⟶ Y) (n : ℕ) : X.normalizedContinuousCohomology n ⟶ Y.normalizedContinuousCohomology n
```

**Native source docstring:** The map on normalized continuous cohomology induced by a coefficient
morphism for a fixed acting group.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L66) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedContinuousCohomologyMap_id

Kind: `theorem`.

```lean
theorem TopRep.normalizedContinuousCohomologyMap_id {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) (n : ℕ) : normalizedContinuousCohomologyMap (CategoryTheory.CategoryStruct.id X) n = CategoryTheory.CategoryStruct.id (X.normalizedContinuousCohomology n)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `normalizedContinuousCohomologyMap_id` for normalization of continuous cohomology and its coefficient maps; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L75) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedContinuousCohomologyMap_comp

Kind: `theorem`.

```lean
theorem TopRep.normalizedContinuousCohomologyMap_comp {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y Z : TopRep k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) : normalizedContinuousCohomologyMap (CategoryTheory.CategoryStruct.comp f g) n = CategoryTheory.CategoryStruct.comp (normalizedContinuousCohomologyMap f n) (normalizedContinuousCohomologyMap g n)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `normalizedContinuousCohomologyMap_comp` for normalization of continuous cohomology and its coefficient maps; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L95) (native source start line; generated entries may point to their parent).

#### TopRep.normalizedContinuousCohomologyMap_comp_assoc

Kind: `theorem`.

```lean
theorem TopRep.normalizedContinuousCohomologyMap_comp_assoc {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {X Y Z : TopRep k G} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) {Z✝ : TopModuleCat k} (h : Z.normalizedContinuousCohomology n ⟶ Z✝) : CategoryTheory.CategoryStruct.comp (normalizedContinuousCohomologyMap (CategoryTheory.CategoryStruct.comp f g) n) h = CategoryTheory.CategoryStruct.comp (normalizedContinuousCohomologyMap f n) (CategoryTheory.CategoryStruct.comp (normalizedContinuousCohomologyMap g n) h)
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated reassociated statement associated with `TopRep.normalizedContinuousCohomologyMap_comp` in normalization of continuous cohomology and its coefficient maps; the original `@[reassoc]` source anchor is shown below.

[Source](../ContinuousGroupCohomology/NormalizedCohomology.lean#L95) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.QuotientConjugationAction

11 native named entries; 0 native instance-table rows.

#### GroupExtension.conjActAbelianization

Kind: `def`.

```lean
noncomputable def GroupExtension.conjActAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) : E →* MulAut (Abelianization N)
```

**Native source docstring:** The conjugation action of the middle group on the abelianization of the
kernel of a group extension.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L47) (native source start line; generated entries may point to their parent).

#### GroupExtension.conjActAbelianization_apply_of

Kind: `theorem`.

```lean
theorem GroupExtension.conjActAbelianization_apply_of {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) (e : E) (n : N) : (S.conjActAbelianization e) (Abelianization.of n) = Abelianization.of ((S.conjAct e) n)
```

**Native source docstring:** Abelianized conjugation sends the class of a kernel element to the class
of its conjugate.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L64) (native source start line; generated entries may point to their parent).

#### GroupExtension.conjActAbelianization_inl

Kind: `theorem`.

```lean
theorem GroupExtension.conjActAbelianization_inl {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) (n : N) : S.conjActAbelianization (S.inl n) = 1
```

**Native source docstring:** An embedded kernel element acts trivially on the kernel abelianization.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L71) (native source start line; generated entries may point to their parent).

#### GroupExtension.ker_rightHom_le_ker_conjActAbelianization

Kind: `theorem`.

```lean
theorem GroupExtension.ker_rightHom_le_ker_conjActAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) : S.rightHom.ker ≤ S.conjActAbelianization.ker
```

**Native source docstring:** The kernel of the extension projection acts trivially after abelianizing
the kernel.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L86) (native source start line; generated entries may point to their parent).

#### GroupExtension.quotientConjActAbelianization

Kind: `def`.

```lean
noncomputable def GroupExtension.quotientConjActAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) : Q →* MulAut (Abelianization N)
```

**Native source docstring:** The quotient group acts canonically on the abelianization of the kernel by
conjugation through any lift to the middle group.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L96) (native source start line; generated entries may point to their parent).

#### GroupExtension.quotientConjActAbelianization_rightHom

Kind: `theorem`.

```lean
theorem GroupExtension.quotientConjActAbelianization_rightHom {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) (e : E) : S.quotientConjActAbelianization (S.rightHom e) = S.conjActAbelianization e
```

**Native source docstring:** Characterization of the quotient action on an arbitrary lift.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L104) (native source start line; generated entries may point to their parent).

#### GroupExtension.quotientConjActAbelianization_apply_of

Kind: `theorem`.

```lean
theorem GroupExtension.quotientConjActAbelianization_apply_of {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) (e : E) (n : N) : (S.quotientConjActAbelianization (S.rightHom e)) (Abelianization.of n) = Abelianization.of ((S.conjAct e) n)
```

**Native source docstring:** Pointwise lift formula for the quotient action, including its conjugation
orientation on representatives of the kernel abelianization.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L121) (native source start line; generated entries may point to their parent).

#### GroupExtension.conjActAbelianization_eq_of_rightHom_eq

Kind: `theorem`.

```lean
theorem GroupExtension.conjActAbelianization_eq_of_rightHom_eq {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) {e e' : E} (h : S.rightHom e = S.rightHom e') : S.conjActAbelianization e = S.conjActAbelianization e'
```

**Native source docstring:** Two lifts of the same quotient element induce the same automorphism of the
kernel abelianization.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L131) (native source start line; generated entries may point to their parent).

#### GroupExtension.abelianization_conjAct_eq_of_rightHom_eq

Kind: `theorem`.

```lean
theorem GroupExtension.abelianization_conjAct_eq_of_rightHom_eq {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] (S : GroupExtension N E Q) {e e' : E} (h : S.rightHom e = S.rightHom e') (n : N) : Abelianization.of ((S.conjAct e) n) = Abelianization.of ((S.conjAct e') n)
```

**Native source docstring:** Inspectable representative-level form of independence from the chosen
lift of a quotient element.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L139) (native source start line; generated entries may point to their parent).

#### GroupExtension.Equiv.conjActAbelianization

Kind: `theorem`.

```lean
theorem GroupExtension.Equiv.conjActAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] {E' : Type u_1} [Group E'] {S : GroupExtension N E Q} {S' : GroupExtension N E' Q} (equiv : S.Equiv S') (e : E) : S'.conjActAbelianization (equiv e) = S.conjActAbelianization e
```

**Native source docstring:** An equivalence of extensions intertwines the middle-group actions on the
common kernel abelianization.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L153) (native source start line; generated entries may point to their parent).

#### GroupExtension.Equiv.quotientConjActAbelianization

Kind: `theorem`.

```lean
theorem GroupExtension.Equiv.quotientConjActAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] {E' : Type u_1} [Group E'] {S : GroupExtension N E Q} {S' : GroupExtension N E' Q} (equiv : S.Equiv S') : S'.quotientConjActAbelianization = S.quotientConjActAbelianization
```

**Native source docstring:** Equivalent extensions with the same kernel and quotient have exactly the
same descended action on the kernel abelianization.

[Source](../ContinuousGroupCohomology/QuotientConjugationAction.lean#L172) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.RestrictedLevelCompact

29 native named entries; 0 native instance-table rows.

#### ContinuousGroupCohomology.LevelCompact.universalNormSubmodule

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.universalNormSubmodule {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) : Submodule R ↥(openSubgroupInvariants A U.toOpenSubgroup)
```

**Native source docstring:** The elements of `A^U` lying in the range of the relative norm from every
deeper open normal level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L40) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.mem_universalNormSubmodule_iff

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.mem_universalNormSubmodule_iff {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) (x : ↥(openSubgroupInvariants A U.toOpenSubgroup)) : x ∈ universalNormSubmodule A U ↔ ∀ (V : OpenNormalSubgroup G) (h : V ≤ U), x ∈ (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Original catalogue explanation (not a Lean docstring):** The iff characterization named `mem_universalNormSubmodule_iff` in closed restricted level systems and finite-stage relative-norm ranges; use the full signature for both directions and their assumptions.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L48) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormSubmodule_le_range

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.universalNormSubmodule_le_range {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) : universalNormSubmodule A U ≤ (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universalNormSubmodule_le_range` in closed restricted level systems and finite-stage relative-norm ranges; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L57) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.relativeNorm_mem_universalNormSubmodule

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.relativeNorm_mem_universalNormSubmodule {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (hVU : V ≤ U) {x : ↥(openSubgroupInvariants A V.toOpenSubgroup)} (hx : x ∈ universalNormSubmodule A V) : (relativeNorm A U.toOpenSubgroup V.toOpenSubgroup hVU) x ∈ universalNormSubmodule A U
```

**Native source docstring:** Relative norms carry universal norms at a deeper normal level to universal
norms at the target level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L64) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormSubmodule_stable

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.universalNormSubmodule_stable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) (q : G ⧸ ↑U.toOpenSubgroup) {x : ↥(openSubgroupInvariants A U.toOpenSubgroup)} (hx : x ∈ universalNormSubmodule A U) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ q) x ∈ universalNormSubmodule A U
```

**Native source docstring:** The universal-norm submodule is stable under the residual quotient action.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L93) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormSubrepresentation

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.universalNormSubrepresentation {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) : Subrepresentation (A.quotientToInvariants ↑U.toOpenSubgroup).ρ
```

**Native source docstring:** Universal norms at `U`, as a subrepresentation of the residual
`G / U`-representation on `A^U`.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L105) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormSubrepresentation_toSubmodule

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.universalNormSubrepresentation_toSubmodule {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) : (universalNormSubrepresentation A U).toSubmodule = universalNormSubmodule A U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universalNormSubrepresentation_toSubmodule` in closed restricted level systems and finite-stage relative-norm ranges; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L113) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.isClosed_universalNormSubmodule

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.isClosed_universalNormSubmodule {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) (U : OpenNormalSubgroup G) : IsClosed ↑(universalNormSubmodule A U)
```

**Native source docstring:** Universal norms form a closed submodule for the level topology.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L120) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem

Kind: `structure`.

```lean
structure ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) : Type u
```

**Native source docstring:** A compatible choice of closed residual subrepresentation at every open
normal level, containing the universal norms and preserved by relative norms.

The topology on each chosen coefficient module is inherited from the supplied
`LevelCompact` topology; no topology on the ambient representation or scalar
ring is required.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L142) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.mk

Kind: `ctor`.

```lean
constructor ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.mk : {R G : Type u} → [inst : CommRing R] → [inst_1 : Group G] → [inst_2 : TopologicalSpace G] → [inst_3 : IsTopologicalGroup G] → [inst_4 : CompactSpace G] → {A : Rep R G} → {L : ContinuousGroupCohomology.LevelCompact A} → (subrepresentation : (U : OpenNormalSubgroup G) → Subrepresentation (A.quotientToInvariants ↑U.toOpenSubgroup).ρ) → (∀ (U : OpenNormalSubgroup G), ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U ≤ (subrepresentation U).toSubmodule) → (∀ (U V : OpenNormalSubgroup G) (h : V ≤ U) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A V.toOpenSubgroup)}, x ∈ subrepresentation V → (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) x ∈ subrepresentation U) → (∀ (U : OpenNormalSubgroup G), IsClosed ↑(subrepresentation U)) → ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem`; the structure fields and parameters are in the displayed signature and source declaration. Closed restricted level systems and finite-stage relative-norm ranges.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L142) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.subrepresentation

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.subrepresentation {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (self : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : Subrepresentation (A.quotientToInvariants ↑U.toOpenSubgroup).ρ
```

**Native source docstring:** The chosen `G / U`-stable coefficient submodule at level `U`.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L150) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.universalNorm_le

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.universalNorm_le {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (self : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : universalNormSubmodule A U ≤ (self.subrepresentation U).toSubmodule
```

**Native source docstring:** Every universal norm belongs to the chosen coefficient system.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L153) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_mem

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_mem {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (self : RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) {x : ↥(openSubgroupInvariants A V.toOpenSubgroup)} : x ∈ self.subrepresentation V → (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) x ∈ self.subrepresentation U
```

**Native source docstring:** Relative norms preserve the chosen coefficient system.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L156) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.isClosed

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.isClosed {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (self : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : IsClosed ↑(self.subrepresentation U)
```

**Native source docstring:** Each chosen coefficient submodule is closed in its level topology.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L162) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.coefficients

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.coefficients {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : Submodule R ↑(A.quotientToInvariants ↑U.toOpenSubgroup)
```

**Native source docstring:** The coefficient module selected at an open normal level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L172) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.topology

Kind: `def`.

```lean
abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.topology {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : TopologicalSpace ↥(S.coefficients U)
```

**Native source docstring:** The topology inherited by a restricted coefficient module from the full
invariant module at the same level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L176) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.t2

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.t2 {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : T2Space ↥(S.coefficients U)
```

**Native source docstring:** A restricted coefficient module is Hausdorff in its inherited topology.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L183) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.compact

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.compact {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : CompactSpace ↥(S.coefficients U)
```

**Native source docstring:** A restricted coefficient module is compact in its inherited topology.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L193) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.topologicalAddGroup

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.topologicalAddGroup {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : IsTopologicalAddGroup ↥(S.coefficients U)
```

**Native source docstring:** Addition and negation are continuous on a restricted coefficient module.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L203) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.group

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.group {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : CompHausAddCommGrp.{u}
```

**Native source docstring:** The compact Hausdorff additive group carried by a restricted coefficient
module at one open normal level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L213) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) : ↥(S.coefficients V) →ₗ[R] ↥(S.coefficients U)
```

**Native source docstring:** A relative norm restricted to the chosen coefficient modules.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L223) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_coe

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_coe {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) (x : ↥(S.coefficients V)) : ↑((S.relativeNorm U V h) x) = (LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `relativeNorm_coe` in closed restricted level systems and finite-stage relative-norm ranges; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L236) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_comp

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNorm_comp {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U V W : OpenNormalSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) : S.relativeNorm U V hVU ∘ₗ S.relativeNorm V W hWV = S.relativeNorm U W ⋯
```

**Native source docstring:** Restricted relative norms compose through a tower of open normal levels.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L243) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.continuous_relativeNorm

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.continuous_relativeNorm {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) : Continuous ⇑(S.relativeNorm U V h)
```

**Native source docstring:** Restricted relative norms are continuous for the inherited topologies.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L263) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNormHom

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem.relativeNormHom {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {A : Rep R G} {L : LevelCompact A} (S : RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) : S.group V ⟶ S.group U
```

**Native source docstring:** A restricted relative norm as a morphism of compact Hausdorff additive
groups.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L277) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) : RestrictedLevelSystem A L
```

**Native source docstring:** The unrestricted system choosing the full invariant module at every open
normal level.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L289) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem

Kind: `def`.

```lean
noncomputable def ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) : RestrictedLevelSystem A L
```

**Native source docstring:** The canonical restricted system consisting exactly of universal norms.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L300) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem_subrepresentation

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem_subrepresentation {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) (U : OpenNormalSubgroup G) : (fullRestrictedLevelSystem A L).subrepresentation U = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `fullRestrictedLevelSystem_subrepresentation` in closed restricted level systems and finite-stage relative-norm ranges; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L310) (native source start line; generated entries may point to their parent).

#### ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem_subrepresentation

Kind: `theorem`.

```lean
theorem ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem_subrepresentation {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : LevelCompact A) (U : OpenNormalSubgroup G) : (universalNormRestrictedLevelSystem A L).subrepresentation U = universalNormSubrepresentation A U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universalNormRestrictedLevelSystem_subrepresentation` in closed restricted level systems and finite-stage relative-norm ranges; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/RestrictedLevelCompact.lean#L316) (native source start line; generated entries may point to their parent).

### ContinuousGroupCohomology.TopModuleCatUlift

18 native named entries; 8 native instance-table rows.

#### ULift.instIsTopologicalAddGroupOfIsTopologicalAddGroup

Kind: `instance`.

```lean
instance ULift.instIsTopologicalAddGroupOfIsTopologicalAddGroup {M : Type v} [AddGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] : IsTopologicalAddGroup (ULift.{v', v} M)
```

**Native source docstring:** Raising the universe of a topological additive group preserves its
topological additive group structure.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L33) (native source start line; generated entries may point to their parent).

#### ULift.instContinuousSMulOfContinuousSMul

Kind: `instance`.

```lean
instance ULift.instContinuousSMulOfContinuousSMul {R : Type u} {M : Type v} [Semiring R] [TopologicalSpace R] [AddCommMonoid M] [Module R M] [TopologicalSpace M] [ContinuousSMul R M] : ContinuousSMul R (ULift.{v', v} M)
```

**Native source docstring:** A scalar action remains continuous after raising the universe of the
acted-on type.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L42) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctor

Kind: `def`.

```lean
def TopModuleCat.uliftFunctor (R : Type u) [Ring R] [TopologicalSpace R] : CategoryTheory.Functor (TopModuleCat R) (TopModuleCat R)
```

**Native source docstring:** Raise the universe of a topological `R`-module.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L56) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctor_map

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctor_map (R : Type u) [Ring R] [TopologicalSpace R] {X Y : TopModuleCat R} (f : X ⟶ Y) : (uliftFunctor.{v', v, u} R).map f = ofHom (↑ContinuousLinearEquiv.ulift.symm ∘SL Hom.hom f ∘SL ↑ContinuousLinearEquiv.ulift)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `uliftFunctor_map` in universe-lift functors for topological module categories; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L57) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctor_obj

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctor_obj (R : Type u) [Ring R] [TopologicalSpace R] (X : TopModuleCat R) : (uliftFunctor.{v', v, u} R).obj X = ↧(ULift.{v', v} ↑X.toModuleCat)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `uliftFunctor_obj` in universe-lift functors for topological module categories; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L57) (native source start line; generated entries may point to their parent).

#### TopModuleCat.fullyFaithfulUliftFunctor

Kind: `def`.

```lean
def TopModuleCat.fullyFaithfulUliftFunctor (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v', v, u} R).FullyFaithful
```

**Native source docstring:** The universe-raising functor on topological modules is fully faithful.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L71) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instFullUliftFunctor

Kind: `instance`.

```lean
instance TopModuleCat.instFullUliftFunctor (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v', v, u} R).Full
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Full` instance in universe-lift functors for topological module categories (native type names: `TopModuleCat.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L78) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instFaithfulUliftFunctor

Kind: `instance`.

```lean
instance TopModuleCat.instFaithfulUliftFunctor (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v', v, u} R).Faithful
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Faithful` instance in universe-lift functors for topological module categories (native type names: `TopModuleCat.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L80) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instAdditiveUliftFunctor

Kind: `instance`.

```lean
instance TopModuleCat.instAdditiveUliftFunctor (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v', v, u} R).Additive
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Additive` instance in universe-lift functors for topological module categories (native type names: `TopModuleCat.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L82) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorObjEquiv

Kind: `def`.

```lean
def TopModuleCat.uliftFunctorObjEquiv (R : Type u) [Ring R] [TopologicalSpace R] (X : TopModuleCat R) : ↑X.toModuleCat ≃L[R] ↑((uliftFunctor.{v', v, u} R).obj X).toModuleCat
```

**Native source docstring:** The original topological module is canonically continuously linearly
equivalent to the carrier of its universe lift.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L84) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorObjEquiv_apply

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctorObjEquiv_apply (R : Type u) [Ring R] [TopologicalSpace R] (X : TopModuleCat R) (x : ↑X.toModuleCat) : (uliftFunctorObjEquiv R X) x = { down := x }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `uliftFunctorObjEquiv_apply` for universe-lift functors for topological module categories; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L90) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorObjEquiv_symm_apply

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctorObjEquiv_symm_apply (R : Type u) [Ring R] [TopologicalSpace R] (X : TopModuleCat R) (x : ↑((uliftFunctor.{v', v, u} R).obj X).toModuleCat) : (uliftFunctorObjEquiv R X).symm x = x.down
```

**Original catalogue explanation (not a Lean docstring):** The named computation `uliftFunctorObjEquiv_symm_apply` for universe-lift functors for topological module categories; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L95) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorObjEquiv_naturality

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctorObjEquiv_naturality (R : Type u) [Ring R] [TopologicalSpace R] {X Y : TopModuleCat R} (f : X ⟶ Y) (x : ↑X.toModuleCat) : (uliftFunctorObjEquiv R Y) ((Hom.hom f) x) = (Hom.hom ((uliftFunctor.{v', v, u} R).map f)) ((uliftFunctorObjEquiv R X) x)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `uliftFunctorObjEquiv_naturality` for universe-lift functors for topological module categories; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L101) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorObjEquiv_symm_naturality

Kind: `theorem`.

```lean
theorem TopModuleCat.uliftFunctorObjEquiv_symm_naturality (R : Type u) [Ring R] [TopologicalSpace R] {X Y : TopModuleCat R} (f : X ⟶ Y) (x : ↑((uliftFunctor.{v', v, u} R).obj X).toModuleCat) : (Hom.hom f) ((uliftFunctorObjEquiv R X).symm x) = (uliftFunctorObjEquiv R Y).symm ((Hom.hom ((uliftFunctor.{v', v, u} R).map f)) x)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `uliftFunctorObjEquiv_symm_naturality` for universe-lift functors for topological module categories; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L107) (native source start line; generated entries may point to their parent).

#### TopModuleCat.uliftFunctorIsoSameUniverse

Kind: `def`.

```lean
noncomputable def TopModuleCat.uliftFunctorIsoSameUniverse (R : Type u) [Ring R] [TopologicalSpace R] : CategoryTheory.Functor.id (TopModuleCat R) ≅ uliftFunctor.{v, v, u} R
```

**Native source docstring:** In one fixed object universe, the identity functor on topological modules is
naturally isomorphic to universe lifting.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L115) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instEssSurjUliftFunctorSameUniverse

Kind: `instance`.

```lean
instance TopModuleCat.instEssSurjUliftFunctorSameUniverse (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v, v, u} R).EssSurj
```

**Native source docstring:** Same-universe lifting of topological modules is essentially surjective.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L123) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instIsEquivalenceUliftFunctorSameUniverse

Kind: `instance`.

```lean
instance TopModuleCat.instIsEquivalenceUliftFunctorSameUniverse (R : Type u) [Ring R] [TopologicalSpace R] : (uliftFunctor.{v, v, u} R).IsEquivalence
```

**Native source docstring:** Same-universe lifting is an equivalence of the category of topological
modules with itself.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L128) (native source start line; generated entries may point to their parent).

#### TopModuleCat.instLinearUliftFunctor

Kind: `instance`.

```lean
instance TopModuleCat.instLinearUliftFunctor (R : Type u) [CommRing R] [TopologicalSpace R] : CategoryTheory.Functor.Linear R (uliftFunctor.{v', v, u} R)
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Linear` instance in universe-lift functors for topological module categories (native type names: `TopModuleCat.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopModuleCatUlift.lean#L139) (native source start line; generated entries may point to their parent).

#### Native instance table

- `TopModuleCat.instAdditiveUliftFunctor`: `CategoryTheory.Functor.Additive`; type names: `TopModuleCat.uliftFunctor`

- `TopModuleCat.instEssSurjUliftFunctorSameUniverse`: `CategoryTheory.Functor.EssSurj`; type names: `TopModuleCat.uliftFunctor`

- `TopModuleCat.instFaithfulUliftFunctor`: `CategoryTheory.Functor.Faithful`; type names: `TopModuleCat.uliftFunctor`

- `TopModuleCat.instFullUliftFunctor`: `CategoryTheory.Functor.Full`; type names: `TopModuleCat.uliftFunctor`

- `TopModuleCat.instIsEquivalenceUliftFunctorSameUniverse`: `CategoryTheory.Functor.IsEquivalence`; type names: `TopModuleCat.uliftFunctor`

- `TopModuleCat.instLinearUliftFunctor`: `CategoryTheory.Functor.Linear`; type names: `TopModuleCat.uliftFunctor`

- `ULift.instContinuousSMulOfContinuousSMul`: `ContinuousSMul`; type names: `ULift`

- `ULift.instIsTopologicalAddGroupOfIsTopologicalAddGroup`: `IsTopologicalAddGroup`; type names: `ULift`

### ContinuousGroupCohomology.TopRepUlift

18 native named entries; 3 native instance-table rows.

#### TopRep.JointlyContinuous

Kind: `class`.

```lean
class TopRep.JointlyContinuous {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] [TopologicalSpace G] (X : TopRep k G) : Prop
```

**Native source docstring:** The action carried by a topological representation is jointly continuous.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L34) (native source start line; generated entries may point to their parent).

#### TopRep.JointlyContinuous.mk

Kind: `ctor`.

```lean
constructor TopRep.JointlyContinuous.mk : ∀ {k : Type u} [inst : Ring k] [inst_1 : TopologicalSpace k] {G : Type v} [inst_2 : Monoid G] [inst_3 : TopologicalSpace G] {X : TopRep k G}, (Continuous fun (p : G × ↑X) => (X.ρ p.1) p.2) → X.JointlyContinuous
```

**Original catalogue explanation (not a Lean docstring):** Lean-generated constructor for the source structure/class `TopRep.JointlyContinuous`; the structure fields and parameters are in the displayed signature and source declaration. Universe-lift functors and jointly continuous topological representations.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L34) (native source start line; generated entries may point to their parent).

#### TopRep.JointlyContinuous.continuous_action

Kind: `theorem`.

```lean
theorem TopRep.JointlyContinuous.continuous_action {k : Type u} {inst✝ : Ring k} {inst✝¹ : TopologicalSpace k} {G : Type v} {inst✝² : Monoid G} {inst✝³ : TopologicalSpace G} {X : TopRep k G} [self : X.JointlyContinuous] : Continuous fun (p : G × ↑X) => (X.ρ p.1) p.2
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `continuous_action` in universe-lift functors and jointly continuous topological representations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L36) (native source start line; generated entries may point to their parent).

#### TopRep.ulift

Kind: `def`.

```lean
def TopRep.ulift {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) : TopRep k (ULift.{v', v} G)
```

**Native source docstring:** Simultaneously raise the universes of the acting monoid and the carrier of
a topological representation.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L38) (native source start line; generated entries may point to their parent).

#### TopRep.ulift_ρ_apply

Kind: `theorem`.

```lean
theorem TopRep.ulift_ρ_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) (g : ULift.{v', v} G) (x : ULift.{w', w} ↑X) : (X.ulift.ρ g) x = { down := (X.ρ g.down) x.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `ulift_ρ_apply` for universe-lift functors and jointly continuous topological representations; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L54) (native source start line; generated entries may point to their parent).

#### TopRep.uliftMap

Kind: `def`.

```lean
def TopRep.uliftMap {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] {X Y : TopRep k G} (f : X ⟶ Y) : X.ulift ⟶ Y.ulift
```

**Native source docstring:** Raise a morphism of topological representations together with its source
and target carriers and the acting monoid.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L61) (native source start line; generated entries may point to their parent).

#### TopRep.uliftMap_apply

Kind: `theorem`.

```lean
theorem TopRep.uliftMap_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] {X Y : TopRep k G} (f : X ⟶ Y) (x : ULift.{w', w} ↑X) : (CategoryTheory.ConcreteCategory.hom (uliftMap f)) x = { down := (Hom.hom f) x.down }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `uliftMap_apply` for universe-lift functors and jointly continuous topological representations; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L78) (native source start line; generated entries may point to their parent).

#### TopRep.uliftFunctor

Kind: `def`.

```lean
def TopRep.uliftFunctor {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] : CategoryTheory.Functor (TopRep k G) (TopRep k (ULift.{v', v} G))
```

**Native source docstring:** Simultaneously raise the acting monoid and coefficient carrier of every
object and morphism in `TopRep`.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L87) (native source start line; generated entries may point to their parent).

#### TopRep.uliftFunctor_map

Kind: `theorem`.

```lean
theorem TopRep.uliftFunctor_map {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] {X✝ Y✝ : TopRep k G} (f : X✝ ⟶ Y✝) : uliftFunctor.{u, v, v', w, w'}.map f = uliftMap f
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `uliftFunctor_map` in universe-lift functors and jointly continuous topological representations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L89) (native source start line; generated entries may point to their parent).

#### TopRep.uliftFunctor_obj

Kind: `theorem`.

```lean
theorem TopRep.uliftFunctor_obj {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) : uliftFunctor.{u, v, v', w, w'}.obj X = X.ulift
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `uliftFunctor_obj` in universe-lift functors and jointly continuous topological representations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L89) (native source start line; generated entries may point to their parent).

#### TopRep.instAdditiveUliftFunctor

Kind: `instance`.

```lean
instance TopRep.instAdditiveUliftFunctor {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] : uliftFunctor.{u, v, v', w, w'}.Additive
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Additive` instance in universe-lift functors and jointly continuous topological representations (native type names: `TopRep.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L105) (native source start line; generated entries may point to their parent).

#### TopRep.uliftEquiv

Kind: `def`.

```lean
def TopRep.uliftEquiv {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) : (X.ρ.restrict MulEquiv.ulift.toMonoidHom).Equiv X.ulift.ρ
```

**Native source docstring:** The original representation, restricted along the canonical map from the
lifted acting monoid, is equivalent to the lifted coefficient representation.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L108) (native source start line; generated entries may point to their parent).

#### TopRep.uliftEquiv_apply

Kind: `theorem`.

```lean
theorem TopRep.uliftEquiv_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) (x : ↑X) : X.uliftEquiv x = { down := x }
```

**Original catalogue explanation (not a Lean docstring):** The named computation `uliftEquiv_apply` for universe-lift functors and jointly continuous topological representations; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L118) (native source start line; generated entries may point to their parent).

#### TopRep.uliftEquiv_symm_apply

Kind: `theorem`.

```lean
theorem TopRep.uliftEquiv_symm_apply {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] (X : TopRep k G) (x : ULift.{w', w} ↑X) : X.uliftEquiv.symm x = x.down
```

**Original catalogue explanation (not a Lean docstring):** The named computation `uliftEquiv_symm_apply` for universe-lift functors and jointly continuous topological representations; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L125) (native source start line; generated entries may point to their parent).

#### TopRep.uliftEquiv_naturality

Kind: `theorem`.

```lean
theorem TopRep.uliftEquiv_naturality {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] {X Y : TopRep k G} (f : X ⟶ Y) (x : ↑X) : (CategoryTheory.ConcreteCategory.hom (uliftMap f)) (X.uliftEquiv x) = Y.uliftEquiv ((Hom.hom f) x)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `uliftEquiv_naturality` for universe-lift functors and jointly continuous topological representations; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L132) (native source start line; generated entries may point to their parent).

#### TopRep.jointlyContinuousUlift

Kind: `instance`.

```lean
instance TopRep.jointlyContinuousUlift {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] [TopologicalSpace G] (X : TopRep k G) [X.JointlyContinuous] : X.ulift.JointlyContinuous
```

**Native source docstring:** Joint continuity of an action is preserved when both the acting monoid
and the coefficient carrier are raised to independent universes.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L149) (native source start line; generated entries may point to their parent).

#### TopRep.jointlyContinuous_ulift_iff

Kind: `theorem`.

```lean
theorem TopRep.jointlyContinuous_ulift_iff {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Monoid G] [TopologicalSpace G] (X : TopRep k G) : X.ulift.JointlyContinuous ↔ X.JointlyContinuous
```

**Native source docstring:** Joint continuity of an action is equivalent to joint continuity after
raising the acting monoid and coefficient carrier to independent universes.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L161) (native source start line; generated entries may point to their parent).

#### TopRep.instLinearUliftFunctor

Kind: `instance`.

```lean
instance TopRep.instLinearUliftFunctor {k : Type u} [CommRing k] [TopologicalSpace k] {G : Type v} [Monoid G] : CategoryTheory.Functor.Linear k uliftFunctor.{u, v, v', w, w'}
```

**Original catalogue explanation (not a Lean docstring):** Provides the native `CategoryTheory.Functor.Linear` instance in universe-lift functors and jointly continuous topological representations (native type names: `TopRep.uliftFunctor`); the displayed signature retains all instance parameters.

[Source](../ContinuousGroupCohomology/TopRepUlift.lean#L186) (native source start line; generated entries may point to their parent).

#### Native instance table

- `TopRep.instAdditiveUliftFunctor`: `CategoryTheory.Functor.Additive`; type names: `TopRep.uliftFunctor`

- `TopRep.instLinearUliftFunctor`: `CategoryTheory.Functor.Linear`; type names: `TopRep.uliftFunctor`

- `TopRep.jointlyContinuousUlift`: `TopRep.JointlyContinuous`; type names: `TopRep.ulift`

### ContinuousGroupCohomology.TopologicalModN

66 native named entries; 7 native instance-table rows.

#### TopologicalModN.multiples

Kind: `def`.

```lean
def TopologicalModN.multiples (A : Type uA) [AddCommGroup A] (n : ℕ) : AddSubgroup A
```

**Native source docstring:** The subgroup of `n`-fold multiples in an additive commutative group.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L43) (native source start line; generated entries may point to their parent).

#### TopologicalModN.closedMultiples

Kind: `def`.

```lean
def TopologicalModN.closedMultiples (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : AddSubgroup A
```

**Native source docstring:** The topological closure of the subgroup of `n`-fold multiples.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L47) (native source start line; generated entries may point to their parent).

#### TopologicalModN

Kind: `def`.

```lean
abbrev TopologicalModN (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : Type uA
```

**Native source docstring:** The quotient of `A` by the closure of its subgroup of `n`-fold multiples,
with mathlib's quotient topology.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L53) (native source start line; generated entries may point to their parent).

#### TopologicalModN.mkQ

Kind: `def`.

```lean
def TopologicalModN.mkQ {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : A →ₜ+ TopologicalModN A n
```

**Native source docstring:** The canonical continuous additive quotient homomorphism.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L67) (native source start line; generated entries may point to their parent).

#### TopologicalModN.mkQ_apply

Kind: `theorem`.

```lean
theorem TopologicalModN.mkQ_apply {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) (a : A) : (mkQ n) a = ↑a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mkQ_apply` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L72) (native source start line; generated entries may point to their parent).

#### TopologicalModN.nsmul_mem_closedMultiples

Kind: `theorem`.

```lean
theorem TopologicalModN.nsmul_mem_closedMultiples {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) (a : A) : n • a ∈ closedMultiples A n
```

**Native source docstring:** Every multiple belongs to the closed subgroup of multiples.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L76) (native source start line; generated entries may point to their parent).

#### TopologicalModN.instModule

Kind: `instance`.

```lean
instance TopologicalModN.instModule {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : Module (ZMod n) (TopologicalModN A n)
```

**Native source docstring:** The closed mod-`n` quotient is canonically a `ZMod n`-module, for every
natural `n`, including zero and one.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L81) (native source start line; generated entries may point to their parent).

#### TopologicalModN.instContinuousSMul

Kind: `instance`.

```lean
instance TopologicalModN.instContinuousSMul {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : ContinuousSMul (ZMod n) (TopologicalModN A n)
```

**Native source docstring:** Scalar multiplication by the discrete ring `ZMod n` is jointly
continuous.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L86) (native source start line; generated entries may point to their parent).

#### TopologicalModN.instT1Space

Kind: `instance`.

```lean
instance TopologicalModN.instT1Space {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : T1Space (TopologicalModN A n)
```

**Native source docstring:** The quotient is T1 even when the input group is not.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L100) (native source start line; generated entries may point to their parent).

#### TopologicalModN.instT2Space

Kind: `instance`.

```lean
instance TopologicalModN.instT2Space {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : T2Space (TopologicalModN A n)
```

**Native source docstring:** The quotient is Hausdorff even when the input group is not.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L105) (native source start line; generated entries may point to their parent).

#### TopologicalModN.KillsMultiples

Kind: `def`.

```lean
def TopologicalModN.KillsMultiples {A : Type uA} {B : Type uB} [AddCommGroup B] (n : ℕ) (f : A → B) : Prop
```

**Native source docstring:** Pointwise formulation saying that a homomorphism kills all `n`-fold
multiples.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L109) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_le_ker

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_le_ker {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] (n : ℕ) (f : A →+ B) (hf : KillsMultiples n ⇑f) : multiples A n ≤ f.ker
```

**Native source docstring:** Killing all pointwise multiples kills the algebraic multiple subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L116) (native source start line; generated entries may point to their parent).

#### TopologicalModN.liftOfClosed

Kind: `def`.

```lean
def TopologicalModN.liftOfClosed {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] (n : ℕ) (f : A →ₜ+ B) (hf : closedMultiples A n ≤ f.ker) : TopologicalModN A n →ₜ+ B
```

**Native source docstring:** Raw universal property.  Without a separation condition on the target,
the exact hypothesis is containment of the closed multiple subgroup in the
kernel.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L123) (native source start line; generated entries may point to their parent).

#### TopologicalModN.liftOfClosed_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.liftOfClosed_mk {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] (n : ℕ) (f : A →ₜ+ B) (hf : closedMultiples A n ≤ f.ker) (a : A) : (liftOfClosed n f hf) ((mkQ n) a) = f a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `liftOfClosed_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L135) (native source start line; generated entries may point to their parent).

#### TopologicalModN.closedMultiples_le_ker

Kind: `theorem`.

```lean
theorem TopologicalModN.closedMultiples_le_ker {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [T1Space B] (n : ℕ) (f : A →ₜ+ B) (hf : KillsMultiples n ⇑f) : closedMultiples A n ≤ f.ker
```

**Native source docstring:** For a T1 target, pointwise killing of multiples implies the exact closed
kernel hypothesis.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L141) (native source start line; generated entries may point to their parent).

#### TopologicalModN.lift

Kind: `def`.

```lean
def TopologicalModN.lift {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [T1Space B] (n : ℕ) (f : A →ₜ+ B) (hf : KillsMultiples n ⇑f) : TopologicalModN A n →ₜ+ B
```

**Native source docstring:** Universal property for continuous homomorphisms to T1 targets which kill
all `n`-fold multiples.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L149) (native source start line; generated entries may point to their parent).

#### TopologicalModN.lift_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.lift_mk {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [T1Space B] (n : ℕ) (f : A →ₜ+ B) (hf : KillsMultiples n ⇑f) (a : A) : (lift n f hf) ((mkQ n) a) = f a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `lift_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L156) (native source start line; generated entries may point to their parent).

#### TopologicalModN.hom_ext

Kind: `theorem`.

```lean
theorem TopologicalModN.hom_ext {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] (n : ℕ) {f g : TopologicalModN A n →ₜ+ B} (h : f.comp (mkQ n) = g.comp (mkQ n)) : f = g
```

**Native source docstring:** Continuous additive homomorphisms out of the quotient are determined on
representatives.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L162) (native source start line; generated entries may point to their parent).

#### TopologicalModN.map_closedMultiples_le

Kind: `theorem`.

```lean
theorem TopologicalModN.map_closedMultiples_le {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (n : ℕ) (f : A →ₜ+ B) : closedMultiples A n ≤ AddSubgroup.comap (↑f) (closedMultiples B n)
```

**Native source docstring:** A continuous homomorphism sends the closed multiple subgroup into the
closed multiple subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L171) (native source start line; generated entries may point to their parent).

#### TopologicalModN.map

Kind: `def`.

```lean
def TopologicalModN.map {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (n : ℕ) (f : A →ₜ+ B) : TopologicalModN A n →ₜ+ TopologicalModN B n
```

**Native source docstring:** Functoriality of closed topological reduction modulo `n`.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L183) (native source start line; generated entries may point to their parent).

#### TopologicalModN.map_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.map_mk {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (n : ℕ) (f : A →ₜ+ B) (a : A) : (map n f) ((mkQ n) a) = (mkQ n) (f a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `map_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L191) (native source start line; generated entries may point to their parent).

#### TopologicalModN.map_id

Kind: `theorem`.

```lean
theorem TopologicalModN.map_id {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : map n (ContinuousAddMonoidHom.id A) = ContinuousAddMonoidHom.id (TopologicalModN A n)
```

**Native source docstring:** Reduction maps the identity homomorphism to the identity.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L195) (native source start line; generated entries may point to their parent).

#### TopologicalModN.map_comp

Kind: `theorem`.

```lean
theorem TopologicalModN.map_comp {A : Type uA} {B : Type uB} {C : Type uC} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] [IsTopologicalAddGroup C] (n : ℕ) (f : A →ₜ+ B) (g : B →ₜ+ C) : map n (g.comp f) = (map n g).comp (map n f)
```

**Native source docstring:** Reduction respects composition.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L204) (native source start line; generated entries may point to their parent).

#### TopologicalModN.congr

Kind: `def`.

```lean
def TopologicalModN.congr {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (n : ℕ) (e : A ≃ₜ+ B) : TopologicalModN A n ≃ₜ+ TopologicalModN B n
```

**Native source docstring:** A continuous additive equivalence induces a continuous equivalence after
closed topological reduction.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L212) (native source start line; generated entries may point to their parent).

#### TopologicalModN.congr_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.congr_mk {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalAddGroup A] [IsTopologicalAddGroup B] (n : ℕ) (e : A ≃ₜ+ B) (a : A) : (congr n e) ((mkQ n) a) = (mkQ n) (e a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `congr_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L239) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_zero

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_zero {A : Type uA} [AddCommGroup A] : multiples A 0 = ⊥
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `multiples_zero` in closed power subgroups and topological reduction modulo n; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L249) (native source start line; generated entries may point to their parent).

#### TopologicalModN.closedMultiples_zero

Kind: `theorem`.

```lean
theorem TopologicalModN.closedMultiples_zero {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] : closedMultiples A 0 = ⊥.topologicalClosure
```

**Native source docstring:** At `n = 0`, the denominator is the closure of zero.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L260) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_one

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_one {A : Type uA} [AddCommGroup A] : multiples A 1 = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `multiples_one` in closed power subgroups and topological reduction modulo n; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L267) (native source start line; generated entries may point to their parent).

#### TopologicalModN.closedMultiples_one

Kind: `theorem`.

```lean
theorem TopologicalModN.closedMultiples_one {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] : closedMultiples A 1 = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `closedMultiples_one` in closed power subgroups and topological reduction modulo n; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L272) (native source start line; generated entries may point to their parent).

#### TopologicalModN.instTopologicalSpaceModN

Kind: `instance`.

```lean
instance TopologicalModN.instTopologicalSpaceModN {A : Type uA} [AddCommGroup A] [TopologicalSpace A] (n : ℕ) : TopologicalSpace (ModN A n)
```

**Native source docstring:** Algebraic `ModN` carries the quotient topology induced by `ModN.mkQ`.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L278) (native source start line; generated entries may point to their parent).

#### TopologicalModN.modNMk

Kind: `def`.

```lean
def TopologicalModN.modNMk {A : Type uA} [AddCommGroup A] [TopologicalSpace A] (n : ℕ) : A →ₜ+ ModN A n
```

**Native source docstring:** The algebraic mod-`n` quotient map, bundled continuously for the quotient
topology on `ModN`.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L282) (native source start line; generated entries may point to their parent).

#### TopologicalModN.modNMk_apply

Kind: `theorem`.

```lean
theorem TopologicalModN.modNMk_apply {A : Type uA} [AddCommGroup A] [TopologicalSpace A] (n : ℕ) (a : A) : (modNMk n) a = (ModN.mkQ n) a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `modNMk_apply` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L289) (native source start line; generated entries may point to their parent).

#### TopologicalModN.algebraicToClosed

Kind: `def`.

```lean
def TopologicalModN.algebraicToClosed {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) : ModN A n →ₜ+ TopologicalModN A n
```

**Native source docstring:** The algebraic quotient maps continuously to the closed quotient for every
topological additive commutative group.  It is generally a further quotient,
not an equivalence.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L292) (native source start line; generated entries may point to their parent).

#### TopologicalModN.algebraicToClosed_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.algebraicToClosed_mk {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] (n : ℕ) (a : A) : (algebraicToClosed n) ((modNMk n) a) = (mkQ n) a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `algebraicToClosed_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L319) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_isCompact

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_isCompact {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] (n : ℕ) : IsCompact ↑(multiples A n)
```

**Native source docstring:** On a compact Hausdorff group, the subgroup of multiples is compact.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L331) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_isClosed

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_isClosed {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) : IsClosed ↑(multiples A n)
```

**Native source docstring:** On a compact Hausdorff group, the subgroup of multiples is closed.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L337) (native source start line; generated entries may point to their parent).

#### TopologicalModN.closedMultiples_eq

Kind: `theorem`.

```lean
theorem TopologicalModN.closedMultiples_eq {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) : closedMultiples A n = multiples A n
```

**Native source docstring:** On the compact Hausdorff boundary, taking the closure does not enlarge
the multiple subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L342) (native source start line; generated entries may point to their parent).

#### TopologicalModN.multiples_eq_modNSubgroup

Kind: `theorem`.

```lean
theorem TopologicalModN.multiples_eq_modNSubgroup {A : Type uA} [AddCommGroup A] (n : ℕ) : multiples A n = ((LinearMap.lsmul ℤ A) ↑n).range.toAddSubgroup
```

**Native source docstring:** The subgroup used by algebraic `ModN` is the subgroup of `n`-fold
multiples.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L353) (native source start line; generated entries may point to their parent).

#### TopologicalModN.compactToModN

Kind: `def`.

```lean
def TopologicalModN.compactToModN {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) : TopologicalModN A n →ₜ+ ModN A n
```

**Native source docstring:** For a compact Hausdorff group, the closed quotient is continuously
additively equivalent to mathlib's algebraic `ModN`, equipped with its quotient
topology.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L365) (native source start line; generated entries may point to their parent).

#### TopologicalModN.compactToModN_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.compactToModN_mk {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) (a : A) : (compactToModN n) ((mkQ n) a) = (modNMk n) a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `compactToModN_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L376) (native source start line; generated entries may point to their parent).

#### TopologicalModN.compactModNEquiv

Kind: `def`.

```lean
def TopologicalModN.compactModNEquiv {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) : TopologicalModN A n ≃ₜ+ ModN A n
```

**Native source docstring:** For a compact Hausdorff group, the closed quotient is continuously
additively equivalent to mathlib's algebraic `ModN`, equipped with its quotient
topology.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L381) (native source start line; generated entries may point to their parent).

#### TopologicalModN.compactModNEquiv_mk

Kind: `theorem`.

```lean
theorem TopologicalModN.compactModNEquiv_mk {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) (a : A) : (compactModNEquiv n) ((mkQ n) a) = (ModN.mkQ n) a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `compactModNEquiv_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L407) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.powers

Kind: `def`.

```lean
def TopologicalPowerQuotient.powers (A : Type uA) [CommGroup A] (n : ℕ) : Subgroup A
```

**Native source docstring:** The subgroup of `n`-th powers.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L422) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.closedPowers

Kind: `def`.

```lean
def TopologicalPowerQuotient.closedPowers (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : Subgroup A
```

**Native source docstring:** The topological closure of the subgroup of `n`-th powers.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L426) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient

Kind: `def`.

```lean
abbrev TopologicalPowerQuotient (A : Type uA) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : Type uA
```

**Native source docstring:** Multiplicative facade for the quotient by the closure of `n`-th powers.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L433) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.presentation

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.presentation {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : TopologicalPowerQuotient A n = (A ⧸ closedPowers A n)
```

**Native source docstring:** The multiplicative facade is definitionally the quotient by the closed
power subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L445) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.multiplicativePresentation

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.multiplicativePresentation {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : TopologicalPowerQuotient A n = Multiplicative (TopologicalModN (Additive A) n)
```

**Native source docstring:** The direct closed-power presentation agrees definitionally with the
multiplicative form of the additive closed-multiple quotient.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L450) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.instT1Space

Kind: `instance`.

```lean
instance TopologicalPowerQuotient.instT1Space {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : T1Space (TopologicalPowerQuotient A n)
```

**Native source docstring:** The closed-power quotient is T1 even when the input group is not.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L456) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.instT2Space

Kind: `instance`.

```lean
instance TopologicalPowerQuotient.instT2Space {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : T2Space (TopologicalPowerQuotient A n)
```

**Native source docstring:** The closed-power quotient is Hausdorff even when the input group is not.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L461) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.mkQ

Kind: `def`.

```lean
def TopologicalPowerQuotient.mkQ {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : A →ₜ* TopologicalPowerQuotient A n
```

**Native source docstring:** The canonical continuous multiplicative quotient homomorphism.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L465) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.mkQ_apply

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.mkQ_apply {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) (a : A) : (mkQ n) a = ↑a
```

**Original catalogue explanation (not a Lean docstring):** The named computation `mkQ_apply` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L470) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.pow_mem_closedPowers

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.pow_mem_closedPowers {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) (a : A) : a ^ n ∈ closedPowers A n
```

**Native source docstring:** Every `n`-th power belongs to the closed power subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L474) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.map_closedPowers_le

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.map_closedPowers_le {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (n : ℕ) (f : A →ₜ* B) : closedPowers A n ≤ Subgroup.comap (↑f) (closedPowers B n)
```

**Native source docstring:** A continuous homomorphism sends the closed power subgroup into the closed
power subgroup.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L479) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.map

Kind: `def`.

```lean
def TopologicalPowerQuotient.map {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (n : ℕ) (f : A →ₜ* B) : TopologicalPowerQuotient A n →ₜ* TopologicalPowerQuotient B n
```

**Native source docstring:** Functoriality of the multiplicative closed-power quotient.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L491) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.map_mk

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.map_mk {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (n : ℕ) (f : A →ₜ* B) (a : A) : (map n f) ((mkQ n) a) = (mkQ n) (f a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `map_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L503) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.map_id

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.map_id {A : Type uA} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (n : ℕ) : map n (ContinuousMonoidHom.id A) = ContinuousMonoidHom.id (TopologicalPowerQuotient A n)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `map_id` for closed power subgroups and topological reduction modulo n; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L507) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.map_comp

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.map_comp {A : Type uA} {B : Type uB} {C : Type uC} [CommGroup A] [CommGroup B] [CommGroup C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C] (n : ℕ) (f : A →ₜ* B) (g : B →ₜ* C) : map n (g.comp f) = (map n g).comp (map n f)
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `map_comp` for closed power subgroups and topological reduction modulo n; refer to the signature for the actual hypotheses.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L515) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.congr

Kind: `def`.

```lean
def TopologicalPowerQuotient.congr {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (n : ℕ) (e : A ≃ₜ* B) : TopologicalPowerQuotient A n ≃ₜ* TopologicalPowerQuotient B n
```

**Native source docstring:** A continuous multiplicative equivalence induces an equivalence of closed
power quotients.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L522) (native source start line; generated entries may point to their parent).

#### TopologicalPowerQuotient.congr_mk

Kind: `theorem`.

```lean
theorem TopologicalPowerQuotient.congr_mk {A : Type uA} {B : Type uB} [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (n : ℕ) (e : A ≃ₜ* B) (a : A) : (congr n e) ((mkQ n) a) = (mkQ n) (e a)
```

**Original catalogue explanation (not a Lean docstring):** The named computation `congr_mk` for closed power subgroups and topological reduction modulo n; the displayed source type specifies its input and result exactly.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L549) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.topologicalPowerQuotient

Kind: `def`.

```lean
def PointwiseContinuousMulAction.topologicalPowerQuotient {Q : Type uQ} {A : Type uA} [Group Q] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (rho : PointwiseContinuousMulAction Q A) (n : ℕ) : PointwiseContinuousMulAction Q (TopologicalPowerQuotient A n)
```

**Native source docstring:** Descend every individually continuous automorphism to the quotient by
closed `n`-th powers.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L567) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.topologicalPowerQuotient_mk

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.topologicalPowerQuotient_mk {Q : Type uQ} {A : Type uA} [Group Q] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A] (rho : PointwiseContinuousMulAction Q A) (n : ℕ) (q : Q) (a : A) : (fun (g : Q) => ⇑((rho.topologicalPowerQuotient n).toMonoidHom g)) q ((TopologicalPowerQuotient.mkQ n) a) = (TopologicalPowerQuotient.mkQ n) ((fun (g : Q) => ⇑(rho.toMonoidHom g)) q a)
```

**Native source docstring:** Exact representative formula for the descended action.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L604) (native source start line; generated entries may point to their parent).

#### PointwiseContinuousMulAction.topologicalPowerQuotient_isEquivariant

Kind: `theorem`.

```lean
theorem PointwiseContinuousMulAction.topologicalPowerQuotient_isEquivariant {Q : Type uQ} {A : Type uA} {B : Type uB} [Group Q] [CommGroup A] [CommGroup B] [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalGroup A] [IsTopologicalGroup B] (rho : PointwiseContinuousMulAction Q A) (sigma : PointwiseContinuousMulAction Q B) (n : ℕ) (f : A →ₜ* B) (hf : rho.IsEquivariant sigma ⇑f) : (rho.topologicalPowerQuotient n).IsEquivariant (sigma.topologicalPowerQuotient n) ⇑(TopologicalPowerQuotient.map n f)
```

**Native source docstring:** An equivariant continuous homomorphism remains equivariant after passing
to closed power quotients.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L616) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationModNAction

Kind: `def`.

```lean
noncomputable abbrev ContinuousGroupExtension.quotientConjActTopologicalAbelianizationModNAction {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : ℕ) : PointwiseContinuousMulAction Q (TopologicalPowerQuotient (TopologicalAbelianization N) n)
```

**Native source docstring:** Reduce the accepted quotient-conjugation action before forming closed
coinvariants.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L648) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationModNCoinvariants

Kind: `def`.

```lean
abbrev ContinuousGroupExtension.quotientConjActTopologicalAbelianizationModNCoinvariants {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : ℕ) : Type uN
```

**Native source docstring:** Closed coinvariants formed after closed topological reduction modulo `n`.
This definition deliberately does not identify the result with reduction
performed after coinvariants.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L654) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationModNAction

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationModNAction {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (n : ℕ) : S'.quotientConjActTopologicalAbelianizationModNAction n = S.quotientConjActTopologicalAbelianizationModNAction n
```

**Native source docstring:** Accepted fixed-kernel/fixed-quotient extension equivalences preserve the
descended action after closed topological reduction.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L668) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationModNCoinvariantsEquiv

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationModNCoinvariantsEquiv {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uE'} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (n : ℕ) : S.quotientConjActTopologicalAbelianizationModNCoinvariants n ≃ₜ* S'.quotientConjActTopologicalAbelianizationModNCoinvariants n
```

**Native source docstring:** Extension equivalences induce the identity-on-representatives continuous
equivalence between the reduced closed coinvariants.

[Source](../ContinuousGroupCohomology/TopologicalModN.lean#L679) (native source start line; generated entries may point to their parent).

#### Native instance table

- `TopologicalModN.instContinuousSMul`: `ContinuousSMul`; type names: `ZMod`, `TopologicalModN`

- `TopologicalModN.instModule`: `Module`; type names: `ZMod`, `TopologicalModN`

- `TopologicalModN.instT1Space`: `T1Space`; type names: `TopologicalModN`

- `TopologicalModN.instT2Space`: `T2Space`; type names: `TopologicalModN`

- `TopologicalModN.instTopologicalSpaceModN`: `TopologicalSpace`; type names: `ModN`

- `TopologicalPowerQuotient.instT1Space`: `T1Space`; type names: `TopologicalPowerQuotient`

- `TopologicalPowerQuotient.instT2Space`: `T2Space`; type names: `TopologicalPowerQuotient`

### ContinuousGroupCohomology.TopologicalQuotientConjugationAction

22 native named entries; 0 native instance-table rows.

#### TopologicalAbelianization.fromAbelianization

Kind: `def`.

```lean
def TopologicalAbelianization.fromAbelianization (G : Type uN) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Abelianization G →* TopologicalAbelianization G
```

**Native source docstring:** The canonical homomorphism from algebraic abelianization to topological
abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L42) (native source start line; generated entries may point to their parent).

#### TopologicalAbelianization.fromAbelianization_apply_of

Kind: `theorem`.

```lean
theorem TopologicalAbelianization.fromAbelianization_apply_of (G : Type uN) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (g : G) : (fromAbelianization G) (Abelianization.of g) = ↑g
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `fromAbelianization_apply_of` in topological quotient-conjugation actions of group extensions; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L48) (native source start line; generated entries may point to their parent).

#### ContinuousMulEquiv.quotientGroupCongr

Kind: `def`.

```lean
def ContinuousMulEquiv.quotientGroupCongr {G : Type uN} {H : Type uH} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] (e : G ≃ₜ* H) (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal] (he : Subgroup.map (↑e) N = M) : G ⧸ N ≃ₜ* H ⧸ M
```

**Native source docstring:** A continuous multiplicative equivalence descends to a continuous
multiplicative equivalence of quotient groups when it carries the first
normal subgroup onto the second.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L60) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.continuous_conjAct

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.continuous_conjAct {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : Continuous ⇑(S.conjAct e)
```

**Native source docstring:** Conjugation on the kernel is continuous.  The proof uses the fact that the
kernel inclusion is an inducing map, not an independently assumed topology on
the abstract conjugation automorphism.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L82) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActContinuous

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.conjActContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : N ≃ₜ* N
```

**Native source docstring:** Conjugation by a middle-group element, bundled as a continuous
multiplicative automorphism of the kernel.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L94) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.map_topologicalClosure_commutator_conjActContinuous

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.map_topologicalClosure_commutator_conjActContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : Subgroup.map (↑(S.conjActContinuous e)) (commutator N).topologicalClosure = (commutator N).topologicalClosure
```

**Native source docstring:** Continuous conjugation preserves the closure of the kernel's commutator
subgroup.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L109) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N
```

**Native source docstring:** Conjugation by a middle-group element on the topological abelianization of
the kernel, bundled as a continuous automorphism.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L129) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous_apply_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous_apply_mk {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) (n : N) : (S.conjActTopologicalAbelianizationContinuous e) ↑n = ↑((S.conjAct e) n)
```

**Native source docstring:** Conjugation on topological abelianization sends a representative to the
class of its conjugate.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L138) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActTopologicalAbelianization

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.conjActTopologicalAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : E →* MulAut (TopologicalAbelianization N)
```

**Native source docstring:** The middle-group action on topological abelianization.  Its values admit
the bundled-continuous refinement
`conjActTopologicalAbelianizationContinuous`.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L146) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActTopologicalAbelianization_inl

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.conjActTopologicalAbelianization_inl {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (n : N) : S.conjActTopologicalAbelianization (S.inl n) = 1
```

**Native source docstring:** An embedded kernel element acts trivially on topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L169) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.ker_rightHom_le_ker_conjActTopologicalAbelianization

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.ker_rightHom_le_ker_conjActTopologicalAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : S.rightHom.ker ≤ S.conjActTopologicalAbelianization.ker
```

**Native source docstring:** The kernel of the extension projection acts trivially on topological
abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L186) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianization

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.quotientConjActTopologicalAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) : Q →* MulAut (TopologicalAbelianization N)
```

**Native source docstring:** The quotient-group action on the topological abelianization of the kernel.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L196) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianization_rightHom

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.quotientConjActTopologicalAbelianization_rightHom {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : S.quotientConjActTopologicalAbelianization (S.rightHom e) = S.conjActTopologicalAbelianization e
```

**Native source docstring:** The quotient action evaluated on a projected middle-group element is the
corresponding conjugation action.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L204) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous

Kind: `def`.

```lean
noncomputable def ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (q : Q) : TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N
```

**Native source docstring:** The value of the quotient action at any element, bundled as a continuous
automorphism of topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L223) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous_rightHom

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous_rightHom {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) : S.quotientConjActTopologicalAbelianizationContinuous (S.rightHom e) = S.conjActTopologicalAbelianizationContinuous e
```

**Native source docstring:** The bundled continuous quotient action agrees with continuous conjugation
on every lift.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L238) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous_apply_mk

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.quotientConjActTopologicalAbelianizationContinuous_apply_mk {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (e : E) (n : N) : (S.quotientConjActTopologicalAbelianizationContinuous (S.rightHom e)) ↑n = ↑((S.conjAct e) n)
```

**Native source docstring:** Arbitrary-lift formula for the continuous quotient action on a
representative of topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L250) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous_eq_of_rightHom_eq

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.conjActTopologicalAbelianizationContinuous_eq_of_rightHom_eq {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) {e e' : E} (h : S.rightHom e = S.rightHom e') : S.conjActTopologicalAbelianizationContinuous e = S.conjActTopologicalAbelianizationContinuous e'
```

**Native source docstring:** Two lifts of the same quotient element induce the same bundled continuous
automorphism of topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L261) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.topologicalAbelianization_conjAct_eq_of_rightHom_eq

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.topologicalAbelianization_conjAct_eq_of_rightHom_eq {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) {e e' : E} (h : S.rightHom e = S.rightHom e') (n : N) : ↑((S.conjAct e) n) = ↑((S.conjAct e') n)
```

**Native source docstring:** Representative-level form of independence from the chosen lift.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L271) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.fromAbelianization_quotientConjAct

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.fromAbelianization_quotientConjAct {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] (S : ContinuousGroupExtension N E Q) (q : Q) (x : Abelianization N) : (TopologicalAbelianization.fromAbelianization N) ((S.quotientConjActAbelianization q) x) = (S.quotientConjActTopologicalAbelianization q) ((TopologicalAbelianization.fromAbelianization N) x)
```

**Native source docstring:** The canonical map from algebraic to topological abelianization
intertwines the accepted algebraic quotient action with the topological one.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L282) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.conjActTopologicalAbelianization

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.conjActTopologicalAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uH} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (e : E) : S'.conjActTopologicalAbelianization (equiv e) = S.conjActTopologicalAbelianization e
```

**Native source docstring:** A continuous equivalence of extensions intertwines the middle-group
actions on topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L300) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianization

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianization {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uH} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') : S'.quotientConjActTopologicalAbelianization = S.quotientConjActTopologicalAbelianization
```

**Native source docstring:** Equivalent continuous extensions with the same kernel and quotient have
the same quotient action on topological abelianization.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L321) (native source start line; generated entries may point to their parent).

#### ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationContinuous

Kind: `theorem`.

```lean
theorem ContinuousGroupExtension.Equiv.quotientConjActTopologicalAbelianizationContinuous {N : Type uN} {E : Type uE} {Q : Type uQ} [Group N] [Group E] [Group Q] [TopologicalSpace N] [TopologicalSpace E] [TopologicalSpace Q] [IsTopologicalGroup N] [IsTopologicalGroup E] [IsTopologicalGroup Q] {E' : Type uH} [Group E'] [TopologicalSpace E'] [IsTopologicalGroup E'] {S : ContinuousGroupExtension N E Q} {S' : ContinuousGroupExtension N E' Q} (equiv : S.Equiv S') (q : Q) : S'.quotientConjActTopologicalAbelianizationContinuous q = S.quotientConjActTopologicalAbelianizationContinuous q
```

**Native source docstring:** Naturality of the bundled continuous automorphism attached to each
quotient element under an equivalence of continuous extensions.

[Source](../ContinuousGroupCohomology/TopologicalQuotientConjugationAction.lean#L341) (native source start line; generated entries may point to their parent).

## Checked-use clients

### examples.CompactFoundationNative

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### examples.FiniteCoinvariantsNative

16 native named entries; 0 native instance-table rows.

#### FiniteCoinvariantsNative.orbit_single

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.orbit_single {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) (g : H) (x : M) : (ContinuousGroupCohomology.finiteOrbitDifference ρ) (Pi.single ((Fintype.equivFin H) g) x) = (ρ g) x - x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `orbit_single` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L39) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.orbit_range

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.orbit_range {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] (ρ : Representation R H M) : (ContinuousGroupCohomology.finiteOrbitDifference ρ).range = Representation.Coinvariants.ker ρ
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `orbit_range` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L43) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.orbit_range_closed

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.orbit_range_closed {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.finiteOrbitDifferenceHom ρ hρ)).range = (Representation.Coinvariants.ker ρ).toAddSubgroup
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `orbit_range_closed` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L51) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.quotient_projection

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.quotient_projection {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (x : M) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.finiteCoinvariantsMk ρ hρ)) x = (Representation.Coinvariants.mk ρ) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `quotient_projection` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L57) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.invariant_descends_on_generators

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.invariant_descends_on_generators {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (f : M →ₗ[R] N) (hf : Continuous ⇑f) (hinv : ∀ (g : H), f ∘ₗ ρ g = f) (x : M) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.finiteCoinvariantsDesc ρ hρ f hf hinv)) ((Representation.Coinvariants.mk ρ) x) = f x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `invariant_descends_on_generators` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L65) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.invariant_descent_continuous

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.invariant_descent_continuous {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (f : M →ₗ[R] N) (hf : Continuous ⇑f) (hinv : ∀ (g : H), f ∘ₗ ρ g = f) : Continuous ⇑(CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.finiteCoinvariantsDesc ρ hρ f hf hinv))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `invariant_descent_continuous` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L72) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.intertwining_map_on_generators

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.intertwining_map_on_generators {R : Type uR} [CommRing R] {H : Type uH} [Group H] [Fintype H] {M : Type uM} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [CompactSpace M] [T2Space M] {N : Type uM} [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [CompactSpace N] [T2Space N] (ρ : Representation R H M) (τ : Representation R H N) (hρ : ∀ (g : H), Continuous ⇑(ρ g)) (hτ : ∀ (g : H), Continuous ⇑(τ g)) (f : ρ.IntertwiningMap τ) (hf : Continuous ⇑f) (x : M) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.finiteCoinvariantsMap ρ τ hρ hτ f hf)) ((Representation.Coinvariants.mk ρ) x) = (Representation.Coinvariants.mk τ) (f x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `intertwining_map_on_generators` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L79) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.residual_action_continuous

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.residual_action_continuous {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : OpenNormalSubgroup G) (q : G ⧸ ↑S.toOpenSubgroup) : Continuous ⇑((A.quotientToInvariants ↑S.toOpenSubgroup).ρ q)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `residual_action_continuous` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L96) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.full_level_norm_comparison

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.full_level_norm_comparison {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (S : OpenNormalSubgroup G) [Fintype (G ⧸ ↑S.toOpenSubgroup)] (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A S.toOpenSubgroup)) : ↑((ContinuousGroupCohomology.LevelCompact.relativeNorm A ⊤ S.toOpenSubgroup ⋯) x) = ↑((A.quotientToInvariants ↑S.toOpenSubgroup).ρ.norm x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `full_level_norm_comparison` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L104) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.descended_norm_on_generators

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.descended_norm_on_generators {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : OpenNormalSubgroup G) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A S.toOpenSubgroup)) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants A L S)) ((Representation.Coinvariants.mk (A.quotientToInvariants ↑S.toOpenSubgroup).ρ) x) = (ContinuousGroupCohomology.LevelCompact.relativeNorm A ⊤ S.toOpenSubgroup ⋯) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `descended_norm_on_generators` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L113) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.descended_norm_continuous

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.descended_norm_continuous {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : OpenNormalSubgroup G) : Continuous ⇑(CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants A L S))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `descended_norm_continuous` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L122) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples

Kind: `def`.

```lean
def FiniteCoinvariantsNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples : TopologicalSpace (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked finite-coinvariant and descended-norm examples; local instance syntax does not by itself promise a global public instance.

[Source](../examples/FiniteCoinvariantsNative.lean#L132) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples : DiscreteTopology (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked finite-coinvariant and descended-norm examples; local instance syntax does not by itself promise a global public instance.

[Source](../examples/FiniteCoinvariantsNative.lean#L133) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.properNormalLevel

Kind: `def`.

```lean
def FiniteCoinvariantsNative.properNormalLevel : OpenNormalSubgroup (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Defines `properNormalLevel` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L135) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.properNormalLevel_lt_top

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.properNormalLevel_lt_top : properNormalLevel.toOpenSubgroup < ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `properNormalLevel_lt_top` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L141) (native source start line; generated entries may point to their parent).

#### FiniteCoinvariantsNative.descended_norm_proper_level

Kind: `theorem`.

```lean
theorem FiniteCoinvariantsNative.descended_norm_proper_level {R : Type uR} [CommRing R] (A : Rep R (Multiplicative (ZMod 2))) (L : ContinuousGroupCohomology.LevelCompact A) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A properNormalLevel.toOpenSubgroup)) : (CompHausAddCommGrp.Hom.hom (ContinuousGroupCohomology.LevelCompact.normFromFiniteCoinvariants A L properNormalLevel)) ((Representation.Coinvariants.mk (A.quotientToInvariants ↑properNormalLevel.toOpenSubgroup).ρ) x) = (ContinuousGroupCohomology.LevelCompact.relativeNorm A ⊤ properNormalLevel.toOpenSubgroup ⋯) x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `descended_norm_proper_level` in checked finite-coinvariant and descended-norm examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteCoinvariantsNative.lean#L146) (native source start line; generated entries may point to their parent).

### examples.FiniteNegativeNative

8 native named entries; 0 native instance-table rows.

#### FiniteNegativeNativeClient.transport_component

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.transport_component {R G : Type u} [CommRing R] [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) (n : ℕ) : (ContinuousGroupCohomology.nestedQuotientInvariantsHomologyNatTrans S T hST n).app A = groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (ContinuousGroupCohomology.nestedQuotientInvariantsRepIso A S T hST).hom n
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `transport_component` in checked concrete finite negative-deflation examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteNegativeNative.lean#L37) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.factorization

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.factorization {R G : Type u} [CommRing R] [Group G] (A : Rep R G) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : ContinuousGroupCohomology.finiteNegativeDeflation A S T hST n = CategoryTheory.CategoryStruct.comp ((groupHomology.coinfNatTrans R (Subgroup.map (QuotientGroup.mk' S) T) n).app (A.quotientToInvariants S)) (CategoryTheory.CategoryStruct.comp ((groupHomology.functor R ((G ⧸ S) ⧸ Subgroup.map (QuotientGroup.mk' S) T) n).map (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants S) (Subgroup.map (QuotientGroup.mk' S) T))) (groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient S T hST).toMonoidHom (ContinuousGroupCohomology.nestedQuotientInvariantsRepIso A S T hST).hom n))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `factorization` in checked concrete finite negative-deflation examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteNegativeNative.lean#L45) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.coefficient_naturality

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.coefficient_naturality {R G : Type u} [CommRing R] [Group G] {A B : Rep R G} (f : A ⟶ B) (S T : Subgroup G) [S.Normal] [T.Normal] (hST : S ≤ T) [Fintype ↥(Subgroup.map (QuotientGroup.mk' S) T)] (n : ℕ) : CategoryTheory.CategoryStruct.comp ((groupHomology.functor R (G ⧸ S) n).map ((Rep.quotientToInvariantsFunctor R S).map f)) (ContinuousGroupCohomology.finiteNegativeDeflation B S T hST n) = CategoryTheory.CategoryStruct.comp (ContinuousGroupCohomology.finiteNegativeDeflation A S T hST n) ((groupHomology.functor R (G ⧸ T) n).map ((Rep.quotientToInvariantsFunctor R T).map f))
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `coefficient_naturality` for checked concrete finite negative-deflation examples; refer to the signature for the actual hypotheses.

[Source](../examples/FiniteNegativeNative.lean#L62) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.bottom_lt_top

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.bottom_lt_top : ⊥ < ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `bottom_lt_top` in checked concrete finite negative-deflation examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteNegativeNative.lean#L75) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.instFintypeSubtypeQuotientMultiplicativeZModOfNatNatSubgroupBotMemMapMk'Top_examples

Kind: `def`.

```lean
noncomputable def FiniteNegativeNativeClient.instFintypeSubtypeQuotientMultiplicativeZModOfNatNatSubgroupBotMemMapMk'Top_examples : Fintype ↥(Subgroup.map (QuotientGroup.mk' ⊥) ⊤)
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked concrete finite negative-deflation examples; local instance syntax does not by itself promise a global public instance.

[Source](../examples/FiniteNegativeNative.lean#L77) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.concrete_degree_zero

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.concrete_degree_zero (A : Rep ℤ (Multiplicative (ZMod 2))) : ContinuousGroupCohomology.finiteNegativeDeflation A ⊥ ⊤ ⋯ 0 = CategoryTheory.CategoryStruct.comp ((groupHomology.coinfNatTrans ℤ (Subgroup.map (QuotientGroup.mk' ⊥) ⊤) 0).app (A.quotientToInvariants ⊥)) (CategoryTheory.CategoryStruct.comp ((groupHomology.functor ℤ ((Multiplicative (ZMod 2) ⧸ ⊥) ⧸ Subgroup.map (QuotientGroup.mk' ⊥) ⊤) 0).map (FiniteGroupTateCohomology.quotientNorm (A.quotientToInvariants ⊥) (Subgroup.map (QuotientGroup.mk' ⊥) ⊤))) (groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient ⊥ ⊤ ⋯).toMonoidHom (ContinuousGroupCohomology.nestedQuotientInvariantsRepIso A ⊥ ⊤ ⋯).hom 0))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `concrete_degree_zero` in checked concrete finite negative-deflation examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteNegativeNative.lean#L81) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.concrete_positive_degree

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.concrete_positive_degree (A : Rep ℤ (Multiplicative (ZMod 2))) : ContinuousGroupCohomology.finiteNegativeDeflation A ⊥ ⊤ ⋯ 1 = CategoryTheory.CategoryStruct.comp ((groupHomology.coinfNatTrans ℤ (Subgroup.map (QuotientGroup.mk' ⊥) ⊤) 1).app (A.quotientToInvariants ⊥)) (CategoryTheory.CategoryStruct.comp ((groupHomology.functor ℤ ((Multiplicative (ZMod 2) ⧸ ⊥) ⧸ Subgroup.map (QuotientGroup.mk' ⊥) ⊤) 1).map ((FiniteGroupTateCohomology.quotientNormNatTrans (Subgroup.map (QuotientGroup.mk' ⊥) ⊤)).app (A.quotientToInvariants ⊥))) (groupHomology.map (QuotientGroup.quotientQuotientEquivQuotient ⊥ ⊤ ⋯).toMonoidHom (ContinuousGroupCohomology.nestedQuotientInvariantsRepIso A ⊥ ⊤ ⋯).hom 1))
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `concrete_positive_degree` in checked concrete finite negative-deflation examples; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/FiniteNegativeNative.lean#L98) (native source start line; generated entries may point to their parent).

#### FiniteNegativeNativeClient.concrete_positive_naturality

Kind: `theorem`.

```lean
theorem FiniteNegativeNativeClient.concrete_positive_naturality {A B : Rep ℤ (Multiplicative (ZMod 2))} (f : A ⟶ B) : CategoryTheory.CategoryStruct.comp ((groupHomology.functor ℤ (Multiplicative (ZMod 2) ⧸ ⊥) 1).map ((Rep.quotientToInvariantsFunctor ℤ ⊥).map f)) (ContinuousGroupCohomology.finiteNegativeDeflation B ⊥ ⊤ ⋯ 1) = CategoryTheory.CategoryStruct.comp (ContinuousGroupCohomology.finiteNegativeDeflation A ⊥ ⊤ ⋯ 1) ((groupHomology.functor ℤ (Multiplicative (ZMod 2) ⧸ ⊤) 1).map ((Rep.quotientToInvariantsFunctor ℤ ⊤).map f))
```

**Original catalogue explanation (not a Lean docstring):** The named composition, identity or naturality law `concrete_positive_naturality` for checked concrete finite negative-deflation examples; refer to the signature for the actual hypotheses.

[Source](../examples/FiniteNegativeNative.lean#L117) (native source start line; generated entries may point to their parent).

### examples.LevelCompactNative

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### examples.LevelCompactNormNative

15 native named entries; 0 native instance-table rows.

#### LevelCompactNormNative.relativeNormSubgroup_comap

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.relativeNormSubgroup_comap {G : Type uG} [Group G] [TopologicalSpace G] (U V : OpenSubgroup G) : ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup U V = OpenSubgroup.comap (↑U).subtype ⋯ V
```

**Native source docstring:** The subgroup used for the relative norm is the pullback inside `U`.

[Source](../examples/LevelCompactNormNative.lean#L35) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.normClientTransversalFintype

Kind: `def`.

```lean
noncomputable def LevelCompactNormNative.normClientTransversalFintype {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (U V : OpenSubgroup G) (T : (↑(ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup U V)).RightTransversal) : Fintype ↑↑T
```

**Original catalogue explanation (not a Lean docstring):** Defines `normClientTransversalFintype` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L40) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_with_choice

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_with_choice {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T : (↑(ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup U V)).RightTransversal) : ContinuousGroupCohomology.LevelCompact.relativeNorm A U V h = ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal A U V h T
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_with_choice` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L45) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_two_choices

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_two_choices {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T S : (↑(ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup U V)).RightTransversal) : ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal A U V h T = ContinuousGroupCohomology.LevelCompact.relativeNormWithTransversal A U V h S
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_two_choices` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L52) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_with_choice_coe

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_with_choice_coe {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenSubgroup G) (h : V ≤ U) (T : (↑(ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup U V)).RightTransversal) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A V)) : ↑((ContinuousGroupCohomology.LevelCompact.relativeNorm A U V h) x) = ∑ t : ↑↑T, (A.ρ (↑↑t)⁻¹) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_with_choice_coe` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L59) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_tower

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_tower {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V W : OpenSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) : ContinuousGroupCohomology.LevelCompact.relativeNorm A U V hVU ∘ₗ ContinuousGroupCohomology.LevelCompact.relativeNorm A V W hWV = ContinuousGroupCohomology.LevelCompact.relativeNorm A U W ⋯
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_tower` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L68) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_same_level

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_same_level {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenSubgroup G) : ContinuousGroupCohomology.LevelCompact.relativeNorm A U U ⋯ = LinearMap.id
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_same_level` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L75) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_residual_action

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_residual_action {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) (g : G) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A V.toOpenSubgroup)) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ ((QuotientGroup.mk' ↑U.toOpenSubgroup) g)) ((ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) x) = (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) (((A.quotientToInvariants ↑V.toOpenSubgroup).ρ ((QuotientGroup.mk' ↑V.toOpenSubgroup) g)) x)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_residual_action` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L79) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_range_residual_stable

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_range_residual_stable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) (q : G ⧸ ↑U.toOpenSubgroup) {y : ↥(ContinuousGroupCohomology.openSubgroupInvariants A U.toOpenSubgroup)} (hy : y ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ q) y ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_range_residual_stable` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L90) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_continuous

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_continuous {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (U V : OpenSubgroup G) (h : V ≤ U) : Continuous ⇑(ContinuousGroupCohomology.LevelCompact.relativeNorm A U V h)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_continuous` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L100) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples

Kind: `def`.

```lean
def LevelCompactNormNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples : TopologicalSpace (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked relative-norm calculations on compact levels; local instance syntax does not by itself promise a global public instance.

[Source](../examples/LevelCompactNormNative.lean#L108) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples : DiscreteTopology (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked relative-norm calculations on compact levels; local instance syntax does not by itself promise a global public instance.

[Source](../examples/LevelCompactNormNative.lean#L109) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.twoElementBottom

Kind: `def`.

```lean
def LevelCompactNormNative.twoElementBottom : OpenSubgroup (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Defines `twoElementBottom` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L111) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.twoElementBottom_lt_top

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.twoElementBottom_lt_top : twoElementBottom < ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `twoElementBottom_lt_top` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L115) (native source start line; generated entries may point to their parent).

#### LevelCompactNormNative.norm_twoElement_proper_level

Kind: `theorem`.

```lean
theorem LevelCompactNormNative.norm_twoElement_proper_level {R : Type uR} [CommRing R] (A : Rep R (Multiplicative (ZMod 2))) (T : (↑(ContinuousGroupCohomology.LevelCompact.relativeNormSubgroup ⊤ twoElementBottom)).RightTransversal) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A twoElementBottom)) : ↑((ContinuousGroupCohomology.LevelCompact.relativeNorm A ⊤ twoElementBottom ⋯) x) = ∑ t : ↑↑T, (A.ρ (↑↑t)⁻¹) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `norm_twoElement_proper_level` in checked relative-norm calculations on compact levels; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/LevelCompactNormNative.lean#L119) (native source start line; generated entries may point to their parent).

### examples.NativeCore

5 native named entries; 0 native instance-table rows.

#### NativeCore.split_connecting_exact

Kind: `theorem`.

```lean
theorem NativeCore.split_connecting_exact {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {A B C : TopRep k G} (sequence : ContinuousCohomology.TopologicallySplitShortExact A B C) [LocallyCompactSpace G] [A.JointlyContinuous] [B.JointlyContinuous] : Function.Exact ⇑sequence.invariantsProjection ⇑(TopModuleCat.Hom.hom sequence.connectingMap)
```

**Native source docstring:** Exactness at invariant quotient coefficients in continuous degree one.

[Source](../examples/NativeCore.lean#L35) (native source start line; generated entries may point to their parent).

#### NativeCore.transfer_from_full_group

Kind: `theorem`.

```lean
theorem NativeCore.transfer_from_full_group {k : Type u} [Ring k] [TopologicalSpace k] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (X : TopRep k G) [X.JointlyContinuous] [LocallyCompactSpace G] : CategoryTheory.CategoryStruct.comp (ContinuousCohomology.map (ContinuousCohomology.CorestrictionTransversal.openSubgroupInclusion ⊤) (ContinuousCohomology.CorestrictionTransversal.restrictionCoeffHom X ⊤) 1) (ContinuousCohomology.CorestrictionTransversal.corestrictionOne X ⊤) = CategoryTheory.CategoryStruct.id (continuousCohomology 1 X)
```

**Native source docstring:** For the full open subgroup, restriction followed by transfer is the identity.

[Source](../examples/NativeCore.lean#L44) (native source start line; generated entries may point to their parent).

#### NativeCore.finite_orbit_relations

Kind: `theorem`.

```lean
theorem NativeCore.finite_orbit_relations {R : Type u} [CommRing R] {H : Type v} [Group H] [Fintype H] {M : Type w} [AddCommGroup M] [Module R M] (representation : Representation R H M) : (ContinuousGroupCohomology.finiteOrbitDifference representation).range = Representation.Coinvariants.ker representation
```

**Native source docstring:** Finite orbit differences generate precisely the coinvariant relations.

[Source](../examples/NativeCore.lean#L56) (native source start line; generated entries may point to their parent).

#### NativeCore.compact_mod_n_representative

Kind: `theorem`.

```lean
theorem NativeCore.compact_mod_n_representative {A : Type u} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [CompactSpace A] [T2Space A] (n : ℕ) (a : A) : (TopologicalModN.compactModNEquiv n) ((TopologicalModN.mkQ n) a) = (ModN.mkQ n) a
```

**Native source docstring:** Closed reduction modulo `n` agrees with algebraic reduction on representatives
of a compact Hausdorff additive group.

[Source](../examples/NativeCore.lean#L65) (native source start line; generated entries may point to their parent).

#### NativeCore.compact_limit_projection

Kind: `theorem`.

```lean
theorem NativeCore.compact_limit_projection {J : Type v} [CategoryTheory.SmallCategory J] [CategoryTheory.IsCofilteredOrEmpty J] (diagram : CategoryTheory.Functor J CompHausAddCommGrp.{max u v}) (index : J) (surjective : ∀ {source : J} (arrow : source ⟶ index), Function.Surjective ⇑(CompHausAddCommGrp.Hom.hom (diagram.map arrow))) : Function.Surjective ⇑(CompHausAddCommGrp.Hom.hom (CategoryTheory.Limits.limit.π diagram index))
```

**Native source docstring:** At any chosen object of a cofiltered-or-empty diagram of compact Hausdorff
additive groups, surjective transitions into that object imply a surjective
limit projection. An empty index category has no object at which to apply this.

[Source](../examples/NativeCore.lean#L75) (native source start line; generated entries may point to their parent).

### examples.NestedInvariantsNative

0 native named entries; 0 native instance-table rows.

No new named declarations in this module.

### examples.RestrictedLevelNative

25 native named entries; 0 native instance-table rows.

#### RestrictedLevelNative.universal_membership

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.universal_membership {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) (x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A U.toOpenSubgroup)) : x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U ↔ ∀ (V : OpenNormalSubgroup G) (h : V ≤ U), x ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universal_membership` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L42) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.universal_in_each_norm_range

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.universal_in_each_norm_range {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A U.toOpenSubgroup)} (hx : x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U) : x ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universal_in_each_norm_range` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L50) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.universal_stable

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.universal_stable {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U : OpenNormalSubgroup G) (q : G ⧸ ↑U.toOpenSubgroup) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A U.toOpenSubgroup)} (hx : x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U) : ((A.quotientToInvariants ↑U.toOpenSubgroup).ρ q) x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universal_stable` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L57) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.universal_norm_preservation

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.universal_norm_preservation {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (U V : OpenNormalSubgroup G) (h : V ≤ U) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A V.toOpenSubgroup)} (hx : x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A V) : (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `universal_norm_preservation` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L64) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_contains_universal

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_contains_universal {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A U.toOpenSubgroup)} (hx : x ∈ ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U) : x ∈ S.coefficients U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_contains_universal` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L71) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_norm_formula

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_norm_formula {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) (x : ↥(S.coefficients V)) : ↑((S.relativeNorm U V h) x) = (ContinuousGroupCohomology.LevelCompact.relativeNorm A U.toOpenSubgroup V.toOpenSubgroup h) ↑x
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_norm_formula` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L77) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_norm_tower

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_norm_tower {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U V W : OpenNormalSubgroup G) (hWV : W ≤ V) (hVU : V ≤ U) : S.relativeNorm U V hVU ∘ₗ S.relativeNorm V W hWV = S.relativeNorm U W ⋯
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_norm_tower` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L83) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_norm_same_level

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_norm_same_level {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : S.relativeNorm U U ⋯ = LinearMap.id
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_norm_same_level` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L89) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_norm_continuous

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_norm_continuous {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) : Continuous ⇑(S.relativeNorm U V h)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_norm_continuous` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L100) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_compact

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_compact {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : CompactSpace ↥(S.coefficients U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_compact` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L106) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_hausdorff

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_hausdorff {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : T2Space ↥(S.coefficients U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_hausdorff` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L111) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_additive_group

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.chosen_additive_group {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : IsTopologicalAddGroup ↥(S.coefficients U)
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `chosen_additive_group` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L116) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_compact_group

Kind: `def`.

```lean
noncomputable def RestrictedLevelNative.chosen_compact_group {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U : OpenNormalSubgroup G) : CompHausAddCommGrp.{u}
```

**Original catalogue explanation (not a Lean docstring):** Defines `chosen_compact_group` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L121) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.chosen_norm_group_hom

Kind: `def`.

```lean
noncomputable def RestrictedLevelNative.chosen_norm_group_hom {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (S : ContinuousGroupCohomology.LevelCompact.RestrictedLevelSystem A L) (U V : OpenNormalSubgroup G) (h : V ≤ U) : S.group V ⟶ S.group U
```

**Original catalogue explanation (not a Lean docstring):** Defines `chosen_norm_group_hom` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L125) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.full_choice

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.full_choice {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (U : OpenNormalSubgroup G) : (ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem A L).subrepresentation U = ⊤
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `full_choice` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L130) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.canonical_choice

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.canonical_choice {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (U : OpenNormalSubgroup G) : (ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem A L).coefficients U = ContinuousGroupCohomology.LevelCompact.universalNormSubmodule A U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `canonical_choice` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L134) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.canonical_le_full

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.canonical_le_full {R G : Type u} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (A : Rep R G) (L : ContinuousGroupCohomology.LevelCompact A) (U : OpenNormalSubgroup G) : (ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem A L).coefficients U ≤ (ContinuousGroupCohomology.LevelCompact.fullRestrictedLevelSystem A L).coefficients U
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `canonical_le_full` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L140) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples

Kind: `def`.

```lean
def RestrictedLevelNative.instTopologicalSpaceMultiplicativeZModOfNatNat_examples : TopologicalSpace (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked restricted-level and norm-range calculations; local instance syntax does not by itself promise a global public instance.

[Source](../examples/RestrictedLevelNative.lean#L149) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.instDiscreteTopologyMultiplicativeZModOfNatNat_examples : DiscreteTopology (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Generated declaration of a module-local instance for checked restricted-level and norm-range calculations; local instance syntax does not by itself promise a global public instance.

[Source](../examples/RestrictedLevelNative.lean#L150) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.twoElementBottom

Kind: `def`.

```lean
def RestrictedLevelNative.twoElementBottom : OpenNormalSubgroup (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Defines `twoElementBottom` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L152) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.twoElementTop

Kind: `def`.

```lean
def RestrictedLevelNative.twoElementTop : OpenNormalSubgroup (Multiplicative (ZMod 2))
```

**Original catalogue explanation (not a Lean docstring):** Defines `twoElementTop` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L158) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.twoElementBottom_lt_top

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.twoElementBottom_lt_top : twoElementBottom < twoElementTop
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `twoElementBottom_lt_top` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L164) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.finiteDiscreteLevelCompact

Kind: `def`.

```lean
noncomputable def RestrictedLevelNative.finiteDiscreteLevelCompact (A : Rep (ZMod 2) (Multiplicative (ZMod 2))) [Finite ↑A] : ContinuousGroupCohomology.LevelCompact A
```

**Original catalogue explanation (not a Lean docstring):** Defines `finiteDiscreteLevelCompact` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L168) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.proper_level_norm_range

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.proper_level_norm_range {Rfinite : Type} [CommRing Rfinite] (A : Rep Rfinite (Multiplicative (ZMod 2))) (L : ContinuousGroupCohomology.LevelCompact A) {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A twoElementTop.toOpenSubgroup)} (hx : x ∈ (ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem A L).coefficients twoElementTop) : x ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A twoElementTop.toOpenSubgroup twoElementBottom.toOpenSubgroup ⋯).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `proper_level_norm_range` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L191) (native source start line; generated entries may point to their parent).

#### RestrictedLevelNative.finite_discrete_proper_norm_range

Kind: `theorem`.

```lean
theorem RestrictedLevelNative.finite_discrete_proper_norm_range (A : Rep (ZMod 2) (Multiplicative (ZMod 2))) [Finite ↑A] {x : ↥(ContinuousGroupCohomology.openSubgroupInvariants A twoElementTop.toOpenSubgroup)} (hx : x ∈ (ContinuousGroupCohomology.LevelCompact.universalNormRestrictedLevelSystem A (finiteDiscreteLevelCompact A)).coefficients twoElementTop) : x ∈ (ContinuousGroupCohomology.LevelCompact.relativeNorm A twoElementTop.toOpenSubgroup twoElementBottom.toOpenSubgroup ⋯).range
```

**Original catalogue explanation (not a Lean docstring):** Records a theorem about `finite_discrete_proper_norm_range` in checked restricted-level and norm-range calculations; the displayed signature, not this orientation text, specifies its exact scope.

[Source](../examples/RestrictedLevelNative.lean#L204) (native source start line; generated entries may point to their parent).

<a id="continuous-group-cohomology-native-finite-stage-colimits-and-compact-finite-quotients"></a>
# Continuous group cohomology

This Lean library develops continuous cohomology of topological groups,
finite-index transfer, and finite-quotient Tate and compact finite-bar
constructions. The [Results guide](docs/Results.md) gives the complete
mathematical inventory, examples and limitations.

## Headline results

These cohomological results are proved here for representations over a ring
`k` equipped with a topology. The group, discreteness and action-continuity
hypotheses are specified separately below; foundations come from Mathlib.

### Finite-quotient descent, torsion and the topological colimit

See [`CompactDiscreteTorsion`](ContinuousGroupCohomology/CompactDiscreteTorsion.lean)
and [`FiniteStageColimit`](ContinuousGroupCohomology/FiniteStageColimit.lean) for these APIs.

For a compact topological group `G` and discrete jointly continuous
`X : TopRep k G` with `[Ring k] [TopologicalSpace k]`, every native continuous
cohomology class lifts from an open-normal finite quotient with its actual
quotient-invariant coefficients. In positive degrees a class-dependent quotient
order annihilates the class; this gives additive torsion, not a uniform bound.
The native open-normal inflation cocone is a filtered colimit in topological
modules in **every degree, including zero**, with arbitrary topological-module
targets. It uses the actual cohomology topology, genuine algebraic boundaries
and class-dependent eventual refinements, not fixed-stage positive-degree
injectivity, a uniform refinement or a closed-boundary-range assumption.

### Positive coinduced cohomology after closed restriction

For compact topological groups and discrete coefficients,
[diagonal insertion](ContinuousGroupCohomology/CoinducedAcyclic.lean)
gives a map on the recursively iterated coinduced homogeneous cochains with an
explicit evaluation law. This insertion contracts the cochain complex in every
positive degree, so continuous cohomology with coinduced discrete coefficients
vanishes there. Degree-zero vanishing is false even for the two-element group
acting trivially on nonzero integers (see the
[two-element-group client](CGCExamples/CoinducedAcyclic.lean)).
The [coefficient functor](ContinuousGroupCohomology/ContinuousCohomologyFunctor.lean)
for a fixed acting group and degree uses Mathlib's continuous-cohomology maps;
its object and morphism laws transport positive vanishing across coefficient
isomorphisms in the same group. For compact Hausdorff totally disconnected
`G`, the [closed-subgroup positive-vanishing theorem](ContinuousGroupCohomology/ProfiniteCoinducedAcyclic.lean)
then applies to every closed `H`, and also to restrictions of representations
isomorphic to `TopRep.coind₁ B`. The restricted representation is `H`-coinduced
from all of `C(G ⧸ H, B)` with its generally nontrivial pointwise `H`-action.
Only discrete `B` is needed; neither openness or normality of `H` nor joint
continuity of the coefficient action is required. The finite signed
[`S₃` clients](CGCExamples/CoinducedRestriction.lean) instantiate positive
vanishing at a nonnormal subgroup, not at a closed nonopen subgroup. These
are strictly positive-degree conclusions, corresponding to the closed-subgroup
clause of Neukirch–Schmidt–Wingberg, I §3, Proposition 1.3.7; they do not
assert degree-zero vanishing or all-integer Tate acyclicity.

### Normal-quotient coinduction

For `[Ring k] [TopologicalSpace k]`, a compact topological group `G`, any
normal subgroup `N` and a discrete, jointly continuous `B : TopRep k G`, the
[normal-quotient coinduction equivalence](ContinuousGroupCohomology/CoinducedInvariants.lean)
identifies `TopRep.quotientInvariants N (TopRep.coind₁ B)` with
`TopRep.coind₁ (TopRep.of (ContRepresentation.trivial k (G ⧸ N) B))`
as representations of `G ⧸ N`. This is universe-polymorphic and requires no
closedness or openness of `N`, Hausdorff condition or choice of section. Its
forward and inverse maps satisfy `(P f)(mk N t) = B.ρ t⁻¹ (f t)` and
`(J F)(t) = B.ρ t (F (mk N t))`. The right-hand coefficient is the **whole**
`B`, not `B^N`, and has trivial quotient action. The
[sign-product and full-group clients](CGCExamples/CoinducedInvariants.lean)
exhibit `B^N = 0` with nonzero `B`, a quotient function moved by the residual
quotient action, and an invariant function whose value at the identity is
moved by `N`.

### Algebraic connecting maps, naturality and initial invariants

The [algebraic connecting-map guide](docs/CohomologyExactSequence.md) describes
a connecting `k`-linear map in each natural degree and proves the three
recurring exactness assertions for the underlying modules of continuous cohomology.
They use locally compact `G`, discrete `B` and `C`, jointly continuous action
on `B`, injective `i`, exact `A → B → C`, and surjective `p`. The connecting
construction uses the cochain short exact sequence and Mathlib's homology
boundary; its representative formula and comparison with the
topologically split degree-zero map specify its sign. The algebraic assertions
also show that vanishing of the underlying `Hⁿ(G,B)` makes the connector mono,
vanishing of `Hⁿ⁺¹(G,B)` makes it epi, and both together give an isomorphism
whose forward arrow is the existing connector, for every natural `n`, including
zero. They do not establish continuity of this new map. For the integer sign action on
`ℤ --×2→ ℤ → ZMod 2`, the quotient invariant `1` has a nonzero connecting
class; its lack of an invariant integer lift is independently verified.
The [coinduced two-point row](CGCExamples/ConnectingIsomorphism.lean)
embeds trivial integers as constant functions and projects to signed integers
by subtracting the values at the two units. Its middle cohomology vanishes in
degrees one and two; the existing exactness statements show that its degree-one
connector has nonzero image and is surjective, without using a general
connecting-isomorphism result in these independent witness proofs. Separate
private clients apply the general mono, epi and isomorphism APIs to this row.
Two split rows give complementary degree-zero boundaries: for
`Multiplicative (ZMod 2)`, coinduced `B` has `H¹(G,B) = 0` but its degree-zero
connector is not mono; for the distinct group `ℤˣ`, the middle signed
coefficient `B` has `H⁰(G,B) = 0` but its degree-zero connector is not epi.
In that second row, the final coefficient `C` is the zero representation on `PUnit`.

Under the same short-exact-row and topological hypotheses, the
[initial-invariants module](ContinuousGroupCohomology/InitialInvariantsExactSequence.lean)
proves exactness of the underlying-module segment
`0 → Aᴳ → Bᴳ → Cᴳ → H¹(G,A) → H¹(G,B) → H¹(G,C)` at its five internal positions.
It uses Mathlib's invariant functor and natural degree-zero isomorphism and the
existing algebraic connector. The coefficient-level lemmas
`TopRep.mapInvariants_injective` and `TopRep.exact_mapInvariants` have weaker
hypotheses. Their earlier `ContinuousCohomology` names remain deprecated aliases. The
[example](CGCExamples/InitialInvariantsExactSequence.lean) checks a nonzero
displayed invariant inclusion and a nonsplit sign-action boundary. Its
coefficient-level obstruction and existing nonzero connector are independent
of the segment theorem. Neither surjectivity at `H¹(G,C)` nor continuity
of the connector is claimed.

The [coefficient-naturality theorem](ContinuousGroupCohomology/ConnectingNaturality.lean)
proves that, for two short exact coefficient sequences over the
same locally compact `G`, with the preceding discreteness and joint-continuity
hypotheses in each row, commuting coefficient maps `(α, β, γ)`
give `δ ≫ Hⁿ⁺¹(α) = Hⁿ(γ) ≫ δ′` for every natural degree. This is an equality
of underlying-module maps, not continuity of `δ`, change-of-group naturality,
or a topological delta-functor. The
[nonidentity sign-sequence client](CGCExamples/ConnectingNaturality.lean)
independently verifies the coefficient squares and a nonzero boundary, then
applies the naturality theorem.

See [Results and use](docs/Results.md) for the other constructions, full
module boundaries, conventions and client map.

## Using the library

Add the dependency to your `lakefile.toml`:

```toml
[[require]]
name = "continuous-group-cohomology"
git = "https://github.com/FormalFrontier/continuous-group-cohomology.git"
rev = "main"
```

GitHub `main` contains reviewed releases. Lake resolves the latest release
when you first add or update the dependency; `lake-manifest.json` records that
commit until the next update. To pin a particular release, replace `main`
with its full commit SHA from the published history and retain the manifest.
Use mutually compatible dependency releases and one common Mathlib revision;
adding the library does not establish compatibility with arbitrary other pins.

```lean
import ContinuousGroupCohomology
```

Import a `ContinuousGroupCohomology.*` leaf to limit dependencies. The
[`NativeCore` client](examples/NativeCore.lean) imports only the public root;
the [Results guide](docs/Results.md) links the specialized clients and APIs.

## Dependencies and builds

Use `elan` and Lake with `lean-toolchain`'s
`leanprover/lean4:v4.34.0-rc2`. `lakefile.toml` and `lake-manifest.json` fix
mathlib at `83abb3e776bdefcbc447a1e44d0debe4010039e5` and the released
`finite-group-tate-cohomology` dependency at
`d17f93bbc5b934f8b9f3cf077769a706a901608d` from
`https://github.com/FormalFrontier/finite-group-tate-cohomology.git`.
The closed-subgroup restriction module additionally uses
`profinite-groups` at `5f11ef67fb23396b63a644a3713391e2b9300546`,
with its resolved `group-theory` dependency at
`01047a79bed13ee795d40b61b777566f2160e5cc`.
Network access to the pinned dependencies and their matching cache is required.
Do not update the manifest when reproducing these pins.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake -KmaxJobs=2 --wfail build
```

Fetching the **matching mathlib cache must succeed before any build**; diagnose
a failed cache fetch rather than silently rebuilding mathlib from source.

Allow headroom for other jobs, and include toolchain, dependency and cache-download
time in fresh setup plans.

### Build targets and clients

The default build selects `ContinuousGroupCohomology` and `CGCExamples`.
The [complete registered client map](docs/Results.md#build-targets-and-clients)
explains each example and its mathematical boundary. The root collects the
public production API; clients import production modules to use their results.

For source elaboration of the aggregate-root client, from the repository root:

```sh
lake env lean examples/NativeCore.lean
```

## What is available

The [full module table](docs/Results.md#what-is-available) records all areas and
their material hypotheses: low-degree cohomology and transfer; finite-quotient
descent and colimits; coinduction, tensors and exact sequences; compact finite
Tate stages, norm rows and restricted limits; and representation interfaces.
The [manual guides](docs/README.md) and linked Lean declarations give usage
and exact universes. The generated API index covers only its stated historical
snapshot, not the complete current import graph.

## Classwise compact/discrete cohomology

For theorem names, class-dependent quotient coefficients, positive-degree
torsion, all-degree colimits and their distinct limitations, see the
[classwise guide](docs/Results.md#classwise-compactdiscrete-cohomology).

### Discrete linear Hom

See [the Hom interface](docs/Results.md#discrete-linear-hom) for the separate
scalar-continuity and four joint-action continuity criteria, inverse-oriented
conjugation and sign-representation examples.

### Degree-one torsion

See [degree-one torsion](docs/Results.md#degree-one-torsion) for the five public
declarations, their compact/discrete/joint-continuity hypotheses, the
class-dependent open-subgroup index and production-module imports.

## Scope and migration

The library is not a construction of general completed continuous Tate
cohomology or continuous homology. Finite-stage and compact-limit results
have their stated finite, continuity, separation and chosen `LevelCompact`
hypotheses; they do not imply general inverse-limit exactness or unconditional
transition surjectivity. The full-open-normal norm limit sequence supplies its
two exact middle pairs and compact universal-norm quotient under its own
hypotheses. Coefficient-ring topology and topological-module comparison are
separate obligations, not implicit in compact additive-group models.

Classwise finite-quotient lifts do not assert degree-zero torsion, acyclicity,
vanishing or uniform quotient bounds. The all-degree topological colimit uses
class-dependent refinements, not fixed-stage positive-degree injectivity.
The [full scope and migration notes](docs/Results.md#scope) distinguish the
provided APIs from excluded constructions; removing an unavailable import
does not supply its missing mathematics. Source-specific coverage is separate
from the mathematical API.

## References

- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1.1 (the correction to its finite-generation
  hypothesis credits Siyan Daniel Li). The discrete direct-sum, tensor and
  linear-Hom results extend its profinite, integer-module setting.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §3 (integral finite-group function–tensor formula
  with twisted action). The underlying equivalence extends to arbitrary finite
  index types over commutative semirings; the left-regular factor action for
  finite groups is inferred from the formula and twisted action.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §3, Proposition (1.3.6)(ii) (normal-invariants
  clause). The coinduction equivalence extends this clause from closed normal
  subgroups of profinite groups to arbitrary normal subgroups of compact
  topological groups with discrete, jointly continuous coefficients.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §3, Proposition 1.3.6(ii) (closed-subgroup
  restriction clause). The restriction isomorphism allows an arbitrary
  topological group when the subgroup and coset space are locally compact and
  a continuous coset section is chosen. It uses the whole continuous-function
  coefficient space with its generally nontrivial pointwise subgroup action;
  its profinite specialization covers every closed subgroup.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §3, Proposition 1.3.7 (positive-degree
  closed-subgroup clause). The coinduced contraction and Mathlib's
  coefficient maps give positive vanishing after all closed restrictions;
  the whole-group isomorphic-coefficient theorem is a further consequence.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1, Exercise 4 (continuous sections of profinite
  coset projections). The chosen section is not a canonical group splitting.
- Mathlib, especially `Representation.directSum`, `Representation.tprod` and
  `TopRep` for representation constructions, and its continuous-cohomology,
  topological and categorical foundations. Its representation-theory and
  topological-action formalizations include conjugation and invariants
  (Antoine Labelle), intertwining maps (Stepan Nesterov and Edison Xie),
  and the open-stabilizer criterion (Yury Kudryashov).
- Formal Frontier's earlier diagonal-insertion formalization developed the swap,
  diagonal and recursive insertion for coinduced cochains. The constructions
  here adapt that approach to this library's `TopRep` resolution and API.
- [Finite group Tate cohomology](https://github.com/FormalFrontier/finite-group-tate-cohomology),
  the formal library providing finite Tate definitions and norm maps; see
  [attribution](docs/attribution.md).
- [Profinite Groups](https://github.com/FormalFrontier/profinite-groups/tree/5f11ef67fb23396b63a644a3713391e2b9300546),
  the formal library providing the continuous coset-section theorem and chosen
  representatives for closed subgroups used in the profinite restriction
  isomorphism. Its section proof uses the
  [Group Theory open-quotient theorem](https://github.com/FormalFrontier/group-theory/tree/01047a79bed13ee795d40b61b777566f2160e5cc);
  see [attribution](docs/attribution.md).

## Credits and license

**Authors: Formal Frontier Agents.** Original project contributions are
licensed under [Apache-2.0](LICENSE). The collective author name records
AI-assisted formalization. [Attribution](docs/attribution.md) distinguishes
original contributors, mathematical sources and reused expression, and
preserves authentic third-party notices without asserting copyright ownership.

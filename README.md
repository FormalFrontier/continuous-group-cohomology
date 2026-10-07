# Continuous group cohomology: native finite-stage colimits and compact finite quotients

## Headline results

This Lean library develops low-degree continuous group cohomology and
finite-index transfer, compact-group degree-one torsion, finite-level Tate
deflation and compact finite-bar homology. It also develops compact exceptional
Tate stages and diagrams, coefficient naturality, actual finite and full-system
Tate norm rows, and restricted universal-norm comparisons. The guides and table
below distinguish these constructions and their hypotheses.

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

Arbitrary algebraic direct sums of discrete representations and tensors of two
discrete representations inherit a chosen discrete topology. Their actions are
jointly continuous when the input actions are, for a topologized monoid without
a continuity assumption on its multiplication. Direct sums work over a
topologized ring, and tensors over a topologized commutative ring.

The [sign-product example](ContinuousGroupCohomology/DiscreteProduct.lean)
shows an existential boundary: the countable product of finite-discrete integer
unit groups acts coordinatewise on integer sequences. The ordinary product
action is jointly continuous but its carrier is not discrete; on a separate
chosen-discrete copy of the algebraic product, each sign acts continuously but
the action is not jointly continuous. Its nonzero constant-one vector has
nonopen singleton stabilizer. This does not concern every infinite product or
assert a categorical product construction.

Discrete linear Hom carries all linear maps with the chosen discrete topology
and inverse-oriented conjugation. Its action is jointly continuous for a
discrete acting group, a finite `T₁` acting group, a finitely generated source
with discrete jointly continuous inputs, or a finite possibly non-`T₁` group
with such inputs. Scalar continuity is separate: it follows from discrete
scalars, or from finite generation with a discrete continuously-scaled target.

For compact topological groups and discrete coefficients,
[diagonal insertion](ContinuousGroupCohomology/CoinducedAcyclic.lean)
gives a map on the recursively iterated coinduced homogeneous cochains with an
explicit evaluation law. This insertion contracts the cochain complex in every
positive degree, so continuous cohomology with coinduced discrete coefficients
vanishes there. Degree-zero vanishing is false even for the two-element group
acting trivially on nonzero integers (see the
[two-element-group client](CGCExamples/CoinducedAcyclic.lean)).

Import `ContinuousGroupCohomology` for the complete public native core, or import a
`ContinuousGroupCohomology.*` leaf to limit dependencies. The
[`NativeCore` client](examples/NativeCore.lean) imports only the public root.

**Authors: Formal Frontier Agents.** Original project contributions are
offered under [Apache-2.0](LICENSE). Actual contributors, reused expression
and authentic notices are documented in [attribution](docs/attribution.md).

The [finite-deflation guide](docs/FiniteDeflation.md) covers finite-level maps;
the [compact exceptional Tate guide](docs/FiniteTateTopology.md) covers the
compact kernel/quotient, continuous finite coinvariant deflation, compact
diagrams, additive comparisons and compact limits;
the [compact coefficient and norm functoriality guide](docs/CompactCoefficientFunctoriality.md)
covers the continuous stage/limit maps and restricted norm diagrams;
the [finite Tate diagrams guide](docs/FiniteTateDiagrams.md) covers the newly
restored diagrams, limits and coefficient functoriality.
The [finite norm-row guide](docs/CompactFiniteTateNormSequence.md) and
[full-system norm-limit guide](docs/CompactTateNormLimitSequence.md) describe
the distinct finite-stage and inverse-limit results.
The [compact norm-row naturality guide](docs/CompactTateNormNaturality.md)
describes their actual coefficient-map squares and natural quotient isomorphism.
The [compact universal-norm limit guide](docs/CompactUniversalNormLimits.md)
describes the distinct restricted relative-norm comparison and its naturality.
The [degree-one torsion guide](#degree-one-torsion)
covers the compact-group result. For compact finite-bar homology, comparison
and functoriality, see the [manual compact-bar API guide](docs/CompactBar.md).
The [historical native API reference](docs/API.md), its [reproduction guide](docs/README.md)
and [machine-readable manifest](docs/api-manifest.json) describe a **historical
analyzed snapshot**: they do not index later-added modules and clients or the
current root's import graph. Their source
links resolve to the matching [published historical release](https://github.com/FormalFrontier/continuous-group-cohomology/tree/be74358d7b1140e76ab6b2ad72f6aa068138e687),
not mutable line numbers in the current modules; the API digest and renderer
agree on the checked-in historical index.

## Classwise compact/discrete cohomology

For a topologized ring `k`, compact topological group `G`, and discrete
`X : TopRep k G` with a jointly continuous action, import
`ContinuousGroupCohomology.CompactDiscreteTorsion` or the public root.
`ContinuousCohomology.exists_openNormal_quotient_class_lift` expresses each
class in any degree as the image of a class on a finite open-normal quotient
with coefficients in `TopRep.quotientInvariants N.toSubgroup X`.
`ContinuousCohomology.exists_openNormal_quotient_card_nsmul_eq_zero` gives,
in positive degree, an annihilating quotient order for each class, and
`ContinuousCohomology.compactDiscrete_isAddTorsion` packages the resulting
`IsAddTorsion (continuousCohomology (n + 1) X)`. See the
[classwise descent and torsion guide](docs/CompactDiscreteTorsion.md),
[quotient-invariants guide](docs/QuotientInvariants.md),
[finite-stage cochain guide](docs/FiniteStageCochains.md), and
[finite-averaging guide](docs/FiniteAveraging.md) for hypotheses and proofs.
The [compact/discrete factor guide](docs/CompactDiscreteFactor.md),
[resolution-image guide](docs/ResolutionImage.md),
[finite-stage resolution guide](docs/FiniteStageResolution.md), and
[cochain-injectivity guide](docs/CochainInjectivity.md) describe reusable
prerequisites and their limitations. All eight guides describe ordinary-import
clients under `examples/*Native.lean`.
The compact finite-quotient and native discreteness checks share
[`ContinuousTorsionNative`](examples/ContinuousTorsionNative.lean) with the
degree-one torsion clients. This union replaces all three separately checked
proof-import environments, including the former Torsion-only host;
[`CompactDiscreteTorsionNative`](examples/CompactDiscreteTorsionNative.lean) and
[`DiscreteCohomologyNative`](examples/DiscreteCohomologyNative.lean) are now
declaration-free entrypoints retaining their original public producer imports;
both import the host ordinarily rather than re-exporting it. The recommended
production imports above are unchanged.

The quotient and its order may depend on the class. This does **not** prove
degree-zero torsion, a uniform bound or quotient, injectivity on cohomology
at a fixed stage, acyclicity,
vanishing or source-specific coverage. The older degree-one torsion and
comparison API below remains available unchanged.

The new [native finite-stage colimit guide](docs/FiniteStageColimit.md) explains
the all-degree comparison, nonuniform equality detection and arbitrary target
cocones. Its [algebraic-boundary](docs/HomologyBoundary.md),
[seeded cochain](docs/SeededCochains.md),
[transition](docs/QuotientTransitions.md),
[eventual equality](docs/FiniteStageBoundary.md),
[discreteness](docs/DiscreteCohomology.md) and
[diagram](docs/OpenNormalDiagram.md) guides describe the separate reusable
ingredients and their individual hypotheses.

## What is available

| Area | Native modules | Mathematical boundary |
| --- | --- | --- |
| Continuous low-degree cohomology | `DegreeOne`, `LowDegreeExact`, `NormalizedCohomology`, `NestedInvariants` | Crossed cocycles modulo principal cocycles compute degree one with locally compact groups and jointly continuous actions; the degree-zero/one connecting sequence uses a continuous, not necessarily equivariant, splitting. |
| Transfer | `Corestriction`, `Composition`, `Mackey` | Open finite-index subgroup transfer and degree-one functoriality, composition and Mackey relations with the hypotheses in each declaration. |
| Degree-one torsion | `Torsion` | Compact topological group, discrete jointly continuous representation over a topologized ring; each continuous `H¹` class has finite additive order. The index is class-dependent. |
| Classwise finite-quotient cohomology | `QuotientInvariants`, `CochainInjectivity`, `ResolutionImage`, `FiniteStageResolution`, `FiniteStageCochains`, `FiniteAveraging`, `CompactDiscreteTorsion`, `Topology.ContinuousMap.CompactDiscrete`, `Topology.Algebra.CompactGroup.DiscreteFactor` | Native all-degree classwise lifting with genuine quotient-invariant coefficients; positive-degree class-dependent annihilation and additive torsion. No uniform stage/order or degree-zero torsion. |
| Coinduced insertion | [`CoinducedAcyclic`](ContinuousGroupCohomology/CoinducedAcyclic.lean) | Diagonal insertion on the actual iterated coinduced resolution, with evaluation laws and a nonzero [two-element-group client](CGCExamples/CoinducedAcyclic.lean). In positive degree, insertion contracts homogeneous cochains and coinduced-coefficient cohomology vanishes; the degree-zero analogue is false. |
| Native finite-stage colimit | `Algebra.Category.ModuleCat.Topology.HomologyBoundary`, `SeededCochains`, `QuotientTransitions`, `FiniteStageBoundary`, `DiscreteCohomology`, `OpenNormalDiagram`, `FiniteStageColimit` | Actual `TopModuleCat` filtered colimit in every degree, including zero, from class-dependent dual-index refinements; arbitrary target cocones. Compact/discrete/joint-continuity hypotheses apply to the colimit, but not to the generic boundary or transition diagram; no closed-range quotient, fixed-stage injectivity or uniform refinement. |
| Finite constructions | `FiniteCoinvariants`, `FiniteNegativeDeflation`, `ExceptionalDeflation`, `FiniteDeflationTransitivity` | Finite acting groups, orbit-difference relations, closed quotient under compact Hausdorff coefficients, and finite-level deflation in Tate degrees `-1` and `0` with nested-normal-subgroup transitivity via the pinned finite-group Tate library. No general nonpositive Tate theory for arbitrary topological groups is constructed. |
| Compact exceptional Tate stages | `FiniteTateTopology`, `FiniteCoinvariantDeflation`, `ExceptionalTateDeflationTopology` | Compact Hausdorff additive closed-kernel/quotient models in degrees `-1` and `0`, continuous coinvariant and induced Tate deflation with identity/composition and additive comparison to algebraic Tate deflation; finite residual-kernel hypotheses apply. No ring topology or topology on algebraic Tate groups is asserted. |
| Compact exceptional Tate diagrams and limits | `CompactExceptionalTateDiagrams`, `CompactExceptionalTateLimits` | Continuous compact deflation diagrams in degrees `-1` and `0`, natural isomorphisms of underlying additive diagrams with algebraic Tate diagrams, compact Hausdorff additive limits, projection equations and eventual-range images. Requires chosen `LevelCompact A` in a common universe; these two leaves alone do not supply coefficient maps, surjectivity or inverse-limit exactness. |
| Compact finite and full-system norm rows | `CompactFiniteTateNormSequence`, `CompactTateNormLimitSequence` | Actual finite coinvariant/kernel/invariant/quotient maps form two exact middle pairs; the full open-normal compact limits yield the corresponding exact row, injective/onto endpoints, universal-norm kernel/range and compact quotient iso. Requires common-universe `R`, `G`, `Rep` and chosen `LevelCompact`; these two modules alone do not supply coefficient naturality. No coefficient-ring topology, onto coinvariant/kernel transitions, arbitrary restricted-system identification, arithmetic or all-degree Tate result. |
| Full norm-row coefficient naturality | `CompactTateNormNaturality` | For arbitrary level-compact coefficient morphisms, the actual finite-coinvariant diagram/limit and the three full norm-row arrows are natural. The coefficient action descends continuously to the actual closed-universal-norm quotient, and the existing quotient-to-degree-zero-limit iso is natural for that independently descended action. No ring or ambient-representation topology, extra preservation/surjectivity, arbitrary restricted-system identification, arithmetic or all-degree Tate result. |
| Compact relative-norm limits | `CompactUniversalNormLimits` | For chosen compact invariant topologies with common-universe level-compact data, full-limit projection range equals universal norms, restricted universal-norm transitions are onto, and the genuine inclusion of any closed restricted system containing universal norms induces an isomorphism of actual compact additive limits with both projection equations. A specified restricted morphism must preserve its chosen coefficients (`map_mem`); universal norms are functorial for every level-compact coefficient map. No full/arbitrary transition surjectivity, ambient coefficient topology, identification with the Tate norm row, arithmetic or all-degree Tate result. |
| Compact coefficient and norm functoriality | `CompactExceptionalTateCoefficientMaps`, `CompactExceptionalTateLimitFunctoriality`, `RestrictedLevelCompactFunctoriality` | Level-compact morphisms give continuous compact coefficient/exceptional-Tate stage maps, natural maps of their compact limit diagrams and limits, and morphisms of selected restricted relative-norm diagrams. Arbitrarily chosen restricted systems require preservation; full and universal-norm systems are canonically functorial. No extra ring/ambient-coefficient topology or surjectivity is assumed. |
| Finite Tate diagrams | `FiniteTateDiagrams`, `NonpositiveTateLimits`, `NonpositiveTateFunctoriality` | Covariant deflation along open normal inclusions of a profinite group, `TopModuleCat` limits and coefficient-morphism functoriality for the homological model of degrees below `-1` and exceptional degrees `-1` and `0`. No identification with completed continuous Tate theory. |
| Compact finite bars | `CompactNegativeTate`, `CompactBarFunctoriality` | Finite-group bar chains with compact Hausdorff additive coefficients and individually continuous action maps; closed-boundary homology, additive comparison with finite Tate degrees `-(n + 2)`, and continuous functoriality for equivariant continuous coefficient maps. |
| Quotients and actions | `ClosedTopologicalCoinvariants`, `QuotientConjugationAction`, `TopologicalQuotientConjugationAction`, `TopologicalModN`, `ContinuousGroupExtension` | Closed versus algebraic coinvariants, quotient conjugation, continuous group extensions, and closed reduction modulo `n`; pointwise continuous actions do not imply jointly continuous actions. |
| Compact groups and limits | `CompactAddCommGroup`, `CompactAddCommGroupLimits`, `CompactFiniteHomology`, `CompactTopModuleLimits` | Compact Hausdorff additive groups, finite products, inverse limits and finite-stage homology constructions; cofiltered limit statements include empty indexing categories where stated. |
| Compact levels | `LevelCompact`, `LevelCompactFunctoriality`, `LevelCompactNorm`, `RestrictedLevelCompact` | Compact level systems, functoriality, relative norms and restricted systems with explicit finite-stage hypotheses. |
| Universe and representation interfaces | `TopModuleCatUlift`, `TopRepUlift`, `GroupExtensionUlift`, `HomogeneousCochainsUlift`, `ContinuousCohomologyUlift` | Universe transport and compatibility for the named continuous cohomology and extension constructions. |
| Discrete representation sums and tensors | `TopRepDiscrete` | Arbitrary varying-index algebraic sums and two-factor tensors with discrete output topology, canonical Mathlib actions, coordinate/pure-tensor equations and jointly continuous actions when the inputs have them. |
| Discrete linear Hom | `TopRepDiscreteHom` | All linear maps with the discrete carrier topology and inverse-oriented conjugation, separate scalar-continuity criteria and four joint-action continuity criteria. |
| Sign-product boundary | `DiscreteProduct` | The countable integer-unit sign product acts jointly continuously on integer sequences with their nondiscrete product topology; a separately discrete copy has continuous fixed-sign operators but no jointly continuous action. |

The [`ContinuousGroupCohomology.lean`](ContinuousGroupCohomology.lean) root
collects the production API. The production leaves and clients
use Lean's native `module` system. A compact additive-group limit or finite-stage
homology *model* is not a construction of general completed continuous homology.
Finite quotients require their actual finite-index/finite-group hypotheses;
topological and compact results require the relevant continuity, compactness and
separation assumptions, not merely algebraic group structure. Consult theorem
statements and individual module documentation for precise universes and instances.

### Discrete linear Hom

`ContinuousGroupCohomology.TopRepDiscreteHom` equips all `k`-linear maps with
a discrete carrier and Mathlib's inverse-oriented conjugation action. Its
action formula and fixed-map criterion compare with Mathlib's invariant and
intertwining-map API. Scalar continuity is automatic for discrete scalars,
including `k = ℤ`; finite generation of the source gives a separate route
when the target has discrete, continuous scalar multiplication.

Finite-source scalar continuity and four group-action joint-continuity routes
hold under their separate hypotheses. The four group conditions are:
discrete `G`; finite `T₁` `G`; a finitely generated source with discrete,
jointly continuous inputs; and finite possibly non-`T₁` `G` with discrete,
jointly continuous inputs. A finite acting group alone does not ensure
scalar continuity for arbitrary `k`. The
[`DiscreteHom` client](ContinuousGroupCohomologyExamples/DiscreteHom.lean)
instantiates the action and statements on sign representations, including
an infinite-rank source and an infinite acting group.

### Degree-one torsion

Import `ContinuousGroupCohomology.Torsion` for the five declarations in namespace
`ContinuousCohomology` (or import the public root). For a `TopRep.{max v w} k G`
over a ring `k` with a topology and a topological group `G`, the statements
provide:

- `continuousCrossedHom_apply_one X f`: a crossed cocycle vanishes at `1`;
- `zeroOpenSubgroup X f`: its zero fibre is an open subgroup, not necessarily normal,
  when the representation carries the discrete topology;
- `zeroOpenSubgroup_finiteIndex X f`: compactness of `G` makes that subgroup's
  index finite;
- `zeroOpenSubgroup_index_nsmul X f`: for a jointly continuous action, its
  finite index annihilates the image of `f` in the quotient by principal cocycles;
- `isAddTorsion_degreeOne X`: `IsAddTorsion (continuousCohomology 1 X)`.

The final theorem assumes `[IsTopologicalGroup G] [DiscreteTopology X]`,
`[TopRep.JointlyContinuous X]` and `[CompactSpace G]`. It derives local compactness
inside its proof; it assumes neither `T2Space G` nor coefficient torsion,
finite generation, a trivial action, or a common group-wide exponent. Transfer
follows restriction in the classwise index argument; no higher-degree claim is
made. [`ContinuousTorsionNative`](examples/ContinuousTorsionNative.lean) checks
both the integral-representation specialization and restriction to an arbitrary
open subgroup of `G`, without imposing a trivial action there. Its proof-import
environment also contains compact finite-quotient and discreteness clients, so
these checks no longer test the Torsion-only import environment in isolation.

## Dependencies and builds

Use `elan` and Lake with `lean-toolchain`'s
`leanprover/lean4:v4.34.0-rc2`. `lakefile.toml` and `lake-manifest.json` fix
mathlib at `83abb3e776bdefcbc447a1e44d0debe4010039e5` and the released
`finite-group-tate-cohomology` dependency at
`d17f93bbc5b934f8b9f3cf077769a706a901608d` from
`https://github.com/FormalFrontier/finite-group-tate-cohomology.git`.
Authorized access to this private dependency and network access to the pinned
mathlib/transitive dependencies and their cache are required. No source-research
checkout is needed. Do not update the manifest when reproducing these pins.

```sh
elan toolchain install leanprover/lean4:v4.34.0-rc2
lake exe cache get
LEAN_NUM_THREADS=2 lake -KmaxJobs=2 --wfail build
```

Fetching the **matching mathlib cache must succeed before any build**; diagnose
a failed cache fetch rather than silently rebuilding mathlib from source.

### Build-time and memory baseline

A previous 56-leaf/thirty-two-client combined root/client CI build at the then-pinned
Lean, mathlib and Tate revisions took about **6.6 minutes** after fetching the
matching mathlib cache. This is an indicative observation, **not** a benchmark
of the current production/client graph or a guaranteed build time.
An earlier, smaller graph had a shared 15 GiB memory limit and a lifetime
high-water reading of about 14.2 GiB after its client build; this is neither
peak RSS for a command nor a measured minimum. Allow headroom for other jobs,
and include toolchain, dependency and cache-download time in fresh setup plans.

### Build targets and clients

`ContinuousGroupCohomology` compiles the public root and its 67 imports;
`CGCExamples` compiles precisely these forty-three native clients, also selected by
the default build:

- [`CompactFoundationNative`](examples/CompactFoundationNative.lean),
  [`CompactExceptionalTateCoefficientMapsNative`](examples/CompactExceptionalTateCoefficientMapsNative.lean),
  [`CompactExceptionalTateLimitFunctorialityNative`](examples/CompactExceptionalTateLimitFunctorialityNative.lean),
  [`CompactExceptionalTateNative`](examples/CompactExceptionalTateNative.lean),
  [`CompactFiniteTateNormSequenceNative`](examples/CompactFiniteTateNormSequenceNative.lean),
  [`CompactTateNormLimitSequenceNative`](examples/CompactTateNormLimitSequenceNative.lean),
  [`CompactTateNormNaturalityNative`](examples/CompactTateNormNaturalityNative.lean),
  [`CompactUniversalNormLimitsNative`](examples/CompactUniversalNormLimitsNative.lean),
  [`CompactNegativeBarNative`](examples/CompactNegativeBarNative.lean),
  [`ContinuousTorsionNative`](examples/ContinuousTorsionNative.lean),
  [`ExceptionalDeflationNative`](examples/ExceptionalDeflationNative.lean),
  [`ExceptionalTateDeflationTopologyNative`](examples/ExceptionalTateDeflationTopologyNative.lean),
  [`FiniteCoinvariantDeflationNative`](examples/FiniteCoinvariantDeflationNative.lean),
  [`FiniteCoinvariantsNative`](examples/FiniteCoinvariantsNative.lean),
  [`FiniteDeflationTransitivityNative`](examples/FiniteDeflationTransitivityNative.lean),
  [`FiniteNegativeNative`](examples/FiniteNegativeNative.lean),
  [`FiniteTateTopologyNative`](examples/FiniteTateTopologyNative.lean),
  [`LevelCompactNative`](examples/LevelCompactNative.lean);
- [`LevelCompactNormNative`](examples/LevelCompactNormNative.lean),
  [`NestedInvariantsNative`](examples/NestedInvariantsNative.lean),
  [`NonpositiveTateDiagramsNative`](examples/NonpositiveTateDiagramsNative.lean),
  [`RestrictedLevelNative`](examples/RestrictedLevelNative.lean),
  [`RestrictedLevelCompactFunctorialityNative`](examples/RestrictedLevelCompactFunctorialityNative.lean), and
  [`NativeCore`](examples/NativeCore.lean);
- [`CompactDiscreteFactorNative`](examples/CompactDiscreteFactorNative.lean),
  [`QuotientInvariantsNative`](examples/QuotientInvariantsNative.lean),
  [`CochainInjectivityNative`](examples/CochainInjectivityNative.lean),
  [`ResolutionImageNative`](examples/ResolutionImageNative.lean),
  [`FiniteStageResolutionNative`](examples/FiniteStageResolutionNative.lean),
  [`FiniteStageCochainsNative`](examples/FiniteStageCochainsNative.lean),
  [`FiniteAveragingNative`](examples/FiniteAveragingNative.lean), and
  [`CompactDiscreteTorsionNative`](examples/CompactDiscreteTorsionNative.lean);
- [`HomologyBoundaryNative`](examples/HomologyBoundaryNative.lean),
  [`SeededCochainsNative`](examples/SeededCochainsNative.lean),
  [`QuotientTransitionsNative`](examples/QuotientTransitionsNative.lean),
  [`FiniteStageBoundaryNative`](examples/FiniteStageBoundaryNative.lean),
  [`DiscreteCohomologyNative`](examples/DiscreteCohomologyNative.lean),
  [`OpenNormalDiagramNative`](examples/OpenNormalDiagramNative.lean), and
  [`FiniteStageColimitNative`](examples/FiniteStageColimitNative.lean);
- [`TopRepDiscrete`](CGCExamples/TopRepDiscrete.lean), the discrete sum and tensor client;
- [`CoinducedAcyclic`](CGCExamples/CoinducedAcyclic.lean), the coinduced-coefficient client;
- [`DiscreteHom`](ContinuousGroupCohomologyExamples/DiscreteHom.lean); and
- [`DiscreteProduct`](ContinuousGroupCohomologyExamples/DiscreteProduct.lean), the
  coordinatewise sign-product boundary client.

The finite-stage resolution, boundary, colimit, quotient-invariants,
resolution-image, cochain, seeded descent, transition and diagram client proofs
elaborate together in `examples.FiniteStageResolutionNative`: seven current
environments combine ten original isolated environments. Their forwarding roots
retain their original producer imports and visibility for importers, but
building those roots does not repeat the original isolated proof elaborations.
Import the corresponding `ContinuousGroupCohomology` production leaves for their APIs.

For an explicit fresh source elaboration of the aggregate-root client:

```sh
lake env lean examples/NativeCore.lean
```

The other client paths above can likewise be given to `lake env lean`.
Representative `#print axioms` commands in the client files report selected
proof dependencies. Release verification uses an applicable successful build and
a complete actual transitive-axiom audit of repository declarations, including
private declarations. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted. The ordinary Lean build checks proofs; separate exhaustive stored-proof
rechecking is not a release prerequisite. Documentation, API claims, metadata,
rights and release history still need independent review. A successful build alone
is not a complete axiom or rights check.

## Scope and migration

This native core does **not** ship earlier scalar-extension experiments,
other finite Tate comparison diagrams, general inverse-limit exactness for
arbitrary systems, or the broader completed continuous Tate and topology layers.
The named full-open-normal compact Tate norm limit sequence *does* supply its
two exact middle pairs and compact universal-norm quotient. The compact finite-bar
construction supplies neither a
topological-module comparison over an unspecified scalar topology nor a general
completed continuous homology construction. Earlier `design/`
notes and eight legacy clients are also excluded. Historical development is
retained in project history but not imported, installed or required by this
library. Migrate code importing an excluded module to the named retained API
where its mathematics matches; otherwise retain an earlier development
revision separately until the missing functionality is reviewed and added.
Removing a legacy import alone does not recreate a deferred theorem. The compact
exceptional Tate modules supply continuous deflation for their stated finite
levels and compact inverse limits with eventual-range images, not general
completed continuous Tate cohomology or unconditional surjectivity.

This is an explicitly scoped library, not a formalization of general
completed continuous Tate cohomology or general continuous homology. The
classwise finite-stage lift does not assert degree-zero torsion, acyclicity,
vanishing or uniform finite-quotient bounds. The all-degree colimit is a
separate result with class-dependent equality refinements and no fixed-stage
injectivity claim. A source-specific coverage determination is separate from
the mathematical API in this library.

## References

- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1.1 (the correction to its finite-generation
  hypothesis credits Siyan Daniel Li). The discrete direct-sum, tensor and
  linear-Hom results extend its profinite, integer-module setting.
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

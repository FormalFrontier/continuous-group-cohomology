# Continuous group cohomology: native core

A Lean library of low-degree continuous group cohomology, degree-one transfer
and compact-group degree-one torsion,
topological quotients and actions, finite-group coinvariants and finite-level
deflation in Tate degrees `-1` and `0`, finite profinite-quotient Tate diagrams
and their topological limits, compact finite-bar homology, compact Hausdorff
additive-group limit models, and compact exceptional finite Tate stages with
continuous deflation at nested open normal levels, their compact diagrams,
additive natural comparisons and compact additive limits.
Coefficient morphisms also act continuously on those compact exceptional Tate
stages and limits and on selected restricted relative-norm diagrams.
The actual compact finite Tate norm row and its full-open-normal inverse-limit
sequence identify the universal-norm kernel, range and compact quotient.
Level-compact coefficient maps act naturally on this actual row and on its
independently descended closed-universal-norm quotient.
Separately, the full invariant relative-norm limit projects onto precisely
the universal norms; their restricted norms are surjective, and inclusion of
any closed restricted system containing them induces a natural compact-limit
isomorphism. This does not assert full-transition surjectivity or identify
that relative-norm diagram with the finite Tate norm row.
Import `ContinuousGroupCohomology` for the complete public native core, or import a
`ContinuousGroupCohomology.*` leaf to limit dependencies. The
[`NativeCore` client](examples/NativeCore.lean) imports only the public root.

**Authors: Formal Frontier Agents.** Original project contributions are
offered under [Apache-2.0](LICENSE). Actual contributors, reused expression,
notices and outstanding rights checks are recorded in
[attribution](docs/attribution.md); a license label is not a whole-artifact
rights determination.

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
analyzed snapshot**: they do not index the twenty additional leaves, sixteen
direct clients, or the current root's import graph.

## What is available

| Area | Native modules | Mathematical boundary |
| --- | --- | --- |
| Continuous low-degree cohomology | `DegreeOne`, `LowDegreeExact`, `NormalizedCohomology`, `NestedInvariants` | Crossed cocycles modulo principal cocycles compute degree one with locally compact groups and jointly continuous actions; the degree-zero/one connecting sequence uses a continuous, not necessarily equivariant, splitting. |
| Transfer | `Corestriction`, `Composition`, `Mackey` | Open finite-index subgroup transfer and degree-one functoriality, composition and Mackey relations with the hypotheses in each declaration. |
| Degree-one torsion | `Torsion` | Compact topological group, discrete jointly continuous representation over a topologized ring; each continuous `H¹` class has finite additive order. The index is class-dependent. |
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

The [`ContinuousGroupCohomology.lean`](ContinuousGroupCohomology.lean) root
publicly imports all 47 listed production leaves. All 47 and the twenty-four clients
use Lean's native `module` system. A compact additive-group limit or finite-stage
homology *model* is not a construction of general completed continuous homology.
Finite quotients require their actual finite-index/finite-group hypotheses;
topological and compact results require the relevant continuity, compactness and
separation assumptions, not merely algebraic group structure. Consult theorem
statements and individual module documentation for precise universes and instances.

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
open subgroup of `G`, without imposing a trivial action there.

## Dependencies and builds

Use `elan` and Lake with `lean-toolchain`'s
`leanprover/lean4:v4.34.0-rc2`. `lakefile.lean` and `lake-manifest.json` fix
mathlib at `e37d88a26f3791ed5a93daa1f949af1021b8d103` and the **official
private** `finite-group-tate-cohomology` dependency at
`fda003db3d06774f28b47232e8248852ffdbfc0d` from
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

For the **earlier 27-leaf/eight-client graph**, on 2026-09-26 with Tate pin
`19c1d8ce0f11e9ce7af8ce5ae1e2479aa7cd0796`, after the matching
mathlib cache fetch and an initial single-leaf build, the root build took
**355.940 seconds** using Lake's normal scheduler. The subsequent eight-client
`CGCExamples` build took **7.794 seconds**, and the subsequent warm default build
took **2.499 seconds**. These are sequential workload observations, not three
independent clean builds. Toolchain installation, dependency checkout and cache
download time are excluded; any dependency compilation performed by a measured
build command is included. These old observations do **not** benchmark this
then-current 40-leaf/seventeen-client graph or its renewed Tate dependency;
it does not measure the later 43-leaf/twenty-client, 45-leaf/twenty-two-client
or the later 46-leaf/twenty-three-client and this 47-leaf/twenty-four-client graph.

The build environment had a shared **15 GiB** memory limit. Its lifetime cgroup
high-water reading was **14,701,797,376 bytes** after the root build and
**15,215,030,272 bytes** (about **14.2 GiB**) after the client build. These are
shared lifetime readings, **not per-command peak RSS** or a measured minimum
memory requirement. Plan additional headroom above that observed high-water
mark for other processes. CPU allocation and hardware were not recorded in this
baseline, so timings are indicative rather than portable guarantees; fresh setup
also depends on network access and available caches.

### Build targets and clients

`ContinuousGroupCohomology` compiles the public root and its 47 imports;
`CGCExamples` compiles precisely these twenty-four native clients, also selected by
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
  [`NativeCore`](examples/NativeCore.lean).

For an explicit fresh source elaboration of the aggregate-root client:

```sh
lake env lean examples/NativeCore.lean
```

The other twenty-three client paths above can likewise be given to `lake env lean`.
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

This is an explicitly scoped library, not an all-degree Tate or continuous
cohomology or general completed continuous homology formalization. The recovered
four-file contribution was independently reviewed and accepted on 2026-09-26 at
`c0dae4cfc6d0a5c6065d9a6b7db1941a54b63b26`. That ordinary code acceptance
does not establish source coverage. Exact release and publication decisions are
recorded separately for each public-lineage commit. At this 2026-09-26 composition
checkpoint, finite deflation and compact finite bars had completed their reviewed
private releases; the degree-one torsion assembly and this combined finite Tate
diagram candidate still awaited their own final acceptance. The earlier diagram
review applies to its exact predecessor, not automatically to this assembly.
The original audit's missing private declarations were corrected by a complete
1,962-declaration base audit and a separate 67-declaration diagram/client audit.
The incomplete historical outputs remain preserved in the review records.
Neither those checks nor this preparation claims source coverage or publication
of this candidate; exact subsequent decisions belong to its review and release records.

The two compact exceptional Tate diagram/limit leaves and their direct client
were an **unreviewed destination promotion candidate at the 2026-09-27 author
handoff**, transferred from accepted incubator main
`aa65d3e5c96fbe5ddd6037f7e7b39fe82114ecf2`. Incubator review does not replace
independent destination review against the different pinned mathlib revision.
Exact subsequent destination acceptance and verified official publication are
recorded separately by the responsible maintainer; the author transfer alone
establishes neither. The historical API index concerns an earlier, narrower graph.

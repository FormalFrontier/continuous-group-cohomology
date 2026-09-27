# Continuous group cohomology: native core

A Lean library of low-degree continuous group cohomology, degree-one transfer
and compact-group degree-one torsion,
topological quotients and actions, finite-group coinvariants and finite-level
deflation in Tate degrees `-1` and `0`, finite profinite-quotient Tate diagrams
and their topological limits, compact finite-bar homology, compact Hausdorff
additive-group limit models, and compact exceptional finite Tate stages with
continuous deflation at nested open normal levels.
Import `ContinuousGroupCohomology` for the complete public native core, or import a
`ContinuousGroupCohomology.*` leaf to limit dependencies. The checked
[`NativeCore` client](examples/NativeCore.lean) imports only the public root.

**Authors: Formal Frontier Agents.** Original project contributions are
offered under [Apache-2.0](LICENSE). Actual contributors, reused expression,
notices and outstanding rights checks are recorded in
[attribution](docs/attribution.md); a license label is not a whole-artifact
rights determination.

The [finite-deflation guide](docs/FiniteDeflation.md) covers finite-level maps;
the [compact exceptional Tate guide](docs/FiniteTateTopology.md) covers the
compact kernel/quotient, continuous finite coinvariant deflation and comparisons;
the [finite Tate diagrams guide](docs/FiniteTateDiagrams.md) covers the newly
restored diagrams, limits and coefficient functoriality.
The [degree-one torsion guide](#degree-one-torsion)
covers the compact-group result. For compact finite-bar homology, comparison
and functoriality, see the [manual compact-bar API guide](docs/CompactBar.md).
The [historical native API reference](docs/API.md), its [reproduction guide](docs/README.md)
and [machine-readable manifest](docs/api-manifest.json) describe a **historical
analyzed snapshot**: they do not index the eleven additional leaves, eight
direct clients, or the current root's import graph.

## What is available

| Area | Native modules | Mathematical boundary |
| --- | --- | --- |
| Continuous low-degree cohomology | `DegreeOne`, `LowDegreeExact`, `NormalizedCohomology`, `NestedInvariants` | Crossed cocycles modulo principal cocycles compute degree one with locally compact groups and jointly continuous actions; the degree-zero/one connecting sequence uses a continuous, not necessarily equivariant, splitting. |
| Transfer | `Corestriction`, `Composition`, `Mackey` | Open finite-index subgroup transfer and degree-one functoriality, composition and Mackey relations with the hypotheses in each declaration. |
| Degree-one torsion | `Torsion` | Compact topological group, discrete jointly continuous representation over a topologized ring; each continuous `H¹` class has finite additive order. The index is class-dependent. |
| Finite constructions | `FiniteCoinvariants`, `FiniteNegativeDeflation`, `ExceptionalDeflation`, `FiniteDeflationTransitivity` | Finite acting groups, orbit-difference relations, closed quotient under compact Hausdorff coefficients, and finite-level deflation in Tate degrees `-1` and `0` with nested-normal-subgroup transitivity via the pinned finite-group Tate library. No general nonpositive Tate theory for arbitrary topological groups is constructed. |
| Compact exceptional Tate stages | `FiniteTateTopology`, `FiniteCoinvariantDeflation`, `ExceptionalTateDeflationTopology` | Compact Hausdorff additive closed-kernel/quotient models in degrees `-1` and `0`, continuous coinvariant and induced Tate deflation with identity/composition and additive comparison to algebraic Tate deflation; finite residual-kernel hypotheses apply. No ring topology or topology on algebraic Tate groups is asserted. |
| Finite Tate diagrams | `FiniteTateDiagrams`, `NonpositiveTateLimits`, `NonpositiveTateFunctoriality` | Covariant deflation along open normal inclusions of a profinite group, `TopModuleCat` limits and coefficient-morphism functoriality for the homological model of degrees below `-1` and exceptional degrees `-1` and `0`. No identification with completed continuous Tate theory. |
| Compact finite bars | `CompactNegativeTate`, `CompactBarFunctoriality` | Finite-group bar chains with compact Hausdorff additive coefficients and individually continuous action maps; closed-boundary homology, additive comparison with finite Tate degrees `-(n + 2)`, and continuous functoriality for equivariant continuous coefficient maps. |
| Quotients and actions | `ClosedTopologicalCoinvariants`, `QuotientConjugationAction`, `TopologicalQuotientConjugationAction`, `TopologicalModN`, `ContinuousGroupExtension` | Closed versus algebraic coinvariants, quotient conjugation, continuous group extensions, and closed reduction modulo `n`; pointwise continuous actions do not imply jointly continuous actions. |
| Compact groups and limits | `CompactAddCommGroup`, `CompactAddCommGroupLimits`, `CompactFiniteHomology`, `CompactTopModuleLimits` | Compact Hausdorff additive groups, finite products, inverse limits and finite-stage homology constructions; cofiltered limit statements include empty indexing categories where stated. |
| Compact levels | `LevelCompact`, `LevelCompactFunctoriality`, `LevelCompactNorm`, `RestrictedLevelCompact` | Compact level systems, functoriality, relative norms and restricted systems with explicit finite-stage hypotheses. |
| Universe and representation interfaces | `TopModuleCatUlift`, `TopRepUlift`, `GroupExtensionUlift`, `HomogeneousCochainsUlift`, `ContinuousCohomologyUlift` | Universe transport and compatibility for the named continuous cohomology and extension constructions. |

The [`ContinuousGroupCohomology.lean`](ContinuousGroupCohomology.lean) root
publicly imports all 38 listed production leaves. All 38 and the sixteen clients
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
38-leaf/sixteen-client graph or its renewed Tate dependency.

The build environment had a shared **15 GiB** memory limit. Its lifetime cgroup
high-water reading was **14,701,797,376 bytes** after the root build and
**15,215,030,272 bytes** (about **14.2 GiB**) after the client build. These are
shared lifetime readings, **not per-command peak RSS** or a measured minimum
memory requirement. Plan additional headroom above that observed high-water
mark for other processes. CPU allocation and hardware were not recorded in this
baseline, so timings are indicative rather than portable guarantees; fresh setup
also depends on network access and available caches.

### Build targets and clients

`ContinuousGroupCohomology` compiles the public root and its 38 imports;
`CGCExamples` compiles precisely these sixteen native clients, also selected by
the default build:

- [`CompactFoundationNative`](examples/CompactFoundationNative.lean),
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
  [`RestrictedLevelNative`](examples/RestrictedLevelNative.lean), and
  [`NativeCore`](examples/NativeCore.lean).

For an explicit fresh source elaboration of the aggregate-root client:

```sh
lake env lean examples/NativeCore.lean
```

The other fifteen client paths above can likewise be given to `lake env lean`.
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
additional finite Tate comparison diagrams, inverse-limit exactness, or the
broader completed continuous Tate and topology layers. The compact finite-bar
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
levels, not general completed continuous Tate cohomology.

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

# Exotic topology: genuine Lean donors and same-object max-cut

Date: 2026-10-25. Original research and textbook authorship retained.
Companion Agda stacked draft: chboishabba/dashi_agda#1254.
This branch does NOT assert new kernel verification without a local Lean receipt.

## Prior-art audit (source files directly inspected)

| Native existing owner | What it already does | What it does NOT do |
| --- | --- | --- |
| `Synthesis/MillenniumHodgeCP1Quotient.lean` | Mathlib literal complex projectivization, actual quotient and chart overlap | Homology |
| `Synthesis/MillenniumHodgeCP1TopologicalSphere.lean` | Real homeomorphism of CP1 with `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1` | A CW cell decomposition or a homology computation |
| `Synthesis/MillenniumHodgeCP1SingularTransport.lean` | Actual `TopCat` functorial singular-chain and H2 isos along the homeomorphism | Sphere H2=Q |
| `Synthesis/MillenniumHodgeCP1CellularH2.lean` | Rational CP1 finite cellular 0/2-cell H² coefficients, H²=Q | An actual cellular-to-singular comparison |
| `Synthesis/MillenniumHodgeSphereSimplicialBoundaryH2.lean` | SSet.boundary 3, tetrahedral fundamental chain, all 2-cycles are multiples, tetrahedral H₂=Q | Same-object normalized-chain-to-singular-chain identification |
| `Integration/UltrametricCensus.lean` | Actual exact prefix-ultrametric equivalences on existing finite carriers; counterexample against an invalid Monster walk ultrametric | Cantor-space infinite stream topology or ambient 3D wild embedding |
| `Spine/FiniteReindex.lean` | General finite sum reindexing and permutation/Gram invariance | Topological embedding/isotopy |
| `Integration/ObserverQuotient.lean` | Finite trit-to-Bool observation, non-descent and polarity loss | Equal Cantor measures/embedding classification |

**Important:** the linked repository presently lacks a GitHub code search index.
Empty code-search results were NOT evidence these files were missing.

## Mathlib CW ownership: exact pin check

Read directly from `leanprover-community/mathlib4` tag `v4.28.0`,
matching this repository's `lakefile.toml` and `lake-manifest.json`
(Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).

- `Mathlib/Topology/CWComplex/Classical/Basic.lean`:
  real `Topology.CWComplex` / `RelCWComplex` classes on subsets
  with characteristic maps, weak topology, closure finite attachments.
  Authors Floris van Doorn / Hannah Scholz, with Mathlib contributors.
- `Mathlib/Topology/CWComplex/Classical/Finite.lean`:
  `CWComplex.mkFinite`, `CWComplex.mkFiniteType`, finite type and
  dimensionality. **Correction:** `CWComplex.mkFinite_map` is not
  present at this pin (the prior Agda draft claimed it without checking).
- `Mathlib/Topology/CWComplex/Abstract/Basic.lean`:
  categorical `TopCat.CWComplex` and relative CW structures,
  Jiazhen Xia / Elliot Dean Young / Joël Riou credited.
- `Mathlib/Topology/Category/TopCat/Sphere.lean`:
  `TopCat.sphere n = TopCat.diskBoundary (n+1)`, whose carrier is
  `ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1)`.
  This is EXACTLY the same Euclidean sphere used by native CP1 proof,
  differing solely by `ULift` and `TopCat.of`.
- `Mathlib/Topology/Constructions.lean`:
  exact source declarations `continuous_uliftUp` and
  `continuous_uliftDown` checked at v4.28.0.

`Synthesis/ExoticTopologyMathlibCWSource.lean` now consumes
actual `Topology.CWComplex`, with a separate acceptance gate for
the particular CP1 topology. No generic CW implementation duplicated.

## Lean-native new consumers

1. `ExoticTopologyCP1TopCatSphereWeld.lean`: constructs the actual
   `CP1 ≃ₜ ULift UnitSphere2`, hence the literal
   `TopCat.of CP1 ≅ TopCat.sphere 2`; transports the native rational
   singular H2 functor along that SAME object.
2. `ExoticTopologyFiniteSpherePairing.lean`: exact nondegenerate
   finite rational evaluation pairing between the existing CP1 cellular
   H² model and tetrahedral H₂ model. H² cohomology and H₂ homology
   remain two DIFFERENT kinds of invariant; pairings alone do not
   produce the singular comparison.
3. `ExoticTopologyWhitneySimons.lean`: Whitney parametrised equation,
   nonnegative z and excluded negative algebraic axis; exact Simons
   unit-link two-factor radius-squared condition.
   No implicit real-image-surjectivity theorem or GMT minimality.
4. `ExoticTopologyWadaBoundary.lean`: typed genuine point-set
   Wada predicate requiring nonempty, open, connected, pairwise
   disjoint domains with common nonempty `frontier`; proves closure
   and open-domain avoidance consequences. Existence remains unsupplied.

## High-value SOTA donor: Hatcher sphere homology

Repo `Deicyde/hatcher-at`, **Jack McCarthy**,
`Hatcher/Sphere/Homology.lean` now contains
`Hatcher.Sphere.reducedHomology_sphere` with
`Nonempty ((Hatcher.Reduced.homologyFunctor R n).obj
(TopCat.sphere n) ≅ R)` and off-diagonal vanishing.

This is a GENUINE formal sphere result on the same `TopCat.sphere 2`
we now expose. It is not merely a source-defined toy chain complex.
Source authority: Hatcher's *Algebraic Topology*, Corollary 2.14,
and Jack McCarthy's Lean construction.

**Critical compatibility issue:** this repository's `lakefile.toml`
pins Mathlib `v4.28.0`, while its checked-in `lean-toolchain`
reads `leanprover/lean4:v4.35.0-rc3`; the Hatcher repo uses
Lean/Mathlib `v4.34.1`. Do not silently alter those pins to force
one import graph; use a source-identified dual-environment theorem
receipt or deliberately reconciled fork and test exact heads.
The already completed Hatcher result may replace the abstract
sphere-homology proof obligation only after the exact object/chain
comparison is completed. It does not automatically prove the local
tetrahedron-to-singular chain comparison, nor the actual cohomological
cycle-class map.

## New absolute acceptance gates / negative tests

- Actual Wada triple: geometric point-set domains, not C3-labeled cells.
- Actual CW: `Topology.CWComplex C` source data, not Euler numbers.
- Whitney implicit algebraic locus strictly includes parametrised
  real image: a negative-z axis point is algebraic but not in the image.
- Simons cone: its unit-link algebra holds, but minimality still needs
  geometric measure theory.
- CP1 homology: functorial transport and finite pairing do not imply
  the missing tetrahedral normalized-to-singular same-object map.

## Kernel and executable status

- Lean source files are committed in an isolated branch, NOT typechecked.
- Existing Lean main code has declarations whose source was inspected;
  no new claim of a fresh exact-head kernel receipt is made.
- Supporting SymPy/local Python algebra from the companion Agda audit can
  validate finite identities but cannot certify Lean theorem statements.
- Before merging: pin-consistent Lean build, `#print axioms` for the
  new theorems, and import compatibility with the actual current stack.


## Final literal sphere-H₂ acceptance cut

`Synthesis/ExoticTopologyCP1SphereH2Acceptance.lean` uses the
new actual `CP1 ≃ₜ TopCat.sphere 2` bridge and asks for one
source-native, correctly typed datum:

```lean
SourceSphereH2Q :
  Prop :=
  Nonempty (LiteralSphere2RationalH2 ≅ rationalCoefficientObject)
```

From this input the file derives, by the already-proved same-object
singular-H₂ functor isomorphism,

```lean
Nonempty (cp1SingularH2 ≅ rationalCoefficientObject)
```

without postulating that the finite tetrahedral normalized chain complex
is the singular chain complex or silently invoking reduced-to-ordinary
homology. This is a conditional supplier-facing theorem and does
NOT inhabit its `SourceSphereH2Q` prerequisite. It isolates the
shortest correctly typed next external donor rather than creating
another surrogate sphere.

`scripts/exotic_topology_lean_donor_audit.py` was run locally using
SymPy; result PASS. It checks the EXACT tetrahedral boundary matrix has
rank three and kills the chosen fundamental cycle; the corresponding
finite H₂ is one-dimensional, finite rational pairing determinant one,
Whitney polynomial vanishing / negative-real-image discriminator,
Simons unit-link radii, and C3 boundary-incidence Wada negative control.
These are independent algebraic audits, NOT Lean kernel checks.


## Completion after first source cut

`Synthesis/ExoticTopologyWhitneyRealImage.lean` now source-writes
the full point-set algebraic biconditional

```
(∃ u v : ℝ, whitneyParam u v = p)
  ↔ whitneyPolynomial p = 0 ∧ 0 ≤ p.z
```

The constructive reverse witness uses `(u,v)=(y,x/y)` when `y≠0`,
and `(u,v)=(0,sqrt(z))` when `y=0` (where the equation forces
`x=0`). It reuses the original single `whitneyParam` and
`whitneyPolynomial` declarations from `ExoticTopologyWhitneySimons`,
not new duplicate polynomial carriers. **Lean kernel typecheck remains
unverified**. The independent `scripts/exotic_topology_lean_donor_audit.py`
now passes 225 exact rational-grid inverse checks alongside the
tetrahedron, perfect-pairing, Simons and C3/Wada negative controls.

This completes the algebraic real-image model as a source-written proof
attempt, not a claim of a globally immersed regular surface. The canonical
Whitney umbrella has a rank singularity and must not be rebranded a
smooth embedding.

## Current numerical/structural cut

Native Lean draft #86 contains seven source-written Lean modules, one
reproducible independent SymPy exact audit and this source review.
In Agda, companion draft #1254 is stacked on horned sphere #1244
and retains separate geometric limit, wildness, Wada existence,
noncompact-surface and other classification obligations.

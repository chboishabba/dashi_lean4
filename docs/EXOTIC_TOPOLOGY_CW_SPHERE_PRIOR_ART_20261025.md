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


## 2026-10-25 second continuation: literal quotient, Warsaw set, native ends

### Actual pinched-torus point-set realisation

`Synthesis/ExoticTopologyPinchedTorusQuotient.lean` is an
actual Mathlib topological quotient:
- `TopologicalUnitCircle = {z : ℂ // ‖z‖ = 1}`;
- `TopologicalTorus = S¹ × S¹`;
- one meridian `{basepoint} × S¹` is collapsed by a
  `Setoid` built from an explicit `Option`-valued label;
- `PinchedTorus = Quotient pinchedTorusSetoid` carries the
  Mathlib coinduced quotient topology;
- the pinching is supplied as a source-written
  `Continuous` and `IsQuotientMap` proof using EXACT source lemmas
  `continuous_quotient_mk'` and `isQuotientMap_quotient_mk'`
  verified at pinned Mathlib 4.28.0;
- meridian collapse, off-meridian injectivity and separation from
  the pinch point are supplied as source-written theorems.

No homeomorphism to a wedge or homology comparison is inferred
from the quotient definition. The previous Python `(1,1,1)`
cellular-Betti model remains a SEPARATE calculation.

### Actual Warsaw planar set

`Synthesis/ExoticTopologyWarsawCircle.lean` now defines the
topologist's sine graph on `0<x≤1`, takes its literal closure in
`ℝ×ℝ`, and adds the exact polygonal closing arc along y=-2.
It constructs `WarsawCircleSpace` as a topological subtype and
records source-written graph/connector inclusions and endpoint facts.
The independent symbolic x_n=1/(2πn+asin(t)) vertical-limit formula
passed locally. The theorem that the entire vertical segment lies in
the ACTUAL closure, compactness/connectedness and all homotopy
properties remain explicitly OPEN in Lean.

### Infinite-type surface stages

`Synthesis/ExoticTopologySurfaceExhaustions.lean` imports the
ALREADY-OWNED `Integration.Address.Addr n Bool`; it does not invent
a second binary-Cantor finite address geometry. Its typed stage
theorems give:
- Cantor tree: boundary `2^n`, genus 0, Euler `2-2^n`;
- Loch Ness monster: one boundary, genus n, Euler `1-2n`;
- Jacob's ladder: two boundaries, genus 2n, Euler `-4n`;
- graph-spine rank `2g+b-1`;
- correct integer, NOT truncated-natural, Euler arithmetic.

Those numeric invariants don't by themselves furnish Richards'
topological classification. Locally verified stages 0..12.

### Seashell

`Synthesis/ExoticTopologySeashellParametric.lean` consumes the
existing `ExoticTopologyWhitneySimons.Point3` and Mathlib real
sine/cosine to establish the source radial identity and u-periodic
seam. This is a real coordinate object without immersion
or global embedding promotion.

### Independent verification

Extended `scripts/exotic_topology_lean_donor_audit.py`
checks all previously recorded sphere/Whitney/Simons/Wada finite
algebra, plus 39 surface-stage Euler/spine identities, all 4096
Cantor frontier address count at depth 12, 256 finite pinched-torus
relation pairs, real seashell radial and seam formulas, and the
Warsaw vertical-limit identity. These calculations PASSED locally
using Python 3 / SymPy. The checked-in executable is a reproducible
audit, not kernel authority.

### Current exact next cut

**(a)** Kernel typecheck and preflight the Lean 4.35.0-rc3 /
mathlib v4.28.0 lock graph (and Agda imports separately).
**(b)** Upgrade the literal pinched torus to its actual cellular/
singular quotient invariants, rather than asserting a homeomorphism
from numerical homology.
**(c)** Prove Warsaw's vertical segment inclusion and its true
weak-homotopy / non-CW classification.
**(d)** Realise the finite surface pants+handle tower as a genuine
locally finite collared manifold and identify the end/genus data.
**(e)** For Wada and Fox-Artin, pay geometric point-set conditions
rather than symmetry or symbolic address substitutes.
**(f)** Complete the literal sphere H₂ external pin and
reduced/ordinary homology compatibility under one Lean source
graph. Hatcher/McCarthy and Mathlib retain original credit.

None of (b)--(f) is claimed complete by the source-written
tranche. No additional physical wild-embedding or space-propulsion
claim is inferred.


## Source-genealogy / PL surface proof cross-pollination (2026-10-25)

New typed Ibrahim/Pareto/snowball genealogy, reusing
`DASHI.Core.AttributedSourceCore` and the canonical snowball
attribution receipt, rather than cloning an identity ontology:

- https://github.com/chboishabba/dashi_agda/blob/topology-exotic-spaces-prior-art-maxcut-20261025/DASHI/Mathematics/Topology/ExoticSourceGenealogyParetoExact.agda
- https://github.com/chboishabba/dashi_agda/blob/topology-exotic-spaces-prior-art-maxcut-20261025/Docs/topology/ExoticTopologyIbrahimSnowballPareto20261025.md
- https://github.com/chboishabba/dashi_agda/blob/topology-exotic-spaces-prior-art-maxcut-20261025/scripts/exotic_topology_pl_surface_gluings.py

**Source-owner correction from the actual originals:** Richards (1963)
quotes *H. R. Brahana*, *Systems of Circuits on Two-Dimensional
Manifolds* (1921), DOI 10.2307/1968030, as the owner of the
compact bordered-surface classification. He credits *B. Kerékjártó*,
*Vorlesungen über Topologie I* (1923), for an earlier ideal-boundary
classification, describing gaps he corrects; the linked book DOI
10.1007/978-3-642-50825-7 identifies its much later electronic edition,
not a 1923 DOI. Richards 1963 DOI 10.2307/1993768 remains the
primary modern end-classification and existence source.

**Constructive geometrical improvement:** Agda companion #1254
now contains a Python PL mesh builder. It literally triangulates
a cube-boundary sphere with separated triangular holes (annulus/pants),
a periodic triangulated torus with two holes (genus-one collar)
and a disk, and performs boundary-circle gluings via orientation
reversing vertex identifications. It verifies every vertex link
is a connected circle or interval, globally consistent
orientation, boundary loops, connectedness and actual
`V-E+F=2-2g-b`. Through depth 4, it recovers 16 outgoing
Cantor boundaries, Loch genus 4, and Jacob genus 8 with both ends.
The local independently implemented algorithm PASSed all stages
and rejected a two-triangle same-oriented-edge counterexample.
This is much stronger than numerical stage bookkeeping but is
NOT a kernel proof, an infinite direct-limit theorem, or
Richards' end-space application.

Pareto next cut remains the **locally finite collared infinite union**
and decorated end-space homeomorphism, once the native Lean
topological surface construction is implemented. Do not duplicate
the Agda script's combinatorial operations in Lean merely to
re-test their numeric output. The native `Integration.Address`
is still the exact owner for finite prefix labels.

Additional sources retained in the typed atlas: Fox--Artin (1948),
DOI 10.2307/1969408; Yoneyama (1917), J-STAGE source (no DOI
verified); Bombieri--De Giorgi--Giusti (1969),
DOI 10.1007/BF01404309; Mardešić's 1978 shape-theory survey;
Hatcher's book; Jack McCarthy's separate Hatcher-at
`reducedHomology_sphere` Lean implementation. Neither citations
nor QIDs/DDC nor Pareto ranks make a theorem executable.


## Direct primary-source Fox--Artin S₅ witness (2026-10-25)

New `Synthesis/ExoticTopologyFoxArtinS5Witness.lean` uses
**Mathlib's existing permutation equivalence carrier**, rather than
a synthetic group with an assumed relator. The source is the
user-pictured **Fox--Artin Example 1.1\***,
Ann. Math. 49 (1948), 983, original equation (2_n*):
```
a_n a_(n+1)^2 a_(n+2)
  = a_(n+1) a_(n+2) a_(n+1)^(-1) a_n a_(n+1)
```

Fox/Artin's actual cycle images, three-periodic in n, are
`(1 2 3 4 5)`, `(1 2 5 3 4)`, `(1 2 4 5 3)`.
Lean #86 source-writes `Fin 5 ≃ Fin 5` instances with explicit
left/right inverses and a `by decide` proof for the three distinct
residue-class relators; the first generator is non-identity and of
order five. This is a source-level nontrivial presentation model.
A separate independent Python tool
`scripts/exotic_topology_fox_artin_s5.py` locally PASSed the
same exact relations on all integers -301..301. No kernel receipt
for the new Lean module has been obtained.

**Source-aware stop condition:** the primary text explicitly
says Example 1.1* has a **non-simply-connected complement**.
Example 1.2 is a wild arc whose complement IS an open 3-cell.
Example 1.3 has a simply-connected complement that is NOT an
open 3-cell. Therefore the previously-existing global complement
group in the horned-sphere lane is only one of the required
topological discriminators. Geometric Van Kampen/colimit
identification of the actual embedded arc's fundamental group
and the local punctured-neighborhood system are STILL OPEN.
The S5 representation does not prove a wild embedding on its own.

Primary: https://www.maths.gla.ac.uk/~mpowell/fox-artin.pdf ,
https://doi.org/10.2307/1969408 .


## Finite PL ancestor bug closed; exact inverse-limit source (2026-10-25)

Agda #1254 discovered and corrected a previously hidden flaw in the
finite Cantor surface audit: selecting index-zero boundary at each
step can select a newborn circle, leaving a preexisting branch
unsplit, despite perfectly valid finite PL meshes and `b_n=2^n`.
New `scripts/exotic_topology_pl_frontier_lineage.py` transports
actual boundary vertices through the orientation-reversing gluing
vertex quotient and checks each preexisting branch `p` is replaced
exactly by `p0,p1`. The geometry, Euler/link checker and pants
donors are the original implementations; no parallel mesh type
was invented. A genuine four-boundary triangulated counterexample
illustrates why counts fail to determine the end tree.

NEW `Synthesis/ExoticTopologyCantorInverseLimit.lean` directly
uses `Integration.Address.Addr n Bool` to define the projective
tower of all compatible finite binary words. It source-writes
`cantorEndInverseLimitEquiv`, with a two-sided inverse between
coherent stage families and infinite binary streams,
using `Fin.lastCases`, the existing core reverse induction for
finite tuples. This is a substantive exact SYMBOLIC inverse-limit
result, not merely a rebranding of `ℕ→Bool`; every stage must
be coherent under the precise restriction map.

The tower equivalence and the corrected PL branching supply
two necessary inputs for proving a genuine Cantor end-space
homeomorphism. They do NOT yet prove:
- a topological direct-limit collared 2-manifold,
- the Richards nested-unbounded-region end equivalence,
- homeomorphism of the actual ideal-boundary topology with the
  cylinder topology,
- the identification of genus accumulated at each genuine end.

New Lean source and revised Python tests have not been kernel
or exact-head executed in this turn. Do not retroactively call
earlier symbolic and finite receipts validation of the repair.


## 2026-10-25 Richards conditional direct-limit theorem and lineage blocker payment

The companion Agda PR #1254 now has
`Docs/topology/ExoticInfiniteSurfaceEndSpaceConditionalTheorem20261025.md`.
It states the explicit five hypotheses H1–H5 for an **actual
collared nested PL surface exhaustion** and gives the mathematical
proof obligations yielding connected orientable second-countable
boundaryless manifolds, compact cofinal exhaustions, and decorated
Richards end spaces:

- Cantor: compatible (p\mapsto p0,p1) frontier labels, homeomorphic
  ideal boundary `{0,1}^N`, every end planar, genus zero.
- Loch Ness: one outgoing end with genus-one collars arbitrarily far out.
- Jacob: two independent labelled outgoing ends, both with
  genus-one collars arbitrarily far out.

The finite PL builder is corrected to explicitly preserve
**the old boundary vertex embeddings** and exact lineage,
rather than relying on counts alone. Its stronger new tests
are not yet executed at the exact pushed GitHub head.

Native Lean source `ExoticTopologyCantorInverseLimit.lean`
defines a precise compatible tower of **the existing**
`Integration.Address.Addr n Bool` and constructs a two-sided
equivalence to infinite binary streams. This is the genuine
combinatorial inverse-limit half of the end argument. It is
NOT the homeomorphism to the **actual topological space
of ends of the geometric union**, which needs kernel-level
collar/cofinality and end-basis proofs.

The attribution chain remains Brahana 1921 ->
Kerékjártó 1923 -> Richards 1963, retaining separate
original compact theorem, noncompact predecessor and
later complete theorem/realization authorship.


## Cross-PR latest frontier and Cantor clopen obstruction, 2026-10-25

NEW `Synthesis/ExoticTopologyCantorClopenMeasureNoGo.lean`
reuses `Integration.Address` and the same branch's
`ExoticTopologyCantorInverseLimit` for source identity, and
proves at SOURCE LEVEL the all-depth arithmetic lemma
`3*k != 2^n` by Mathlib's existing
`Nat.Prime.dvd_of_dvd_pow`. A finite clopen subset of fair-bit
Cantor space has dyadic measure, whereas a one-symbol cylinder
of uniform ternary Cantor measure has mass 1/3. By compactness,
a measure-preserving **homeomorphism** is impossible between
the two SPECIFIED measured spaces, even though a topological
homeomorphism exists via prefix-free code. The full topological
clopen/compactness argument is mathematical prose, not a
complete Lean theorem connecting to product measures.

Sibling Agda #1254 inspected relevant NEW work:
- #1244 already owns three-arm open cover / van Kampen conditional
  assembly, not a fully realised Fox--Artin embedding;
- #1239 already owns the source-first B3->SL2Z matrix image and
  framing-loss negative controls; a finite regression consumer
  now keeps S3 endpoints, SL2Z representation, actual B3, and
  ribbon framing distinct;
- #1259 reuses the generic QueryIndexedProjectionAdequacyExact;
  Agda #1254 now instantiates BOTH an adequate sector-query
  and inadequate linked-marker query on the same horn-address
  projection, and imports the canonical all-rechart no-go.

The original Artin 1925/1947 papers and implementing PRs
retain separate source roles; source 1925 DOI
10.1007/BF02950718, source 1947 DOI 10.2307/1969218.
No Lean kernel checking or new Wada/wildness/space-end
homeomorphism is claimed by this work.


## Latest external and repository prior art / October 25 evening

Agda #1254 source first re-audited its advancing parent #1244,
braid #1239 and recent Animalexic #1259. The new Agda source
directly inherits the exact parent horned cover, central
`pi1` reduction, and 867-point pierced-shell stereography after
a non-destructive merge `f1b1c097767bf085535e48795e49b5e515792c0e`.
No corresponding Fox--Artin arc complement theorem follows
from this Hatcher/Alexander wild solid without a same-object map.

New Lean module
`Synthesis/ExoticTopologyCantorClopenMeasureNoGo.lean`
source-writes the **ALL-DEPTH** theorem
`3 * k ≠ 2 ^ n` for natural k,n by the existing
Mathlib `Nat.Prime.dvd_of_dvd_pow` theorem. The topological
paper corollary is that fair-bit Cantor product measure and
uniform ternary Cantor product measure cannot be related
by a measure-preserving homeomorphism: a one-digit
ternary clopen cylinder has mass 1/3, while any binary
clopen set (finite union of same-depth cylinder sets)
has dyadic mass. The topological/measure
homeomorphism theorem has NOT been kernel-verified.

New `.github/workflows/exotic-topology-lean-focused.yml`
follows source-pinned narrow Hatcher-style kernel ingress,
using `lake build` module targets (with import closures)
rather than standalone `lake env lean` on modules
whose dependencies may have no compiled `.olean`.
It retains the actual repo toolchain/Mathlib lock to
expose any mismatch rather than silently upgrading
a dependency and attributing the result to the wrong
source. GitHub workflow existence is not an execution
receipt; at last observed head no successful new Lean
kernel run was available.

Important reuse: `DASHI.Core.QueryIndexedProjectionAdequacyExact`
already factors through the general
`IntersectionalNonFactorability` theorem, as used by
latest Animalexic #1259. Agda #1254 now imports both to
show a **single horn-address projection** can be
adequate for the source sector query and inadequate
for an independent marked linking query. No
post-recharting of that address can repair the latter.
Original Blackwell and Crenshaw source contributions
are conceptual; this is repository-local mathematics,
not a theorem by those authors on wild knots.

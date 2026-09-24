import Cuisine.SensoryCore
import Cuisine.Surfaces
import Cuisine.Lineage
import Cuisine.ProcessRoute
import Cuisine.DataFlow
import Cuisine.Publication
import Cuisine.Provenance
import Cuisine.LedgerPattern
import Cuisine.SourceAtlas
import Cuisine.CarryingCapacity
import Cuisine.HyperfabricGuard
import Cuisine.ToneSeparation
import Cuisine.Witnesses
import Cuisine.UmamiTransport
import Cuisine.NineSheet
import Cuisine.SafetyFabric
import Cuisine.SeveritySeam
import Cuisine.MdlPrimeModel
import Cuisine.SpiralCarrier
import Cuisine.SurfaceInterpretation
import Cuisine.KnotWeave
import Cuisine.NonaryAction
import Cuisine.SweetgrassSpine
import Cuisine.ToeBridge
import Cuisine.TransportKernel
import Cuisine.CodecTransport
import Cuisine.SupervoxelClopen
import Cuisine.LoomBridge
import Cuisine.FourLevelLedger
import Cuisine.EndToEnd
import Cuisine.AxiomAudit

/-!
# The cuisine lane

Root module of the `Cuisine` library: a Lean formalisation of the proof-relevant
content of the Agda cuisine corpus at `Agda/DASHI/Culture/Cuisine/`, together
with the theorems that corpus states informally, checks at single points, or
leaves open.

Layers, in dependency order:

* `Cuisine.SensoryCore` — the stimulus/reading carriers, the umami interaction
  law with its closed form and non-additivity, and the observer- and
  process-dependence obstructions;
* `Cuisine.Surfaces` — the surface non-collapse ledger, its soundness, its
  directedness and its incompleteness;
* `Cuisine.Lineage` — the sauce derivation graph as an acyclic partial order,
  and the carbonara identity envelope as a partition;
* `Cuisine.ProcessRoute` — the phantom-index defect in the supplied mole route
  relation, and a repaired route family for which order-sensitivity is a
  theorem;
* `Cuisine.DataFlow` — the promotion pipeline and its fail-closed property;
* `Cuisine.Publication` — the publication decision map, the hole in the supplied
  impact assessment, and the repaired assessment;
* `Cuisine.Provenance` — channel-dependent provenance routing;
* `Cuisine.LedgerPattern` — what the corpus-wide `Bool`-with-`= false` field
  pattern does and does not prove;
* `Cuisine.CarryingCapacity` — the free-`standing` hole in the supplied
  carrying-capacity record, its total repair, and a fail-closed variant for
  partial measurement;
* `Cuisine.SourceAtlas` — the twenty-two-source receipt, with distinctness;
* `Cuisine.HyperfabricGuard` — the lane's one cross-domain definitional import,
  audited: a guard that really does reject every promotion route, a vocabulary
  separated only by naming, a contentless cuisine-side facet, and a cardinality
  obstruction to reading the triad surfaces as ternary;
* `Cuisine.ToneSeparation` — the honest bridge to `Synthesis.ToneCore`: the
  carriers are abstractly isomorphic, the structures are not;
* `Cuisine.Witnesses` — the finite witnesses and the Agda regression suite;
* `Cuisine.UmamiTransport` — the positive cross-domain bridge: the cuisine
  umami combination law as a monoid, and its structure-preserving, surjective
  transport onto the hyperfabric of ternary sections over the Monster prime
  base, equivariant for the dialectical action;
* `Cuisine.NineSheet` — the `3 · 5 = 15` shape of that base, the `3^9 = 19683`
  depth-nine sheet count, and the affine identities relating it to the supplied
  moonshine numerals;
* `Cuisine.SafetyFabric` — safety fields over the Monster base as hyperfabric
  sections, fail-closed aggregation as a mask-semilattice homomorphism, and the
  supplied Monster ultrametric and contractive projection pulled back to
  cuisine safety data;
* `Cuisine.SeveritySeam` — the SensibLaw/`Base369` hexadic ladder mirrored, the
  rotation-equivariant surjection of the `369` carrier onto cuisine safety
  verdicts, and the general theorem that a fail-closed severity is constant
  along any rotation, so every such ladder has a seam;
* `Cuisine.MdlPrimeModel` — the `Agda/MDL` two-part-code interface instantiated
  on the transport: the MDL-optimal subset of supersingular primes for a
  transported cuisine intensity is exactly its Monster mask, uniquely;
* `Cuisine.SpiralCarrier` — a referent for the guard's `spiral` surface: the
  four-element Klüver form-constant carrier, with its geometry-hint family shown
  to be a singleton over each form, and the honest limitation that four elements
  do not inject into three;
* `Cuisine.SurfaceInterpretation` — the guard's eight semantic surface names
  interpreted in the repository's implementation carriers, with the
  cardinalities proved; the table is now total and injective, and the one
  residual ambiguity (`stage` and `spiral` are both four-element carriers) is
  recorded as such;
* `Cuisine.KnotWeave` — the cuisine record's second typed cross-domain
  dependency audited: a contentless admissibility gate, but a genuinely ternary
  knot/weave/braid carrier, canonically the balanced-ternary digit, whose
  cycle is the tone rotation and, over the Monster prime base, cuisine-side
  seasoning;
* `Cuisine.NonaryAction` — the `3 · 5` grid gives the Monster prime base its own
  order-three rotation; it commutes with the `369` rotation of the fibre, so the
  hyperfabric carries a faithful nonary action, the base-invariant sections
  number `3 ^ 5 = 243`, the fibre rotation fixes nothing, and — honestly — the
  base rotation moves the moonshine trivector mask — while the three-cycle of
  the trivector primes themselves is a moonshine-preserving base symmetry with
  `3 ^ 13` invariant sections;
* `Cuisine.SweetgrassSpine` — the Sweetgrass carrier-spine vocabulary audited
  (unused anchors, an unused Hecke-operator role, a projection that collapses
  thirty-nine roles onto five targets) and *realised*: a typed table sending
  thirteen of its thirty-five motifs to the implementation types they name,
  with the structural theorems tying those types to one another and to the
  cuisine transport;
* `Cuisine.ToeBridge` — all of the above packaged as the `CuisineToeBridge`
  interface with its canonical inhabitant;
* `Cuisine.TransportKernel` — the kernel of the umami transport, exactly: a
  blend has neutral hyperfabric shadow iff its successor is a cube times a
  factor divisible by no supersingular prime, and two blends agree iff their
  fifteen supersingular exponents agree modulo three;
* `Cuisine.CodecTransport` — the cuisine monoid in the balanced-ternary codec
  coordinates of `TriadicKernelAlgebra`: combining blends is the *affine* codec
  operation, self-seasoning is the codec inversion translated by one (and never
  literally the codec inversion), and the self-seasoning quotient of the
  hyperfabric has the supplied codec orbit count `7174454`;
* `Cuisine.SupervoxelClopen` — the supervoxel interface of
  `DASHI.Foundations.ConstraintClopenRefinement` mirrored, with a checked
  ternary clopen-ball instance, non-atomicity proved rather than declared by a
  `Bool` field, the cuisine transport identified with the depth-15 ball
  projection, and the refinement order on cuisine neutrality constraints shown
  to be the Monster mask lattice order;
* `Cuisine.LoomBridge` — the dialectic-loom relation algebra: bucket refines
  root, the loom and the cuisine publication lane are two instances of the
  supervoxel refinement interface, neither coarse classifier is atomic, and the
  nine relation types provably do not carry the nonary rotation;
* `Cuisine.FourLevelLedger` — the typed four-level map: which lanes are linked
  to cuisine by vocabulary only, by a stored record dependency, by a shared
  implementation type, and by a proved transport, with the witness for every
  entry;
* `Cuisine.EndToEnd` — the `CuisineSpine` interface, its canonical inhabitant,
  and the composite theorem `cuisine_end_to_end`;
* `Cuisine.AxiomAudit` — prints the axiom dependencies of the headline results.

See `CUISINE_DEPENDENCY_MAP.md` for the provenance map, the classification of
the Agda material, and the list of remaining proof obligations.
-/

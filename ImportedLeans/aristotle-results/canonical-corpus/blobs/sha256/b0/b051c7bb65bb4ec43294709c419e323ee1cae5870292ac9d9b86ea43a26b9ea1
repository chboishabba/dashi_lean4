import Synthesis.ToneCore
import Synthesis.DialecticTone
import Synthesis.RelationSeam
import Synthesis.MonsterFibre
import Synthesis.WalkGeometry
import Synthesis.MoonshineBase
import Synthesis.WalkArithmetic
import Synthesis.Vec15Fibre
import Synthesis.StatisticsFibre
import Synthesis.InferenceFibre
import Synthesis.PhysicsInterfaces
import Synthesis.SpinCoverBridge
import Synthesis.CircleCover
import Synthesis.ExponentFibre
import Synthesis.MonsterOrder
import Synthesis.Hyperfabric
import Synthesis.CodecBridge
import Synthesis.EndToEnd
import Synthesis.AxiomAudit

/-!
# Cross-domain synthesis spine

Root module of the `Synthesis` library: a minimal, fully proved proof spine over
the cross-domain material in this repository.

Layers, in dependency order:

* `Synthesis.ToneCore` — the shared ternary tone primitive (`Trit ≃ TriTruth ≃ ℤ/3`)
  and the half-trit fibre with its `Fin 5` index;
* `Synthesis.DialecticTone` — dialectical carriers over the tone: the sixfold
  descent bridge, the fourfold impossibility, and the tetralemma route divergence;
* `Synthesis.RelationSeam` — the Loom relation classifiers as a strict
  refinement (bucket over root), the typed-relation record as a bare fibre over
  the relation type with promotion provably unconstrained, and the seam of the
  fourfold tone: unavoidable, minimal at one stage, and empty over the sixfold
  carrier;
* `Synthesis.MonsterFibre` — the 15-element supersingular prime base, the
  identification of the three supplied mask carriers, and the transported
  ultrametric geometry with its contractive projection;
* `Synthesis.WalkGeometry` — the walk state carrier, the proof that the two
  supplied mask distances are complementary, and the fact that the walk stays
  inside the mask fibre;
* `Synthesis.MoonshineBase` — mask products over the prime base, and the supplied
  moonshine numerals as values of that arithmetic;
* `Synthesis.WalkArithmetic` — an arithmetic reading of the walk's uninterpreted
  admissibility lens, and the proof that under it the walk is non-expanding
  towards the collapse mask;
* `Synthesis.Vec15Fibre` — the flat 15-slot record carriers (`Vec15`, `Sig15`)
  identified with the same fibre over the prime base;
* `Synthesis.StatisticsFibre` — the order/selection layer on the 15-lane carrier:
  its threshold masks are Monster masks and its threshold family is a monotone
  chain in the mask geometry;
* `Synthesis.InferenceFibre` — the descriptive, inference and robust layers on
  the same 15-lane carrier: the non-zero count is the support mask's cardinality,
  the decision surface is a mask detector, and the robust fences are Monster masks;
* `Synthesis.PhysicsInterfaces` — how much the physics-facing interface records
  actually constrain: the gauge and spin records are shown to carry no such
  content, while the conformance predicate is exactly mask equality in the
  Monster mask geometry;
* `Synthesis.SpinCoverBridge` — the finite quaternion cover `Q8 → V4` is a genuine
  two-to-one cover and instantiates the spin interface with real content, while
  the continuous Spin(3,1) record is shown to be inhabited with all of its
  propositional obligations set to `True`;
* `Synthesis.CircleCover` — a genuine *continuous* double cover: the squaring map
  of the circle group is a continuous two-to-one homomorphism of an infinite
  group, so the spin interface is satisfiable outside finite models as well
  (the circle is not `Spin(3,1)`, and no Lorentz statement is claimed);
* `Synthesis.ExponentFibre` — exponent vectors over the prime base: the exponent
  order refines the mask order, and the "observer residue" `+1 ≡ 1` holds modulo
  every prime a mask keeps, generalising the supplied numeral checks;
* `Synthesis.MonsterOrder` — the arithmetic half of the Monster-order obligation:
  the literature's order numeral has exactly the fifteen base primes as prime
  factors, and its radical is the full mask product (no group is constructed);
* `Synthesis.Hyperfabric` — sections of the ternary fibre over the Monster base,
  their `(ℤ/3)^15` algebra, and the dialectical action on them;
* `Synthesis.CodecBridge` — the identification of the hyperfabric with the
  depth-15 balanced-ternary codec kernel of `TriadicKernelAlgebra`;
* `Synthesis.EndToEnd` — the `CrossDomainSpine` interface, its canonical
  inhabitant, and the composite theorem `spine_end_to_end`;
* `Synthesis.AxiomAudit` — prints the axiom dependencies of the headline results.

See `DEPENDENCY_MAP.md` for the provenance map and the list of remaining proof
obligations.
-/

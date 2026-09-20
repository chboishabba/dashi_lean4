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
import Synthesis.ContractRepair
import Synthesis.CircleCover
import Synthesis.ExponentFibre
import Synthesis.MonsterOrder
import Synthesis.MonsterCharacterDetermination
import Synthesis.MonsterCharacterMultiplicityRegression
import Synthesis.RiemannFarShellQuarticCutoff
import Synthesis.RiemannFarShellQuarticCutoffRegression
import Synthesis.RiemannFarShellSignedWindowQuarticIncompatibility
import Synthesis.RiemannNormalizedCenteredOffOscillatoryDecay
import Synthesis.RiemannNormalizedCenteredOffAtomicMeasure
import Synthesis.RiemannNormalizedCenteredProfileSpectralGap
import Synthesis.RiemannNormalizedCenteredOffHorizontalSplit
import Synthesis.RiemannNormalizedZeroCountingStieltjes
import Synthesis.RiemannNormalizedHorizontalCorrectionBound
import Synthesis.RiemannNormalizedCountingAbelCompiler
import Synthesis.RiemannNormalizedRvMMainRemainderCompiler
import Synthesis.RiemannNormalizedRvMZeroModeFourier
import Synthesis.RiemannNormalizedRvMConstantDensityCancellation
import Synthesis.RiemannRvMMuGammaEvenConeWeld
import Synthesis.RiemannRvMCenteredResidual
import Synthesis.RiemannRvMClusterDeletionFirewall
import Synthesis.RiemannCenteredClusterPoleReduction
import Synthesis.RiemannCanonicalCenteredClusterPoleReduction
import Synthesis.RiemannSelectedRadiusClusterReduction
import Synthesis.RiemannHighProjectiveFrontier
import Synthesis.RiemannHighSchurFrontier
import Synthesis.RiemannShortWindowSchurCompiler
import Synthesis.RiemannHighSchurMinCut
import Synthesis.RiemannHighDeterministicSchurNoGo
import Synthesis.RiemannHighOneZeroSchurCutset
import Synthesis.RiemannSmoothShortWindowSchurLift
import Synthesis.RiemannSmoothNormalizedWindow
import Synthesis.RiemannSmoothNarrowWindowDomination
import Synthesis.RiemannConstructedSmoothShortWindowSchur
import Synthesis.RiemannCorrectedHighSchurFrontier
import Synthesis.RiemannReflectionPartnerSchurNoGo
import Synthesis.RiemannReflectionPairClusterSignal
import Synthesis.RiemannReflectionDoubledProjectiveGate
import Synthesis.RiemannReflectionPairSignedResidualCutset
import Synthesis.RiemannSmoothWindowLeadingSignal
import Synthesis.RiemannCanonicalLeadingSignalFloor
import Synthesis.RiemannCanonicalGateData
import Synthesis.RiemannArbitraryRadiusTargetRemainder
import Synthesis.RiemannCanonicalReflectionCoefficientGate
import Synthesis.RiemannSupportScaledTargetRemainder
import Synthesis.RiemannActualHighAnalyticMinCut
import Synthesis.RiemannFarShellDisplacementAdaptiveCutoff
import Synthesis.RiemannAdaptiveCutoffCrossingCompatibility
import Synthesis.RiemannAdaptiveCutoffNearSignNoGo
import Synthesis.RiemannRvMMuGammaSameObject
import Synthesis.RiemannZeta23RvMProducerBridge
import Synthesis.RiemannZeta23RvMIntervalDiscrepancy
import Synthesis.RiemannZeta23RvMIntervalDiscrepancyBound
import Synthesis.RiemannZeta23RvMTwoSidedDiscrepancy
import Synthesis.RiemannNormalizedRvMIntervalAttachment
import Synthesis.RiemannZeta23RvMArbitraryWindowDiscrepancy
import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy
import Synthesis.RiemannNormalizedRvMRightDiscrepancy
import Synthesis.RiemannNormalizedRvMLeftDiscrepancy
import Synthesis.RiemannNormalizedBaseTransformVariation
import Synthesis.RiemannNormalizedRvMAbelResidualBound
import Synthesis.RiemannNormalizedRvMFourierCosineWeld
import Synthesis.RiemannNormalizedCenteredProfileSchwartz
import Synthesis.RiemannNormalizedRvMSmoothMainDecomposition
import Synthesis.RiemannNormalizedRvMCumulativeDiscrepancyCompiler
import Synthesis.RiemannNormalizedBaseTransformDecay
import Synthesis.RiemannNormalizedRvMPhysicalDomainCompiler
import Synthesis.RiemannNormalizedRvMMissingTailBound
import Synthesis.RiemannNormalizedCanonicalFixedProfile
import Synthesis.RiemannGammaCanonicalRatioGap
import Synthesis.RiemannGammaIntegratedRatioGap
import Synthesis.RiemannGammaMatchedQuantitativeGain
import Synthesis.RiemannGammaConeAbsoluteMargin
import Synthesis.RiemannGammaEndpointGapAbsoluteScale
import Synthesis.RiemannGammaInnerRatioAbsoluteScale
import Synthesis.RiemannGammaInnerPoleAbsoluteScale
import Synthesis.RiemannGammaCanonicalIntegratedDeficit
import Synthesis.RiemannQuantitativeGammaDeficit
import Synthesis.RiemannGammaCenteredKernelCompactBridge
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
* `Synthesis.ContractRepair` — the repairs of the three vacuous physics
  contracts: an admissible witness for the gauge claim, the fibre-count property
  for the spin cover, and a separating inner product for the unitary record.
  Each repair refutes the corresponding countermodel and is itself inhabited;
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

import Synthesis.RiemannNormalizedCenteredOffShell

import Synthesis.RiemannProjectiveCenteredGaugeBridge

import Synthesis.RiemannNormalizedCenteredOffTwoRadius

import Synthesis.RiemannNormalizedOffRadiusZeroAtomicMeasure
import Synthesis.RiemannNormalizedProjectiveOffAtomicMeasure

import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment

import Synthesis.RiemannNormalizedProjectiveOffHorizontalSplit
import Synthesis.RiemannNormalizedProjectiveBaseProfile
import Synthesis.RiemannNormalizedProjectiveRvMConsumer
import Synthesis.RiemannNormalizedProjectiveHorizontalQuadraticFactor

import Synthesis.RiemannProjectiveRvMMuGammaSameObject

import Synthesis.RiemannNormalizedProjectiveRvMMissingTailBound

import Synthesis.RiemannProjectiveRvMMuNamedGammaDefect
import Synthesis.RiemannProjectiveRvMCenteredResidualCutset

import Synthesis.RiemannNormalizedProjectiveBaseZeroAtSameOrd
import Synthesis.RiemannNormalizedProjectiveBaseTransformVariation
import Synthesis.RiemannNormalizedProjectiveRvMAbelResidualBound

import Synthesis.RiemannZetaMuExactAbel

import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivative

import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivativeRegularity

import Synthesis.RiemannProjectiveZetaMuContinuousAbel

import Synthesis.RiemannNormalizedProjectiveProfileScaling

import Synthesis.RiemannCanonicalDoubledRadiusPoleSign

import Synthesis.RiemannProjectiveZetaMuExplicitScaling

import Synthesis.RiemannCanonicalNearLineAbsoluteBudgetNoGo

import Synthesis.RiemannProjectiveCompletedSmoothResidual

import Synthesis.RiemannProjectiveFullCompletedCancellation

import Synthesis.RiemannNormalizedProjectiveFullCarrier
import Synthesis.RiemannNormalizedProjectiveSameOrdinateCollapse

import Synthesis.RiemannProjectiveCompletedResidualCircularityFirewall
import Synthesis.RiemannNormalizedProjectiveHorizontalSameOrdSign
import Synthesis.RiemannNormalizedProjectiveHorizontalOscillation
import Synthesis.RiemannNormalizedProjectiveHorizontalFarDecay
import Synthesis.RiemannNormalizedProjectiveHorizontalActualStrip

import Synthesis.RiemannCanonicalCompletedResidualMinCut
import Synthesis.RiemannProjectiveSyntheticHeightSign
import Synthesis.RiemannNormalizedProjectiveHorizontalUniformSign
import Synthesis.RiemannNormalizedProjectiveHorizontalSourceSign
import Synthesis.RiemannNormalizedProjectiveHorizontalSignedNearFar
import Synthesis.RiemannNormalizedProjectiveHorizontalFarSummability

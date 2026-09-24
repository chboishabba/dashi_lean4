import AgdaMirror.Moonshine
import AgdaMirror.MoonshineEarn
import AgdaMirror.JFixedPoint
import AgdaMirror.CRTPeriod
import AgdaMirror.CRTJFixedPointBridge
import AgdaMirror.MonsterOntos
import AgdaMirror.UFTC_Lattice
import AgdaMirror.TenfoldBridges
import AgdaMirror.Base369
import AgdaMirror.Overflow
import AgdaMirror.LogicTlurey
import AgdaMirror.SWAR
import AgdaMirror.Ultrametric
import AgdaMirror.Contraction
import AgdaMirror.FixedPoint
import AgdaMirror.Scaffolding
import AgdaMirror.MonsterWalk
import AgdaMirror.LoomRelationAlgebra
import AgdaMirror.DASHIValuation
import AgdaMirror.DASHIAlgebra
import AgdaMirror.StageQuotient
import AgdaMirror.TritBridge
import AgdaMirror.HalfTrit
import AgdaMirror.TetralemmaBridge
import AgdaMirror.CoprimeLayer
import AgdaMirror.DeltaGrowth
import AgdaMirror.OperatorTypes
import AgdaMirror.ProjectionVsInvertible
import AgdaMirror.UnitaryVsCollapse
import AgdaMirror.MonsterProjection15
import AgdaMirror.ValuationLemmas
import AgdaMirror.ProjectionOrthogonality
import AgdaMirror.DimensionFixedPoint
import AgdaMirror.KernelMonoid
import AgdaMirror.OperatorMonoidClosed
import AgdaMirror.LensKernel
import AgdaMirror.EnergyMetric
import AgdaMirror.RealTernaryCarrier
import AgdaMirror.PhysicsSignature
import AgdaMirror.GaugeGroupContract
import AgdaMirror.QuantumInterface
import AgdaMirror.QuantumMeasurement
import AgdaMirror.CliffordUniversalProperty
import AgdaMirror.QuantumUnitary
import AgdaMirror.SpinEmergence
import AgdaMirror.JoinSurface
import AgdaMirror.VpTrue
import AgdaMirror.UVFiniteness
import AgdaMirror.CCRFromProjection
import AgdaMirror.ConstraintClosure
import AgdaMirror.DashiMarkov
import AgdaMirror.AlgebraCCR
import AgdaMirror.NoGlobalAttractor
import AgdaMirror.SignatureDerivation
import AgdaMirror.PhysicsConformance
import AgdaMirror.QuotientSetoidSurface
import AgdaMirror.AuthorityBoundary
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Order
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport
import AgdaMirror.ActiveWallStructure
import AgdaMirror.WeightedPressure
import AgdaMirror.MaxPressure
import AgdaMirror.DeltaRarity
import AgdaMirror.ActiveWallBounds
import AgdaMirror.NormalizeAdd
import AgdaMirror.CancellationPressure
import AgdaMirror.AnomalyContracts
import AgdaMirror.HalfTritIndexed
import AgdaMirror.Vec15Inference
import AgdaMirror.Vec15Robust
import AgdaMirror.NormalizeAddNonexpansive
import AgdaMirror.NormalizeAddSumPreservation
import AgdaMirror.TrackedCoprimeTable
import AgdaMirror.ArithmeticCoprimeLayer
import AgdaMirror.ArithmeticDeltaGrowth
import AgdaMirror.VpAddUnequal
import AgdaMirror.DeltaInteraction
import AgdaMirror.KPrimeInteraction
import AgdaMirror.GlobalPressure
import AgdaMirror.CancellationPressureFromCanonical
import AgdaMirror.CancellationPressureRefinement
import AgdaMirror.PrimeIndexedPressure
import AgdaMirror.Q
import AgdaMirror.MoonshineBridge
import AgdaMirror.DimensionFixedPointInstance
import AgdaMirror.TreeCCR
import AgdaMirror.SpinFromEvenClifford
import AgdaMirror.UniversalOperatorBasis
import AgdaMirror.TypedResidualBasisDecomposition
import AgdaMirror.ConstraintAlgebraClosure
import AgdaMirror.MonsterGroups
import AgdaMirror.MonsterVectors
import AgdaMirror.Core
import AgdaMirror.Algebra
import AgdaMirror.Analysis
import AgdaMirror.Physics.YangMills

/-!
# `AgdaMirror`: Lean transcriptions of the non-NS/YM root Agda modules

This library surveys the repository's root-level Agda modules (outside the
Yang–Mills / Navier–Stokes "closure" stack, which lives in `ClayClosure`),
classifies each as *genuine provable content* or *structural scaffolding*, and
provides faithful Lean mirrors:

* **Genuine, fully proved** (no `sorry`, no axioms beyond the kernel's
  `propext, Classical.choice, Quot.sound`):
  `Moonshine`, `MoonshineEarn`, `JFixedPoint`, `CRTPeriod`,
  `CRTJFixedPointBridge`, `MonsterOntos`, `UFTC_Lattice`, `TenfoldBridges`,
  `Base369`, `Overflow`, `LogicTlurey`, `SWAR` (genuine *conditional* refinement lemma).

* **Scaffolding, faithfully transcribed** with honesty boundaries preserved
  (Agda `postulate`s become explicit hypotheses / structure fields, never
  Lean `axiom`s): `Ultrametric`, `Contraction`, `FixedPoint`
  (which also *proves* fixed-point uniqueness), and `Scaffolding`
  (abstract entropy systems, restoration, completion law — with the genuinely
  provable 3-adic, `ℤ/6`-regularity, and no-infinite-descent facts proved).
-/

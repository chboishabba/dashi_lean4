# Mirror provenance census (Agda → Lean)

`Lean/AgdaMirror/*` is a layer of **hand-written** Lean transcriptions of named
Agda modules.  Every claim in the integration spine that is phrased as "the Agda
states X" ultimately rests on that layer, and until now nothing checked the
correspondence at all: the Lean build proves the Lean side coherent, not that a
mirror faithfully states its Agda original.  This document is the first
mechanical audit of that layer.

`scripts/mirror_provenance.py` reads each mirror's header for the Agda file it
claims to mirror, locates that file in the `Agda` tree, extracts the top-level
declaration names on both sides, and matches them modulo case, hyphens, dots and
underscores (`tri-low` ↔ `triLow`, `dMask` ↔ `dMask`).  Re-run with

```
python3 scripts/mirror_provenance.py --markdown
```

**What this establishes.**  Traceability: for a matched name there is a
declaration of that name in the cited Agda file, and for an unmatched one there
is not.  **What it does not establish.**  Faithfulness: a name match says
nothing about whether the Lean statement is the Agda statement.  Nor is a
mismatch automatically a defect — many mirrors are deliberately partial, and
several use different names for the same content.  The value of the census is
that the mirror layer is now enumerable and its gaps are visible rather than
implicit.

## Findings

* 123 (mirror, claimed source) pairs examined, from 101 mirror files.
* 116 pairs resolve to an Agda file that exists in this tree.
* **1 dangling citation**: `Lean/AgdaMirror/GodelLattice.lean` cites
  `Ontology/GodelLattice.agda`, which is not present in this cutset.
* **6 mirrors declare no source** in their header: `Algebra.lean`,
  `Analysis.lean`, `Core.lean` (aggregates, so this is expected),
  `DASHIAlgebra.lean`, `MonsterWalk.lean`, `MoonshineEarn.lean` (not
  aggregates — these three are the ones whose provenance is genuinely
  unrecorded).
* Across the resolved pairs, 1 012 Agda top-level declarations are in scope and
  668 (66.0 %) have a name-level correspondent in the mirror.  The remaining
  third are Agda declarations that the mirror does not carry a same-named
  counterpart for; per-module detail is in the table below.

Two consequences for the global map.  First, any registry row whose evidence
comes from a *mirrored* Agda statement should be read as depending on this layer;
rows whose evidence is a Lean theorem about Lean definitions (the great majority
of level-iii/iv rows) do not.  Second, the honest upper bound on this audit is
name-level: a machine-checked faithfulness statement would require an Agda
toolchain and a statement-level comparison, neither of which exists here.

## Per-module table

| Lean mirror | claimed Agda source | Agda decls | name-matched | unmatched |
| --- | --- | ---: | ---: | --- |
| `Lean/AgdaMirror/ActiveWallBounds.lean` | `Agda/DASHI/Arithmetic/ActiveWallBounds.agda` | 50 | 4 | `maxNat-left-≤`, `maxNat-right-≤`, `delta2≤maxPressure`, `tail59`, `tail47`, `tail41`, … (+40) |
| `Lean/AgdaMirror/ActiveWallStructure.lean` | `Agda/DASHI/Arithmetic/ActiveWallStructure.agda` | 12 | 6 | `activeWallMask15`, `supportMask15`, `activeWallMaskAt≤supportMaskAt`, `activeWallCount≤supportPrimeCount`, `ActiveWallStructure`, `activeWallStructure` |
| `Lean/AgdaMirror/Algebra/ConstructiveClifford.lean` | `Agda/DASHI/Algebra/ConstructiveClifford.agda` | 25 | 24 | `_≈Cl_` |
| `Lean/AgdaMirror/Algebra/ContinuousSpin31LorentzCover.lean` | `Agda/DASHI/Algebra/ContinuousSpin31LorentzCover.agda` | 5 | 5 | — |
| `Lean/AgdaMirror/Algebra/FiniteQuaternionStrictCover.lean` | `Agda/DASHI/Algebra/FiniteQuaternionStrictCover.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/Algebra/FiniteQuaternionStrictCover.lean` | `Agda/DASHI/Algebra/FiniteQuaternionDoubleCover.agda` | 34 | 23 | `RotationPreimage`, `rhoSurjective`, `plusMinusDistinct`, `plusMinusIDistinct`, `plusMinusJDistinct`, `plusMinusKDistinct`, … (+5) |
| `Lean/AgdaMirror/Algebra.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/AlgebraCCR.lean` | `Agda/DASHI/Algebra/CCR.agda` | 5 | 3 | `_∘_`, `CCRFramework` |
| `Lean/AgdaMirror/Analysis/CanonicalRationalMetric.lean` | `Agda/DASHI/Analysis/CanonicalRationalMetric.agda` | 29 | 29 | — |
| `Lean/AgdaMirror/Analysis/ConcreteComplex.lean` | `Agda/DASHI/Analysis/ConcreteComplex.agda` | 13 | 10 | `_+C_`, `_-C_`, `_*C_` |
| `Lean/AgdaMirror/Analysis/ConstructiveIntermediateValue.lean` | `Agda/DASHI/Analysis/ConstructiveIntermediateValue.agda` | 7 | 7 | — |
| `Lean/AgdaMirror/Analysis/FiniteOperatorReductionCore.lean` | `Agda/DASHI/Analysis/FiniteOperatorReductionCore.agda` | 5 | 5 | — |
| `Lean/AgdaMirror/Analysis.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/AnomalyContracts.lean` | `Agda/DASHI/Algebra/AnomalyContracts.agda` | 8 | 4 | `Y`, `cancel-U1³`, `cancel-221`, `cancel-331` |
| `Lean/AgdaMirror/AnomalyContracts.lean` | `Agda/DASHI/Algebra/AnomalyContracts.agda` | 8 | 4 | `Y`, `cancel-U1³`, `cancel-221`, `cancel-331` |
| `Lean/AgdaMirror/ArithmeticCoprimeLayer.lean` | `Agda/DASHI/Arithmetic/CoprimeLayer.agda` | 5 | 2 | `trackedBaseVsPrimePowerCoprime`, `CoprimeLayer`, `coprimeLayer` |
| `Lean/AgdaMirror/ArithmeticDeltaGrowth.lean` | `Agda/DASHI/Arithmetic/DeltaGrowth.agda` | 7 | 4 | `pow-mono-divides`, `vp-depth-power-divides`, `deltaPower≤sum` |
| `Lean/AgdaMirror/ArithmeticIntegerEmbedding.lean` | `Agda/DASHI/Arithmetic/ArithmeticIntegerEmbedding.agda` | 25 | 16 | `Int`, `embed`, `embed-primeContribution`, `embed-primeIndexedPressure`, `embed-StateCancellationPressure`, `embed-StateSupportPressure`, … (+3) |
| `Lean/AgdaMirror/AuthorityBoundary.lean` | `Agda/DASHI/Core/AuthorityBoundary.agda` | 5 | 5 | — |
| `Lean/AgdaMirror/Base369.lean` | `Agda/Base369.agda` | 32 | 26 | `triXor-closed`, `triXor-identityˡ`, `hexXor-closed`, `hexXor-identityˡ`, `nonaryXor-closed`, `nonaryXor-identityˡ` |
| `Lean/AgdaMirror/CCRFromProjection.lean` | `Agda/DASHI/Algebra/Quantum/CCRFromProjection.agda` | 5 | 5 | — |
| `Lean/AgdaMirror/CRTJFixedPointBridge.lean` | `Agda/CRTJFixedPointBridge.agda` | 6 | 5 | `CRTJFixedPointBridge` |
| `Lean/AgdaMirror/CRTPeriod.lean` | `Agda/CRTPeriod.agda` | 3 | 2 | `d` |
| `Lean/AgdaMirror/CancellationPressure.lean` | `Agda/DASHI/Arithmetic/CancellationPressureCore.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/CancellationPressure.lean` | `Agda/DASHI/Arithmetic/CancellationPressureBound.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/CancellationPressureFromCanonical.lean` | `Agda/DASHI/Arithmetic/CancellationPressureFromCanonical.agda` | 16 | 7 | `canonicalCancellationPressure`, `canonicalCancellationPressureBoundFn`, `canonicalCancellationPressure≤bound`, `canonicalCancellationPressureBound-step`, `canonicalCancellationPressureBound`, `CancellationPressureFromCanonical`, … (+3) |
| `Lean/AgdaMirror/CancellationPressureRefinement.lean` | `Agda/DASHI/Arithmetic/CancellationPressureRefinement.agda` | 6 | 6 | — |
| `Lean/AgdaMirror/CliffordUniversalProperty.lean` | `Agda/cubical/Cubical/Categories/Site/Sheafification/UniversalProperty.agda` | 0 | 0 | — |
| `Lean/AgdaMirror/ConstraintAlgebraClosure.lean` | `Agda/DASHI/Algebra/ConstraintAlgebraClosure.agda` | 4 | 2 | `ConstraintConsequences`, `ConstraintClosure-theorem` |
| `Lean/AgdaMirror/ConstraintClosure.lean` | `Agda/DASHI/Algebra/Quantum/ConstraintClosure.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/Contraction.lean` | `Agda/Contraction.agda` | 4 | 3 | `_≢_` |
| `Lean/AgdaMirror/CoprimeLayer.lean` | `Agda/DASHI/Arithmetic/CoprimeLayer.agda` | 5 | 3 | `trackedBaseVsPrimePowerCoprime`, `distinctTrackedPrimePowersCoprime` |
| `Lean/AgdaMirror/Core/ComparisonLawCore.lean` | `Agda/DASHI/Core/ComparisonLawCore.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/Core/ContextIndexedEncoding.lean` | `Agda/DASHI/Core/ContextIndexedEncoding.agda` | 7 | 6 | `_×_` |
| `Lean/AgdaMirror/Core.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/DASHIAlgebra.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/DASHIValuation.lean` | `Agda/DASHI/Arithmetic/VpDepth.agda` | 12 | 6 | `_≢_`, `suc-neq`, `suc-injective`, `zero-neq-suc`, `swap-divides-sum`, `vp-depth-stable-next` |
| `Lean/AgdaMirror/DASHIValuation.lean` | `Agda/DASHI/Arithmetic/NatBoolEquality.agda` | 4 | 3 | `_≢_` |
| `Lean/AgdaMirror/DashiMarkov.lean` | `Agda/DASHI/Core/DashiMarkov.agda` | 6 | 5 | `DASHIMarkovStatus` |
| `Lean/AgdaMirror/DeltaGrowth.lean` | `Agda/DASHI/Arithmetic/DeltaGrowth.agda` | 7 | 2 | `pow`, `deltaPowerDividesSum`, `deltaPower≤sum`, `DeltaGrowthStructure`, `deltaGrowthStructure` |
| `Lean/AgdaMirror/DeltaInteraction.lean` | `Agda/DASHI/Arithmetic/DeltaInteraction.agda` | 6 | 6 | — |
| `Lean/AgdaMirror/DeltaRarity.lean` | `Agda/DASHI/Arithmetic/DeltaRarity.agda` | 14 | 4 | `thresholdMask15`, `largeDeltaAt2`, `largeDeltaMask15`, `thresholdAt≤supportMaskAt`, `thresholdCount≤supportPrimeCount`, `thresholdRarity`, … (+4) |
| `Lean/AgdaMirror/DimensionFixedPoint.lean` | `Agda/DASHI/Algebra/Quantum/DimensionFixedPoint.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/DimensionFixedPointInstance.lean` | `Agda/DASHI/Algebra/Quantum/DimensionFixedPointInstance.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/EnergyMetric.lean` | `Agda/MDL/Core.agda` | 12 | 0 | `CodeLength`, `Dataset`, `Model`, `modelTotalLength`, `better`, `Subset`, … (+6) |
| `Lean/AgdaMirror/EnergyMetric.lean` | `Agda/DASHI/Energy/TranslationInvariantMetric.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/FixedPoint.lean` | `Agda/FixedPoint.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/GaugeGroupContract.lean` | `Agda/DASHI/Algebra/GaugeGroupContract.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/GlobalPressure.lean` | `Agda/DASHI/Arithmetic/GlobalPressure.agda` | 9 | 6 | `wallDeltaAt≡deltaAt`, `wallDelta15≡delta15`, `totalPressure≡wallPressure` |
| `Lean/AgdaMirror/GodelLattice.lean` | `Ontology/GodelLattice.agda` **(not in tree)** | – | – | – |
| `Lean/AgdaMirror/HalfTrit.lean` | `Agda/DASHI/Algebra/Trit/HalfTrit.agda` | 17 | 4 | `embedTrit-negOne-collapses-with-negHalf`, `embedTrit-posHalf-collapses-with-posOne`, `HalfTritConstructionStatus`, `HalfTritDuplicateFreedomStatus`, `HalfTritResidualObligation`, `canonicalHalfTritResidualObligations`, … (+7) |
| `Lean/AgdaMirror/HalfTritIndexed.lean` | `Agda/DASHI/Algebra/Trit/HalfTritIndexed.agda` | 25 | 10 | `HalfTritIndexedIndex`, `_≟Indexed_`, `allHalfTritIndexedValuesLength`, `NotIn`, `NoDuplicates`, `indexedSeparatesNegOneNegHalf`, … (+9) |
| `Lean/AgdaMirror/JFixedPoint.lean` | `Agda/JFixedPoint.agda` | 15 | 9 | `fixed-0`, `fixed-1`, `fixed-2`, `fixed-100`, `tower-1`, `tower-3` |
| `Lean/AgdaMirror/JoinSurface.lean` | `Agda/DASHI/Core/UniversalOperatorBasis.agda` | 6 | 3 | `CoordinateTransport`, `UniversalOperatorBasis`, `JoinCompatibleUniversalOperatorBasis` |
| `Lean/AgdaMirror/KPrimeInteraction.lean` | `Agda/DASHI/Arithmetic/KPrimeInteraction.agda` | 15 | 12 | `kThresholdMask`, `KPrimeInteractionSurface`, `kPrimeInteractionSurface` |
| `Lean/AgdaMirror/KernelMonoid.lean` | `Agda/DASHI/Core/KernelMonoid.agda` | 7 | 6 | `_∘K_` |
| `Lean/AgdaMirror/LensKernel.lean` | `Agda/DASHI/Core/LensKernel.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/LogicTlurey.lean` | `Agda/LogicTlurey.agda` | 19 | 15 | `sym`, `cong`, `length`, `_++_` |
| `Lean/AgdaMirror/LoomRelationAlgebra.lean` | `Agda/LoomRelationAlgebra.agda` | 13 | 13 | — |
| `Lean/AgdaMirror/MaxPressure.lean` | `Agda/DASHI/Arithmetic/MaxPressure.agda` | 10 | 2 | `maxNat≤sum`, `max15≤sum15`, `maxPressure≤totalPressure`, `weightedMaxPressure≤weightedPressure`, `weightedMaxPressure≤weightedSupport`, `maxPressure≤trackedSupport`, … (+2) |
| `Lean/AgdaMirror/MonsterGroups.lean` | `Agda/MonsterGroups.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/MonsterOntos.lean` | `Agda/MonsterOntos.agda` | 4 | 3 | `_≟_` |
| `Lean/AgdaMirror/MonsterProjection15.lean` | `Agda/DASHI/Algebra/MonsterUltrametric15.agda` | 12 | 4 | `len`, `lcpLen-self-eq`, `id-zeroMask`, `lcpLen-symmetric`, `len-const`, `dMask-symmetric`, … (+2) |
| `Lean/AgdaMirror/MonsterProjection15.lean` | `Agda/DASHI/Algebra/MonsterProjection15.agda` | 6 | 1 | `_≢_`, `lcpLen-zero→eq`, `lcpLen≤len`, `d0→eq`, `Contractive≢` |
| `Lean/AgdaMirror/MonsterVectors.lean` | `Agda/MonsterVectors.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/MonsterWalk.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/Moonshine.lean` | `Agda/Moonshine.agda` | 15 | 15 | — |
| `Lean/AgdaMirror/MoonshineBridge.lean` | `Agda/DASHI/Algebra/MoonshineBridge.agda` | 6 | 6 | — |
| `Lean/AgdaMirror/MoonshineEarn.lean` | *(none declared)* | – | – | – |
| `Lean/AgdaMirror/NoGlobalAttractor.lean` | `Agda/DASHI/Algebra/Quantum/NoGlobalAttractor.agda` | 5 | 3 | `NoGlobalAttractorAxioms`, `invertible-nontrivial-no-attractor` |
| `Lean/AgdaMirror/NormalizeAdd.lean` | `Agda/DASHI/Arithmetic/NormalizeAddState.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/NormalizeAdd.lean` | `Agda/DASHI/Arithmetic/NormalizeAdd.agda` | 7 | 7 | — |
| `Lean/AgdaMirror/NormalizeAdd.lean` | `Agda/DASHI/Arithmetic/CanonicalResidueZero.agda` | 6 | 3 | `normalizeAdd-residueBudget-zero`, `CanonicalResidueZeroSurface`, `canonicalResidueZeroSurface` |
| `Lean/AgdaMirror/NormalizeAddNonexpansive.lean` | `Agda/DASHI/Arithmetic/NormalizeAddNonexpansive.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/NormalizeAddSumPreservation.lean` | `Agda/DASHI/Arithmetic/NormalizeAddSumPreservation.agda` | 7 | 5 | `normalizeAddOneStepSumInvariantEvidence`, `normalizeAddOneStepSumInvariantWitness` |
| `Lean/AgdaMirror/OperatorMonoidClosed.lean` | `Agda/DASHI/Algebra/OperatorMonoidClosed.agda` | 6 | 4 | `_∘_`, `id` |
| `Lean/AgdaMirror/OperatorTypes.lean` | `Agda/DASHI/Core/OperatorTypes.agda` | 6 | 5 | `Classifies` |
| `Lean/AgdaMirror/Overflow.lean` | `Agda/Overflow.agda` | 17 | 8 | `congOverflow`, `_≺_`, `compare-below→≺`, `compare-above→≺`, `compare-equal→≡`, `compare-≺→below`, … (+3) |
| `Lean/AgdaMirror/PhysicsConformance.lean` | `Agda/DASHI/Algebra/PhysicsConformance.agda` | 2 | 1 | `physics-conformance` |
| `Lean/AgdaMirror/PhysicsSignature.lean` | `Agda/DASHI/Algebra/PhysicsSignature.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/PrimeIndexedPressure.lean` | `Agda/DASHI/Arithmetic/PrimeIndexedPressure.agda` | 8 | 8 | — |
| `Lean/AgdaMirror/ProjectionOrthogonality.lean` | `Agda/DASHI/Algebra/Quantum/ProjectionOrthogonality.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/ProjectionVsInvertible.lean` | `Agda/DASHI/Algebra/ProjectionVsInvertible.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/Q.lean` | `Agda/DASHI/Core/Q.agda` | 8 | 3 | `_+ℚ_`, `_-ℚ_`, `_*ℚ_`, `zeroℚ`, `oneℚ` |
| `Lean/AgdaMirror/QuantumInterface.lean` | `Agda/DASHI/Algebra/QuantumInterface.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/QuantumMeasurement.lean` | `Agda/DASHI/Physics/Measurement.agda` | 4 | 0 | `PredictionTheory`, `MeasurementTheory`, `QuantumMeasurement`, `BornLike` |
| `Lean/AgdaMirror/QuantumUnitary.lean` | `Agda/DASHI/Algebra/Quantum/Unitary.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/QuotientSetoidSurface.lean` | `Agda/DASHI/Foundations/QuotientSetoidSurface.agda` | 11 | 8 | `subst`, `SetoidUnaryOperationSurface`, `SetoidBinaryOperationSurface` |
| `Lean/AgdaMirror/RealTernaryCarrier.lean` | `Agda/DASHI/Physics/RealTernaryCarrier.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/SWAR.lean` | `Agda/SWAR_Equivalence.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/AntiFascistSystem.agda` | 4 | 1 | `invertibleInjective`, `DistinctionPreserving`, `rankPreservationImpliesNonincrease` |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/FascisticSystem.agda` | 5 | 3 | `ProperContraction`, `properContractionIsNonInjective` |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/MaassRestoration.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/ActionMonotonicity.agda` | 2 | 0 | `Action`, `Monotone` |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/PrimeRoles.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/HGSA_Fixpoints.agda` | 3 | 0 | `Eventually`, `AES`, `AES-theorem` |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/ThreeAdic_Attractor.agda` | 0 | 0 | — |
| `Lean/AgdaMirror/Scaffolding.lean` | `Agda/Z6_RegularInverse.agda` | 3 | 0 | `Z6`, `Regular`, `regular` |
| `Lean/AgdaMirror/SignatureDerivation.lean` | `Agda/DASHI/Algebra/Quantum/SignatureDerivation.agda` | 2 | 2 | — |
| `Lean/AgdaMirror/SpinEmergence.lean` | `Agda/DASHI/Algebra/Quantum/SpinEmergence.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/SpinFromEvenClifford.lean` | `Agda/DASHI/Algebra/Quantum/SpinFromEvenClifford.agda` | 4 | 4 | — |
| `Lean/AgdaMirror/StageQuotient.lean` | `Agda/DASHI/Algebra/StageQuotient.agda` | 16 | 13 | `_≢_`, `Stage12FibreSurface`, `canonicalStage12FibreSurface` |
| `Lean/AgdaMirror/TenfoldBridges.lean` | `Agda/TenfoldBridges.agda` | 5 | 5 | — |
| `Lean/AgdaMirror/TetralemmaBridge.lean` | `Agda/DASHI/Algebra/TetralemmaBridge.agda` | 19 | 18 | `_≢_` |
| `Lean/AgdaMirror/TrackedCoprimeTable.lean` | `Agda/DASHI/Arithmetic/TrackedCoprimeTable.agda` | 4 | 3 | `_≢_` |
| `Lean/AgdaMirror/TrackedSupport.lean` | `Agda/DASHI/Arithmetic/TrackedSupport.agda` | 8 | 3 | `deltaAt≤supportAt`, `sum15≤`, `totalPressure≤trackedSupport`, `TrackedSupportStructure`, `trackedSupportStructure` |
| `Lean/AgdaMirror/TreeCCR.lean` | `Agda/DASHI/Algebra/Quantum/TreeCCR.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/TritBridge.lean` | `Agda/DASHI/Algebra/TritTriTruthBridge.agda` | 17 | 11 | `_≢_`, `inv-reflection-not-rotation-at-neg`, `tritXor-identityˡ`, `inv-reflection-involutive`, `inv-reflection-not-tritXor-hom-at-neg`, `tritTriTruthIsoSurface` |
| `Lean/AgdaMirror/TypedResidualBasisDecomposition.lean` | `Agda/DASHI/Core/TypedResidualBasisDecomposition.agda` | 12 | 9 | `OpenTRBDObstructionName`, `DASHIDerivationRequest`, `OpenShapeLawRequest` |
| `Lean/AgdaMirror/UFTC_Lattice.lean` | `Agda/UFTC_Lattice.agda` | 12 | 7 | `_⊑_`, `_⊔s_`, `Monotone₂`, `ConeInterior`, `ConeInteriorPreserved` |
| `Lean/AgdaMirror/UVFiniteness.lean` | `Agda/DASHI/Algebra/Quantum/UVFiniteness.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/Ultrametric.lean` | `Agda/Ultrametric.agda` | 2 | 1 | `max` |
| `Lean/AgdaMirror/UnitaryVsCollapse.lean` | `Agda/DASHI/Algebra/UnitaryVsCollapse.agda` | 3 | 3 | — |
| `Lean/AgdaMirror/UniversalOperatorBasis.lean` | `Agda/DASHI/Core/UniversalOperatorBasis.agda` | 6 | 1 | `JoinSurface`, `JoinPreserving`, `CoordinateTransport`, `DualOrderSymmetry`, `JoinCompatibleUniversalOperatorBasis` |
| `Lean/AgdaMirror/ValuationLemmas.lean` | `Agda/DASHI/Arithmetic/ValuationLemmas.agda` | 3 | 2 | `same-minus-zero` |
| `Lean/AgdaMirror/ValuationLemmas.lean` | `Agda/DASHI/Arithmetic/VpAddUnequal.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/Vec15Descriptive.lean` | `Agda/DASHI/Statistics/Vec15Descriptive.agda` | 8 | 6 | `maxNat`, `minNat` |
| `Lean/AgdaMirror/Vec15Inference.lean` | `Agda/DASHI/Statistics/Vec15Inference.agda` | 50 | 28 | `CorrelationResult`, `RegressionResult`, `PCAResult`, `ClusterResult`, `FactorAnalysisResult`, `ModelInput`, … (+16) |
| `Lean/AgdaMirror/Vec15Order.lean` | `Agda/DASHI/Statistics/Vec15Order.agda` | 40 | 24 | `one`, `two`, `three`, `four`, `five`, `six`, … (+10) |
| `Lean/AgdaMirror/Vec15Robust.lean` | `Agda/DASHI/Statistics/Vec15Robust.agda` | 40 | 37 | `maxNat-self`, `minNat-self`, `zeroCarrier15` |
| `Lean/AgdaMirror/VpAddUnequal.lean` | `Agda/DASHI/Arithmetic/VpAddUnequal.agda` | 1 | 1 | — |
| `Lean/AgdaMirror/VpTrue.lean` | `Agda/DASHI/Arithmetic/VpTrue.agda` | 5 | 4 | `vp-true-stable` |
| `Lean/AgdaMirror/WeightedPressure.lean` | `Agda/DASHI/Arithmetic/WeightedPressure.agda` | 12 | 8 | `weightedSum15≤`, `weightedPressure≤weightedSupport`, `WeightedPressureStructure`, `weightedPressureStructure` |

pairs examined              : 123
  resolved to an Agda file  : 116
  claimed source not found  : 1
  no source declared        : 6
Agda declarations in scope  : 1012
  with a name-level match   : 668
  coverage                  : 66.0%

Name-level correspondence is provenance evidence only; it is not a proof
that a mirrored statement is faithful to the Agda statement.

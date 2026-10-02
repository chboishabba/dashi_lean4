import Mathlib
import Integration.TwistronicsRelativeRegistrationComparator
import Integration.TwistronicsRegistrationControlFutureSplit

/-!
# Flat-band / charge-order cross-pollination

Lean mirror of the repository-owned theorem shape shared by:

* magic-angle / registration-engineered twisted bilayer graphene, and
* interaction-driven flat-band / charge-order Fe5GeTe2.

External provenance is kept in comments/boundary data here; the Agda owner
carries the attributed-source atlas.  No physical mechanism is identified
across the two materials.
-/

namespace Integration.CondensedMatterFlatBandCrossPollination

structure BandSystem (Momentum Energy : Type) where
  energy : Momentum → Energy

structure FlatPairWitness
    {Momentum Energy : Type}
    (band : BandSystem Momentum Energy) where
  leftMomentum : Momentum
  rightMomentum : Momentum
  sameEnergy :
    band.energy leftMomentum = band.energy rightMomentum
  distinctMomentum :
    leftMomentum ≠ rightMomentum

theorem flatPair_not_injective
    {Momentum Energy : Type}
    (band : BandSystem Momentum Energy)
    (w : FlatPairWitness band) :
    ¬ Function.Injective band.energy := by
  intro h
  exact w.distinctMomentum (h w.sameEnergy)

def EnergyFibre
    {Momentum Energy : Type}
    (band : BandSystem Momentum Energy)
    (reference : Momentum) :=
  { momentum : Momentum // band.energy momentum = band.energy reference }

structure FlatBandPhaseSplitWitness
    {Momentum Energy Phase : Type}
    (band : BandSystem Momentum Energy)
    (phaseObserver : Momentum → Phase) where
  flatPair : FlatPairWitness band
  phaseSeparatesPair :
    phaseObserver flatPair.leftMomentum ≠
      phaseObserver flatPair.rightMomentum

def PhaseDescendsThroughEnergy
    {Momentum Energy Phase : Type}
    (band : BandSystem Momentum Energy)
    (phaseObserver : Momentum → Phase) : Prop :=
  ∀ ⦃left right⦄,
    band.energy left = band.energy right →
    phaseObserver left = phaseObserver right

theorem flatBandPhaseSplit_refutes_energy_only_descent
    {Momentum Energy Phase : Type}
    (band : BandSystem Momentum Energy)
    (phaseObserver : Momentum → Phase)
    (w : FlatBandPhaseSplitWitness band phaseObserver) :
    ¬ PhaseDescendsThroughEnergy band phaseObserver := by
  intro descent
  exact w.phaseSeparatesPair (descent w.flatPair.sameEnergy)

inductive FlatteningMechanism
  | registrationEngineered
  | interactionDriven
  deriving DecidableEq, Repr

theorem mechanisms_distinct :
    FlatteningMechanism.registrationEngineered ≠
      FlatteningMechanism.interactionDriven := by
  decide

structure ThreeFoldPresentation (Momentum FoldedMomentum : Type) where
  first : Momentum
  second : Momentum
  third : Momentum
  fold : Momentum → FoldedMomentum
  firstSecondDistinct : first ≠ second
  firstThirdDistinct : first ≠ third
  secondThirdDistinct : second ≠ third
  firstSecondFoldTogether : fold first = fold second
  firstThirdFoldTogether : fold first = fold third

theorem threeFold_not_injective
    {Momentum FoldedMomentum : Type}
    (p : ThreeFoldPresentation Momentum FoldedMomentum) :
    ¬ Function.Injective p.fold := by
  intro h
  exact p.firstSecondDistinct (h p.firstSecondFoldTogether)

def canonicalThreeFoldPresentation :
    ThreeFoldPresentation (Fin 3) Unit where
  first := 0
  second := 1
  third := 2
  fold := fun _ => ()
  firstSecondDistinct := by decide
  firstThirdDistinct := by decide
  secondThirdDistinct := by decide
  firstSecondFoldTogether := rfl
  firstThirdFoldTogether := rfl

/-!
Primary Fe5GeTe2 source:
Q. Gao et al., "Interaction-driven flat band and charge order in Fe5GeTe2",
Science Advances 12(32), eaeg5930 (2026), DOI 10.1126/sciadv.aeg5930.

The paper reports high-resolution ARPES evidence for:
* a flat band at the Fermi level throughout the Brillouin zone;
* sqrt(3) x sqrt(3) R30-degree charge order;
* band folding within 30 meV below EF;
* logarithmic temperature dependence of spectral weight;
and suggests a phenomenological Kondo-like coherent Fermi liquid.

This receipt deliberately does not contain raw ARPES arrays or a derived
microscopic Kondo Hamiltonian.
-/

structure Fe5GeTe2SourceReplay where
  flatBandAtFermiLevelReported : Bool
  flatBandThroughoutBrillouinZoneReported : Bool
  chargeOrderReported : Bool
  bandFoldingWindowBelowFermiMeV : Nat
  logarithmicTemperatureDependenceReported : Bool
  phenomenologicalKondoLikeInterpretationAttributed : Bool
  rawARPESArrayPaid : Bool
  exactMicroscopicHamiltonianPaid : Bool
  roomTemperatureOperationDemonstrated : Bool
  memoryDeviceDemonstrated : Bool
  deriving Repr

def canonicalFe5GeTe2SourceReplay : Fe5GeTe2SourceReplay where
  flatBandAtFermiLevelReported := true
  flatBandThroughoutBrillouinZoneReported := true
  chargeOrderReported := true
  bandFoldingWindowBelowFermiMeV := 30
  logarithmicTemperatureDependenceReported := true
  phenomenologicalKondoLikeInterpretationAttributed := true
  rawARPESArrayPaid := false
  exactMicroscopicHamiltonianPaid := false
  roomTemperatureOperationDemonstrated := false
  memoryDeviceDemonstrated := false

inductive FlatBandRoute
  | magicAngleRegistration
  | interactionDrivenFe5GeTe2
  deriving DecidableEq, Repr

theorem routes_distinct :
    FlatBandRoute.magicAngleRegistration ≠
      FlatBandRoute.interactionDrivenFe5GeTe2 := by
  decide

structure CrossPollinationBoundary where
  bistritzerMacDonaldMagicAngleSourceRetained : Bool
  caoCorrelatedPhaseSourcesRetained : Bool
  huInSituRegistrationControlSourceRetained : Bool
  gaoFe5GeTe2SourceRetained : Bool
  sharedObservableFibreTheoremShapeUsed : Bool
  sharedConsumerRefinementTheoremShapeUsed : Bool
  twistAngleIdentifiedWithFeInteractionStrength : Bool
  grapheneFlatBandIdentifiedWithFeFlatBandSameObject : Bool
  grapheneCorrelatedPhaseIdentifiedWithFeChargeOrder : Bool
  kondoLikeInterpretationTransferredToGraphene : Bool
  sqrt3R30OrderTransferredToGraphene : Bool
  exactExperimentalFlatPairOrderSplitWitnessInvented : Bool
  deriving Repr

def canonicalBoundary : CrossPollinationBoundary where
  bistritzerMacDonaldMagicAngleSourceRetained := true
  caoCorrelatedPhaseSourcesRetained := true
  huInSituRegistrationControlSourceRetained := true
  gaoFe5GeTe2SourceRetained := true
  sharedObservableFibreTheoremShapeUsed := true
  sharedConsumerRefinementTheoremShapeUsed := true
  twistAngleIdentifiedWithFeInteractionStrength := false
  grapheneFlatBandIdentifiedWithFeFlatBandSameObject := false
  grapheneCorrelatedPhaseIdentifiedWithFeChargeOrder := false
  kondoLikeInterpretationTransferredToGraphene := false
  sqrt3R30OrderTransferredToGraphene := false
  exactExperimentalFlatPairOrderSplitWitnessInvented := false

end Integration.CondensedMatterFlatBandCrossPollination

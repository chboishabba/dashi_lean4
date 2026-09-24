import Mathlib
import Integration.PredictionEnvelope
import Integration.Experiment.ProbabilityLayer
import Integration.Base369Schrodinger

/-!
# Exact forecast verification and observation-state separation (validation root)

Lean mirror of the thin forecast-verification kernel added to dashi_agda.

This file does not introduce another experiment/search/statistics framework.
It supplies the missing probabilistic-forecast arithmetic and reuses the
existing Integration observation/fibre machinery.
-/

namespace Integration.ForecastVerification

inductive BinaryOutcome where
  | no
  | yes
  deriving DecidableEq, Repr

def outcomeValue : BinaryOutcome → ℚ
  | .no => 0
  | .yes => 1

structure Probability where
  value : ℚ
  lower : 0 ≤ value
  upper : value ≤ 1
  deriving Repr

def brierLossValue (p : ℚ) (y : BinaryOutcome) : ℚ :=
  (p - outcomeValue y) ^ 2

def brierLoss (p : Probability) (y : BinaryOutcome) : ℚ :=
  brierLossValue p.value y

@[simp] theorem brier_half_no :
    brierLossValue (1 / 2 : ℚ) .no = 1 / 4 := by
  norm_num [brierLossValue, outcomeValue]

@[simp] theorem brier_half_yes :
    brierLossValue (1 / 2 : ℚ) .yes = 1 / 4 := by
  norm_num [brierLossValue, outcomeValue]

theorem brier_half (y : BinaryOutcome) :
    brierLossValue (1 / 2 : ℚ) y = 1 / 4 := by
  cases y <;> simp

theorem brier_nonneg (p : Probability) (y : BinaryOutcome) :
    0 ≤ brierLoss p y := by
  cases y <;> simp [brierLoss, brierLossValue, outcomeValue] <;> positivity

theorem brier_le_one (p : Probability) (y : BinaryOutcome) :
    brierLoss p y ≤ 1 := by
  cases y <;>
    simp only [brierLoss, brierLossValue, outcomeValue] <;>
    nlinarith [p.lower, p.upper]

theorem brier_mem_unit_interval (p : Probability) (y : BinaryOutcome) :
    0 ≤ brierLoss p y ∧ brierLoss p y ≤ 1 :=
  ⟨brier_nonneg p y, brier_le_one p y⟩

structure BinaryLogScoreCoordinates (p : Probability) where
  negLogP : ℚ
  negLogOneMinusP : ℚ
  coordinateReference : String
  analyticLogReceiptReference : String

def logLoss {p : Probability} (c : BinaryLogScoreCoordinates p) :
    BinaryOutcome → ℚ
  | .no => c.negLogOneMinusP
  | .yes => c.negLogP

structure OddsPair where
  favourable : ℚ
  unfavourable : ℚ
  deriving Repr

def oddsPair (p : Probability) : OddsPair :=
  ⟨p.value, 1 - p.value⟩

structure OddsUpdateReceipt (prior posterior : Probability) where
  likelihoodNumerator : ℚ
  likelihoodDenominator : ℚ
  crossMultipliedUpdate :
    (oddsPair posterior).favourable *
        (oddsPair prior).unfavourable * likelihoodDenominator =
      (oddsPair posterior).unfavourable *
        (oddsPair prior).favourable * likelihoodNumerator
  evidenceReference : String
  calibrationReference : String

structure OddsComparisonReceipt (left right : Probability) where
  ratioNumerator : ℚ
  ratioDenominator : ℚ
  crossMultipliedRatio :
    (oddsPair left).favourable *
        (oddsPair right).unfavourable * ratioDenominator =
      (oddsPair left).unfavourable *
        (oddsPair right).favourable * ratioNumerator
  comparisonReference : String

inductive ResolutionState where
  | open
  | awaitingJudge
  | scored (outcome : BinaryOutcome) (evidenceRef : String)
  | voided (reason : String) (evidenceRef : String)
  deriving Repr

structure PublishedForecast where
  forecastReference : String
  propositionReference : String
  issuedAtReference : String
  horizonReference : String
  probability : Probability
  domainReference : String
  originReference : String
  modelReference : String
  sourceStateReference : String
  resolutionPolicyReference : String

structure ForecastEpistemicCut (Time Evidence : Type)
    (le : Time → Time → Prop) where
  issuedAt : Time
  availableAt : Evidence → Time
  admissibleAtForecast : Evidence → Prop
  admissibilitySound :
    ∀ atom, admissibleAtForecast atom → le (availableAt atom) issuedAt
  hindsightAtom : Evidence → Prop
  cutReference : String

structure HindsightSeparation {Time Evidence : Type}
    {le : Time → Time → Prop}
    (cut : ForecastEpistemicCut Time Evidence le) where
  lateAtom : Evidence
  knownInHindsight : cut.hindsightAtom lateAtom
  notAdmissibleAtForecast : ¬ cut.admissibleAtForecast lateAtom
  separationReference : String

structure BrierDecompositionReceipt where
  score : ℚ
  reliability : ℚ
  resolution : ℚ
  uncertainty : ℚ
  reconstructs : score = reliability - resolution + uncertainty
  partitionReference : String
  cohortReference : String

inductive ScoreRecomputationKind where
  | rawWindowDelta
  | holdCohortRuleFixed
  | holdResolvedIntersectionFixed
  | holdOriginMixtureFixed
  | holdDomainMixtureFixed
  | holdResolutionObserverFixed
  deriving DecidableEq, Repr

structure ScoreRecomputation where
  kind : ScoreRecomputationKind
  sourceSnapshotReference : String
  targetSnapshotReference : String
  controlledCoordinateReference : String
  sourceScore : ℚ
  targetScore : ℚ
  delta : ℚ
  deltaCorrect : delta = targetScore - sourceScore

inductive ReferenceForecastKind where
  | constantHalf
  | cohortBaseRate
  | historicalRollingBaseRate
  | marketComparator
  | declaredSimpleModel
  deriving DecidableEq, Repr

structure ReferenceForecastReceipt where
  kind : ReferenceForecastKind
  cohortReference : String
  informationCutReference : String
  score : ℚ
  referenceModelReference : String

def worldMonitorLedgerCount : ℕ := 1058
def worldMonitorResolvedCount : ℕ := 862
def worldMonitorScoredCount : ℕ := 541
def worldMonitorVoidedCount : ℕ := 321
def worldMonitorAwaitingJudgeCount : ℕ := 94
def worldMonitorOpenCount : ℕ := 102
def worldMonitorHeadlineCount : ℕ := 200
def worldMonitorExcludedScoredCount : ℕ := 341

theorem worldMonitor_ledger_partition :
    worldMonitorResolvedCount + worldMonitorAwaitingJudgeCount +
      worldMonitorOpenCount = worldMonitorLedgerCount := by
  norm_num [worldMonitorResolvedCount, worldMonitorAwaitingJudgeCount,
    worldMonitorOpenCount, worldMonitorLedgerCount]

theorem worldMonitor_resolved_partition :
    worldMonitorScoredCount + worldMonitorVoidedCount =
      worldMonitorResolvedCount := by
  norm_num [worldMonitorScoredCount, worldMonitorVoidedCount,
    worldMonitorResolvedCount]

theorem worldMonitor_headline_partition :
    worldMonitorHeadlineCount + worldMonitorExcludedScoredCount =
      worldMonitorScoredCount := by
  norm_num [worldMonitorHeadlineCount, worldMonitorExcludedScoredCount,
    worldMonitorScoredCount]

def worldMonitorHeadlineBrier : ℚ := 115 / 1000
def worldMonitorAllScoredBrier : ℚ := 195 / 1000
def worldMonitorMarketOverlapForecastBrier : ℚ := 149 / 1000
def worldMonitorMarketOverlapMarketBrier : ℚ := 72 / 1000
def worldMonitorMarketOverlapDelta : ℚ :=
  worldMonitorMarketOverlapMarketBrier - worldMonitorMarketOverlapForecastBrier

theorem worldMonitor_market_overlap_delta :
    worldMonitorMarketOverlapDelta = -(77 / 1000 : ℚ) := by
  norm_num [worldMonitorMarketOverlapDelta,
    worldMonitorMarketOverlapMarketBrier,
    worldMonitorMarketOverlapForecastBrier]

inductive ForecastFineState where
  | stableMechanismWeakEvidence
  | unstableRegimeTransientEvidence
  deriving DecidableEq, Repr

inductive CurrentProbabilitySurface where
  | same
  deriving DecidableEq, Repr

inductive NextProbabilitySurface where
  | low
  | high
  deriving DecidableEq, Repr

def currentProbabilityProjection : ForecastFineState → CurrentProbabilitySurface
  | _ => .same

def nextProbabilityObservation : ForecastFineState → NextProbabilitySurface
  | .stableMechanismWeakEvidence => .low
  | .unstableRegimeTransientEvidence => .high

theorem same_current_probability :
    currentProbabilityProjection .stableMechanismWeakEvidence =
      currentProbabilityProjection .unstableRegimeTransientEvidence := rfl

theorem different_next_probability :
    nextProbabilityObservation .stableMechanismWeakEvidence ≠
      nextProbabilityObservation .unstableRegimeTransientEvidence := by
  decide

theorem current_probability_not_sufficient :
    ¬ ∃ f : CurrentProbabilitySurface → NextProbabilitySurface,
      ∀ s, nextProbabilityObservation s = f (currentProbabilityProjection s) := by
  rintro ⟨f, h⟩
  have h₁ := h ForecastFineState.stableMechanismWeakEvidence
  have h₂ := h ForecastFineState.unstableRegimeTransientEvidence
  have hbad : NextProbabilitySurface.low = NextProbabilitySurface.high := by
    simpa [nextProbabilityObservation, currentProbabilityProjection] using h₁.trans h₂.symm
  cases hbad

theorem current_probability_projection_not_injective :
    ¬ Function.Injective currentProbabilityProjection := by
  intro h
  have hbad :
      ForecastFineState.stableMechanismWeakEvidence =
        ForecastFineState.unstableRegimeTransientEvidence :=
    h same_current_probability
  cases hbad

theorem controlled_recomputation_identity
    (r : ScoreRecomputation) :
    r.delta = r.targetScore - r.sourceScore :=
  r.deltaCorrect

end Integration.ForecastVerification

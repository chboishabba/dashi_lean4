import Mathlib
import AgdaMirror.Physics.YangMills.YMSourceAuthoritySurface

/-!
Lean mirror of `ArithmeticLemmaQueue.agda`.  Elementary natural/real arithmetic
is proved here.  The Agda postulates concerning an abstract exponential,
geometric summability, and imported rates are explicit fields of
`ImportedArithmeticData`.
-/
namespace AgdaMirror.Physics.YangMills.ArithmeticLemmaQueue

open YMSourceAuthoritySurface

/-- The DASHI-normalised decay constant. -/
def kappa : Nat := 1

theorem lemmaP04_1_kappaPositive : 0 < kappa := by decide

theorem lemmaP05_1_kappaNormalisedToOne : kappa = 1 := rfl

theorem lemmaP09_1_9271_lt_10000 : 9271 < 10000 := by decide

noncomputable def fourQ : ℝ := 9271 / 10000

def fourQValueCanonical : String := "4q = 0.9271 = 9271/10000"

theorem fourQValueCanonical_ok :
    fourQValueCanonical = "4q = 0.9271 = 9271/10000" := rfl

theorem fourQ_nonneg : 0 ≤ fourQ := by norm_num [fourQ]

theorem fourQ_lt_one : fourQ < 1 := by norm_num [fourQ]

theorem lemmaP09_2_cDiamOneImpliesMarginLtOne (cDiam : ℝ)
    (h : cDiam = 1) : cDiam * fourQ < 1 := by
  rw [h, one_mul]
  exact fourQ_lt_one

theorem lemmaP09_3_cDiamLeOne (mLink cDiam : ℝ) (hm : 1 ≤ mLink)
    (hc : cDiam = 1 / mLink) : cDiam ≤ 1 := by
  rw [hc]
  exact (div_le_one (by linarith)).2 hm

theorem lemmaP09_4_generalMarginFromBounds (cDiam : ℝ)
    (hc0 : 0 ≤ cDiam) (hc1 : cDiam ≤ 1) : cDiam * fourQ < 1 := by
  have hp : 0 ≤ cDiam * fourQ := mul_nonneg hc0 fourQ_nonneg
  have hu : cDiam * fourQ ≤ fourQ := by
    simpa using mul_le_mul_of_nonneg_right hc1 fourQ_nonneg
  linarith [fourQ_lt_one, hp, hu]

/-- Explicit replacement for all non-elementary Agda postulates in this file. -/
structure ImportedArithmeticData where
  expArith : ℝ → ℝ
  SummableSeq : (Nat → ℝ) → Prop
  geometricSeriesConverges : ∀ r : ℝ, 0 ≤ r → r < 1 →
    SummableSeq (fun n => r ^ n)
  entropyDecaySeriesConverges : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A * B < 1 →
    SummableSeq (fun n => A ^ n * B ^ n)
  animalCountRate : ℝ
  activityDecayRate : ℝ
  animalCountRateNonneg : 0 ≤ animalCountRate
  activityDecayRateNonneg : 0 ≤ activityDecayRate
  animalCountingBoundHolds : animalCountRate * activityDecayRate < 1

/-- The transport argument around the imported exponential is genuine. -/
theorem lemmaP05_2_normalisationPreservesDecay (d : ImportedArithmeticData)
    (k d0 d' : ℝ) (h : d' = k * d0) :
    d.expArith (-(k * d0)) = d.expArith (-d') := by rw [h]

theorem lemmaP07_3_fromBound (d : ImportedArithmeticData) :
    d.SummableSeq (fun n => d.animalCountRate ^ n * d.activityDecayRate ^ n) :=
  d.entropyDecaySeriesConverges d.animalCountRate d.activityDecayRate
    d.animalCountRateNonneg d.activityDecayRateNonneg d.animalCountingBoundHolds

structure EntropyMarginFromDiameterConstant where
  strictNatMargin : 9271 < 10000
  fourQIsCanonical : String
  fourQIsCanonicalOK : fourQIsCanonical = "4q = 0.9271 = 9271/10000"
  fourQNonnegative : 0 ≤ fourQ
  fourQStrictlySubunit : fourQ < 1
  marginTheorem : ∀ cDiam : ℝ, 0 ≤ cDiam → cDiam ≤ 1 → cDiam * fourQ < 1
  proofBoundary : String

def currentEntropyMarginFromDiameterConstant : EntropyMarginFromDiameterConstant :=
  { strictNatMargin := lemmaP09_1_9271_lt_10000
    fourQIsCanonical := fourQValueCanonical
    fourQIsCanonicalOK := rfl
    fourQNonnegative := fourQ_nonneg
    fourQStrictlySubunit := fourQ_lt_one
    marginTheorem := lemmaP09_4_generalMarginFromBounds
    proofBoundary := "P09 reducer: elementary arithmetic is checked in Lean." }

structure KPSummabilityReducerFromAnimalDecayAndMargin (d : ImportedArithmeticData) where
  reducer : ∀ A B : ℝ, 0 ≤ A → 0 ≤ B → A * B < 1 →
    d.SummableSeq (fun n => A ^ n * B ^ n)
  instantiatedReducer :
    d.SummableSeq (fun n => d.animalCountRate ^ n * d.activityDecayRate ^ n)
  proofBoundary : String

def currentKPSummabilityReducerFromAnimalDecayAndMargin (d : ImportedArithmeticData) :
    KPSummabilityReducerFromAnimalDecayAndMargin d :=
  { reducer := d.entropyDecaySeriesConverges
    instantiatedReducer := lemmaP07_3_fromBound d
    proofBoundary := "P07 is conditional on the explicit imported real-analysis fields." }

structure ArithmeticLemmaQueueBundle (d : ImportedArithmeticData) where
  kappaPositive : 0 < kappa
  kappaNormalised : kappa = 1
  fourQIsLtOne : fourQ < 1
  marginClosed : ∀ cDiam : ℝ, 0 ≤ cDiam → cDiam ≤ 1 → cDiam * fourQ < 1
  p09Reducer : EntropyMarginFromDiameterConstant
  kpSummable : d.SummableSeq (fun n => d.animalCountRate ^ n * d.activityDecayRate ^ n)
  p07Reducer : KPSummabilityReducerFromAnimalDecayAndMargin d
  proofBoundary : String
  noClayPromotion : clayYangMillsPromoted = false

def currentArithmeticLemmaQueueBundle (d : ImportedArithmeticData) :
    ArithmeticLemmaQueueBundle d :=
  { kappaPositive := lemmaP04_1_kappaPositive
    kappaNormalised := lemmaP05_1_kappaNormalisedToOne
    fourQIsLtOne := fourQ_lt_one
    marginClosed := lemmaP09_4_generalMarginFromBounds
    p09Reducer := currentEntropyMarginFromDiameterConstant
    kpSummable := lemmaP07_3_fromBound d
    p07Reducer := currentKPSummabilityReducerFromAnimalDecayAndMargin d
    proofBoundary := "Elementary arithmetic proved; analytic inputs remain explicit hypotheses."
    noClayPromotion := rfl }

end AgdaMirror.Physics.YangMills.ArithmeticLemmaQueue

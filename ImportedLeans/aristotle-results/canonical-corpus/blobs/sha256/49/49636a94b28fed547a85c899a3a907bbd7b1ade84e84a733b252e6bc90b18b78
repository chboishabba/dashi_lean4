import Integration.ApproximateIntertwiner

/-!
# The education lane's seven-gate algebra is conjunctive, and its rate frame is second-order

`Agda/DASHI/Education/RelationalEducationGateAlgebra.agda` supplies three
surfaces:

1. a seven-element gate enumeration and a record `EducationRelation` of seven
   *carrier types*, with `ValidEducationRelation` a record of seven inhabitants;
2. `EducationMetricGovernance`, five `Bool` fields each pinned to `false`
   (`surveyEqualsVoice`, `clickEqualsLearning`, `attendanceEqualsEngagement`,
   `accessEqualsEquity`, `trainingEqualsEnactment`);
3. `FiniteRate` with `multiplyRate`, and the exact computation
   `3/100 × 7/100 = 21/10000`, with a `Bool` field recording that `21` is *not*
   a first-order population count.

The Agda side proves (1) nothing beyond the record declaration, (2) that the
canonical inhabitant has all five flags `false`, and (3) the two `Nat`
multiplications by `refl`.  This file states and proves what those surfaces are
for.

## What is proved

* `validEquivProduct` — validity **is** the seven-fold product: a valid relation
  carries no information beyond one inhabitant of each gate carrier.
* `isEmpty_of_gate_empty` — **no gate is substitutable**: if a single gate
  carrier is empty then there is no valid relation, whatever the other six are.
* `sixOfSeven`, `sixOfSeven_no_witness`, `sixOfSeven_six_inhabited` — the
  counterexample making that sharp: six gates inhabited, one empty, no valid
  relation.  So gate satisfaction does not aggregate as a count.
* `metric_governance_fail_closed` — every inhabitant of
  `EducationMetricGovernance` has all five identification flags `false`: the
  record is fail-closed by construction, and this is the one thing it does say.
* `value_multiplyRate` — `multiplyRate` computes the product of the rational
  values, so the second-order rate is the independence product;
* `overlap_lt_marginals` — and it is *strictly below both marginals*;
* `rate_value_not_injective` — but the `FiniteRate` record is a presentation,
  not a value: `21/10000` and `42/20000` are distinct records with equal value.
  Any claim about "the rate" must therefore say which of the two it is about.
* `twentyOne_not_first_order` — the boundary flag's content: as a rate,
  `21/10000` is neither of the marginals nor `21/100`.

## Claim boundary

`EducationGate` is a seven-element label type and `FiniteRate` is a pair of
naturals.  Nothing here is a claim about education, early learning, policy,
measurement practice, or any empirical rate; the numbers `3/100` and `7/100`
are the Agda module's own constants and are used only as arithmetic inputs.
-/

namespace Integration.EducationGates

/-! ## The seven gates -/

/-- Mirror of `DASHI.Education.RelationalEducationGateAlgebra.EducationGate`. -/
inductive EducationGate
  | voiceGate | agencyGate | situatedEthicsGate | partnershipGate
  | enactmentGate | engagementIntelligenceGate | equityConditionsGate
  deriving DecidableEq, Repr, Fintype

/-- The canonical enumeration, in the Agda module's order. -/
def canonicalEducationGates : List EducationGate :=
  [.voiceGate, .agencyGate, .situatedEthicsGate, .partnershipGate,
   .enactmentGate, .engagementIntelligenceGate, .equityConditionsGate]

theorem canonicalEducationGates_nodup : canonicalEducationGates.Nodup := by decide

theorem canonicalEducationGates_complete (g : EducationGate) :
    g ∈ canonicalEducationGates := by decide +revert

/-- Mirror of `EducationRelation`: a carrier type for each gate. -/
structure EducationRelation where
  /-- Voice gate carrier. -/
  Voice : Type
  /-- Agency gate carrier. -/
  Agency : Type
  /-- Situated-ethics gate carrier. -/
  SituatedEthics : Type
  /-- Partnership gate carrier. -/
  Partnership : Type
  /-- Enactment gate carrier. -/
  Enactment : Type
  /-- Engagement-intelligence gate carrier. -/
  EngagementIntelligence : Type
  /-- Equity-conditions gate carrier. -/
  EquityConditions : Type

/-- The carrier a gate names. -/
def gateCarrier (E : EducationRelation) : EducationGate → Type
  | .voiceGate => E.Voice
  | .agencyGate => E.Agency
  | .situatedEthicsGate => E.SituatedEthics
  | .partnershipGate => E.Partnership
  | .enactmentGate => E.Enactment
  | .engagementIntelligenceGate => E.EngagementIntelligence
  | .equityConditionsGate => E.EquityConditions

/-- Mirror of `ValidEducationRelation`: one inhabitant of every gate carrier. -/
structure ValidEducationRelation (E : EducationRelation) where
  /-- Voice witness. -/
  voice : E.Voice
  /-- Agency witness. -/
  agency : E.Agency
  /-- Situated-ethics witness. -/
  situatedEthics : E.SituatedEthics
  /-- Partnership witness. -/
  partnership : E.Partnership
  /-- Enactment witness. -/
  enactment : E.Enactment
  /-- Engagement-intelligence witness. -/
  engagementIntelligence : E.EngagementIntelligence
  /-- Equity-conditions witness. -/
  equityConditions : E.EquityConditions

/-- Validity is exactly the seven-fold product. -/
def validEquivProduct (E : EducationRelation) :
    ValidEducationRelation E ≃
      (E.Voice × E.Agency × E.SituatedEthics × E.Partnership × E.Enactment ×
        E.EngagementIntelligence × E.EquityConditions) where
  toFun v := ⟨v.voice, v.agency, v.situatedEthics, v.partnership, v.enactment,
              v.engagementIntelligence, v.equityConditions⟩
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The witness a valid relation supplies at a given gate. -/
def ValidEducationRelation.at {E : EducationRelation} (v : ValidEducationRelation E) :
    ∀ g : EducationGate, gateCarrier E g
  | .voiceGate => v.voice
  | .agencyGate => v.agency
  | .situatedEthicsGate => v.situatedEthics
  | .partnershipGate => v.partnership
  | .enactmentGate => v.enactment
  | .engagementIntelligenceGate => v.engagementIntelligence
  | .equityConditionsGate => v.equityConditions

/-- **No gate is substitutable.**  One empty gate carrier empties the whole
validity type, whatever the other six carriers contain. -/
theorem isEmpty_of_gate_empty (E : EducationRelation) (g : EducationGate)
    (h : IsEmpty (gateCarrier E g)) : IsEmpty (ValidEducationRelation E) :=
  ⟨fun v => h.elim (v.at g)⟩

/-! ### The six-of-seven counterexample -/

/-- Six gates inhabited, one (equity conditions) empty. -/
def sixOfSeven : EducationRelation where
  Voice := Unit
  Agency := Unit
  SituatedEthics := Unit
  Partnership := Unit
  Enactment := Unit
  EngagementIntelligence := Unit
  EquityConditions := Empty

theorem sixOfSeven_six_inhabited :
    Nonempty sixOfSeven.Voice ∧ Nonempty sixOfSeven.Agency ∧
    Nonempty sixOfSeven.SituatedEthics ∧ Nonempty sixOfSeven.Partnership ∧
    Nonempty sixOfSeven.Enactment ∧ Nonempty sixOfSeven.EngagementIntelligence :=
  ⟨⟨()⟩, ⟨()⟩, ⟨()⟩, ⟨()⟩, ⟨()⟩, ⟨()⟩⟩

/-- **Gate satisfaction does not aggregate as a count**: six of seven gates
inhabited still yields no valid relation. -/
theorem sixOfSeven_no_witness : IsEmpty (ValidEducationRelation sixOfSeven) :=
  isEmpty_of_gate_empty sixOfSeven .equityConditionsGate ⟨fun e => e.elim⟩

/-! ## Metric governance is fail-closed -/

/-- Mirror of `EducationMetricGovernance`: five identification flags, each
carrying a proof that it is `false`. -/
structure EducationMetricGovernance where
  /-- "Survey = voice". -/
  surveyEqualsVoice : Bool
  /-- Pinned false. -/
  surveyEqualsVoiceIsFalse : surveyEqualsVoice = false
  /-- "Click = learning". -/
  clickEqualsLearning : Bool
  /-- Pinned false. -/
  clickEqualsLearningIsFalse : clickEqualsLearning = false
  /-- "Attendance = engagement". -/
  attendanceEqualsEngagement : Bool
  /-- Pinned false. -/
  attendanceEqualsEngagementIsFalse : attendanceEqualsEngagement = false
  /-- "Access = equity". -/
  accessEqualsEquity : Bool
  /-- Pinned false. -/
  accessEqualsEquityIsFalse : accessEqualsEquity = false
  /-- "Training = enactment". -/
  trainingEqualsEnactment : Bool
  /-- Pinned false. -/
  trainingEqualsEnactmentIsFalse : trainingEqualsEnactment = false

/-- The canonical inhabitant. -/
def canonicalEducationMetricGovernance : EducationMetricGovernance :=
  ⟨false, rfl, false, rfl, false, rfl, false, rfl, false, rfl⟩

/-- **Fail-closed**: *every* inhabitant has all five flags `false`, not just the
canonical one.  This is the whole formal content of the record: it cannot be
used to assert any of the five identifications. -/
theorem metric_governance_fail_closed (m : EducationMetricGovernance) :
    m.surveyEqualsVoice = false ∧ m.clickEqualsLearning = false ∧
    m.attendanceEqualsEngagement = false ∧ m.accessEqualsEquity = false ∧
    m.trainingEqualsEnactment = false :=
  ⟨m.surveyEqualsVoiceIsFalse, m.clickEqualsLearningIsFalse,
   m.attendanceEqualsEngagementIsFalse, m.accessEqualsEquityIsFalse,
   m.trainingEqualsEnactmentIsFalse⟩

/-! ## The rate frame -/

/-- Mirror of `FiniteRate`: a numerator and a denominator, as a *presentation*. -/
structure FiniteRate where
  /-- Numerator. -/
  numerator : ℕ
  /-- Denominator. -/
  denominator : ℕ
  deriving DecidableEq, Repr

/-- Mirror of `multiplyRate`: componentwise multiplication of presentations. -/
def multiplyRate (r s : FiniteRate) : FiniteRate :=
  ⟨r.numerator * s.numerator, r.denominator * s.denominator⟩

/-- The rational value of a presentation. -/
def value (r : FiniteRate) : ℚ := (r.numerator : ℚ) / (r.denominator : ℚ)

/-- The Agda module's first marginal. -/
def threePerHundred : FiniteRate := ⟨3, 100⟩

/-- The Agda module's second marginal. -/
def sevenPerHundred : FiniteRate := ⟨7, 100⟩

/-- The Agda module's second-order overlap. -/
def expectedIndependentOverlap : FiniteRate := multiplyRate threePerHundred sevenPerHundred

theorem expectedIndependentOverlap_eq : expectedIndependentOverlap = ⟨21, 10000⟩ := rfl

/-- `multiplyRate` computes the product of the values: the second-order rate
really is the independence product. -/
theorem value_multiplyRate (r s : FiniteRate) :
    value (multiplyRate r s) = value r * value s := by
  simp only [value, multiplyRate, Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

/-- **The second-order rate is strictly below both marginals.** -/
theorem overlap_lt_marginals :
    value expectedIndependentOverlap < value threePerHundred ∧
    value expectedIndependentOverlap < value sevenPerHundred := by
  constructor <;> · norm_num [value, expectedIndependentOverlap, multiplyRate,
                              threePerHundred, sevenPerHundred]

/-- The record is a presentation, not a value: two distinct `FiniteRate`s can
have the same rational value, so "the rate" is ambiguous until a presentation is
fixed. -/
theorem rate_value_not_injective : ¬ Function.Injective value := by
  intro h
  have : (⟨21, 10000⟩ : FiniteRate) = ⟨42, 20000⟩ := h (by norm_num [value])
  exact absurd this (by decide)

/-- The boundary flag's content: as a rate, the second-order overlap is neither
marginal, and is not `21` per hundred. -/
theorem twentyOne_not_first_order :
    value expectedIndependentOverlap ≠ value threePerHundred ∧
    value expectedIndependentOverlap ≠ value sevenPerHundred ∧
    value expectedIndependentOverlap ≠ value ⟨21, 100⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    norm_num [value, expectedIndependentOverlap, multiplyRate, threePerHundred,
              sevenPerHundred]

/-! ## A rounded overlap count: an *approximate* square with an explicit bound -/

open Integration.ApproximateIntertwiner in
/-- The integer count of second-order overlaps expected in a population of `n`,
at the module's own rate `21/10000`. -/
noncomputable def overlapCount (n : ℕ) : ℝ := ⌊(21 : ℝ) * n / 10000⌋

open Integration.ApproximateIntertwiner in
/-- **An approximate intertwiner with an explicit, checked bound.**  Adding one
member to the population increases the *rounded* expected overlap count by the
rate `21/10000` up to an error of at most one whole unit.  The square does not
commute exactly — rounding is genuinely lossy — and `1` is the honest bound. -/
theorem overlapCount_approx :
    IsApproxIntertwiner overlapCount (fun n => n + 1) (fun x => x + 21 / 10000) 1 := by
  intro n
  set a : ℝ := (21 : ℝ) * n / 10000 with ha
  have hstep : (21 : ℝ) * (n + 1 : ℕ) / 10000 = a + 21 / 10000 := by
    push_cast [ha]; ring
  have h1 : (⌊a + 21 / 10000⌋ : ℝ) ≤ a + 21 / 10000 := Int.floor_le _
  have h2 : a - 1 < (⌊a⌋ : ℝ) := Int.sub_one_lt_floor a
  have h3 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
  have h4 : a + 21 / 10000 - 1 < (⌊a + 21 / 10000⌋ : ℝ) := Int.sub_one_lt_floor _
  simp only [overlapCount, hstep, Real.dist_eq]
  rw [abs_le]
  constructor <;> [linarith; linarith]

end Integration.EducationGates

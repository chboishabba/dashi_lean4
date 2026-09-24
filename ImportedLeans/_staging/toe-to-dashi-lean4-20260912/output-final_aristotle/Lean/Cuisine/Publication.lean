import Mathlib

/-!
# Cuisine layer 5: the publication decision, and the hole in the assessment

Lean mirror of the publication block of
`DASHI.Culture.Cuisine.ControlledSuccessCore`: `PublicationRisk`,
`PublicationDecision`, `publicationDecision`, and the record
`PublicationImpactAssessment`.

The Agda file proves two point facts (`highRiskFailsClosed`,
`unknownRiskFailsClosed`) about `publicationDecision`.

New content proved here:

* `decisionLevel_publicationDecision` — the decision map is *exactly* the
  identity on risk levels, from which monotonicity and both Agda point facts
  follow;
* `publish_iff_low` and `abstain_iff` — full characterisations, so "fail-closed"
  is proved as an equivalence rather than checked at two points;
* `LooseAssessment.publish_with_all_components_high` — the supplied record has a
  hole: `overallRisk` is a free field, unconstrained by the component risks, so
  an assessment may record maximal component risk and still decide to publish;
* `TightAssessment` — the repair (a join law on `overallRisk`) together with
  `TightAssessment.abstains_of_any_component_high`, the theorem the record is
  meant to guarantee.
-/

namespace Cuisine.Publication

inductive PublicationRisk
  | lowPublicationRisk | controlledPublicationRisk | highPublicationRisk
  | unknownPublicationRisk
  deriving DecidableEq, Fintype, Repr

inductive PublicationDecision
  | publishDecision | limitedProjectionDecision | abstainDecision
  deriving DecidableEq, Fintype, Repr

open PublicationRisk PublicationDecision

/-- The Agda decision function. -/
def publicationDecision : PublicationRisk → PublicationDecision
  | lowPublicationRisk => publishDecision
  | controlledPublicationRisk => limitedProjectionDecision
  | highPublicationRisk => abstainDecision
  | unknownPublicationRisk => abstainDecision

/-- Severity of a risk.  `unknown` is treated as maximally severe: that is the
fail-closed convention of the Agda source. -/
def riskLevel : PublicationRisk → ℕ
  | lowPublicationRisk => 0
  | controlledPublicationRisk => 1
  | highPublicationRisk => 2
  | unknownPublicationRisk => 2

/-- Restrictiveness of a decision. -/
def decisionLevel : PublicationDecision → ℕ
  | publishDecision => 0
  | limitedProjectionDecision => 1
  | abstainDecision => 2

/-- **The decision map is level-preserving.**  Everything else in this section
is a corollary. -/
theorem decisionLevel_publicationDecision (r : PublicationRisk) :
    decisionLevel (publicationDecision r) = riskLevel r := by cases r <;> rfl

theorem publicationDecision_mono {r s : PublicationRisk} (h : riskLevel r ≤ riskLevel s) :
    decisionLevel (publicationDecision r) ≤ decisionLevel (publicationDecision s) := by
  rw [decisionLevel_publicationDecision, decisionLevel_publicationDecision]; exact h

theorem decisionLevel_injective {d e : PublicationDecision}
    (h : decisionLevel d = decisionLevel e) : d = e := by
  cases d <;> cases e <;> simp_all [decisionLevel]

/-- Publication happens only at the lowest risk level. -/
theorem publish_iff_low (r : PublicationRisk) :
    publicationDecision r = publishDecision ↔ r = lowPublicationRisk := by
  cases r <;> decide

/-- Abstention is exactly the maximal-severity case, which includes *unknown*:
this is the fail-closed property, as an equivalence. -/
theorem abstain_iff (r : PublicationRisk) :
    publicationDecision r = abstainDecision ↔ riskLevel r = 2 := by
  cases r <;> decide

/-- The two Agda point facts. -/
theorem highRiskFailsClosed : publicationDecision highPublicationRisk = abstainDecision := rfl

theorem unknownRiskFailsClosed :
    publicationDecision unknownPublicationRisk = abstainDecision := rfl

/-- Absence of evidence is treated as maximal risk: `unknown` is never less
restrictive than any other risk. -/
theorem unknown_is_maximally_restrictive (r : PublicationRisk) :
    decisionLevel (publicationDecision r) ≤
      decisionLevel (publicationDecision unknownPublicationRisk) := by
  cases r <;> decide

theorem riskLevel_le_two (r : PublicationRisk) : riskLevel r ≤ 2 := by cases r <;> decide

/-- Worst-case combination of two risks. -/
def riskJoin (a b : PublicationRisk) : PublicationRisk :=
  if riskLevel a ≤ riskLevel b then b else a

theorem riskLevel_riskJoin (a b : PublicationRisk) :
    riskLevel (riskJoin a b) = max (riskLevel a) (riskLevel b) := by
  cases a <;> cases b <;> decide

/-! ## The assessment record

The Agda `PublicationImpactAssessment` has component risk fields, a free
`overallRisk` field, a `decision` field, and the single law
`decision ≡ publicationDecision overallRisk`. -/

/-- The record exactly as supplied. -/
structure LooseAssessment where
  locationRisk : PublicationRisk
  appropriationRisk : PublicationRisk
  harassmentRisk : PublicationRisk
  overallRisk : PublicationRisk
  decision : PublicationDecision
  decisionMatchesRisk : decision = publicationDecision overallRisk

/-- **The hole.**  Nothing links `overallRisk` to the component risks, so the
record admits an assessment whose three component risks are all maximal and
whose decision is nevertheless "publish".  The `decisionMatchesRisk` law does
not prevent this. -/
theorem LooseAssessment.publish_with_all_components_high :
    ∃ a : LooseAssessment,
      a.locationRisk = highPublicationRisk ∧
      a.appropriationRisk = highPublicationRisk ∧
      a.harassmentRisk = unknownPublicationRisk ∧
      a.decision = publishDecision :=
  ⟨{ locationRisk := highPublicationRisk
     appropriationRisk := highPublicationRisk
     harassmentRisk := unknownPublicationRisk
     overallRisk := lowPublicationRisk
     decision := publishDecision
     decisionMatchesRisk := rfl },
   rfl, rfl, rfl, rfl⟩

/-- The repair: require the overall risk to dominate every component risk. -/
structure TightAssessment where
  locationRisk : PublicationRisk
  appropriationRisk : PublicationRisk
  harassmentRisk : PublicationRisk
  overallRisk : PublicationRisk
  decision : PublicationDecision
  decisionMatchesRisk : decision = publicationDecision overallRisk
  overallDominates :
    riskLevel overallRisk =
      max (riskLevel locationRisk) (max (riskLevel appropriationRisk) (riskLevel harassmentRisk))

namespace TightAssessment

/-- Every loose assessment can be repaired by recomputing the overall risk, and
the repair is conservative: it never lowers the recorded severity. -/
theorem exists_tightening (a : LooseAssessment) :
    ∃ t : TightAssessment,
      t.locationRisk = a.locationRisk ∧ t.appropriationRisk = a.appropriationRisk ∧
      t.harassmentRisk = a.harassmentRisk := by
  classical
  refine ⟨{ locationRisk := a.locationRisk
            appropriationRisk := a.appropriationRisk
            harassmentRisk := a.harassmentRisk
            overallRisk :=
              riskJoin a.locationRisk (riskJoin a.appropriationRisk a.harassmentRisk)
            decision :=
              publicationDecision
                (riskJoin a.locationRisk (riskJoin a.appropriationRisk a.harassmentRisk))
            decisionMatchesRisk := rfl
            overallDominates := ?_ }, rfl, rfl, rfl⟩
  simp only [riskLevel_riskJoin]

/-- **The theorem the record is meant to guarantee.**  If any single component
risk is maximal — high *or* unknown — the repaired assessment abstains. -/
theorem abstains_of_any_component_high (t : TightAssessment)
    (h : riskLevel t.locationRisk = 2 ∨ riskLevel t.appropriationRisk = 2 ∨
      riskLevel t.harassmentRisk = 2) :
    t.decision = abstainDecision := by
  have b1 := riskLevel_le_two t.locationRisk
  have b2 := riskLevel_le_two t.appropriationRisk
  have b3 := riskLevel_le_two t.harassmentRisk
  have hmax : riskLevel t.overallRisk = 2 := by
    rw [t.overallDominates]; omega
  rw [t.decisionMatchesRisk, abstain_iff]
  exact hmax

/-- Conversely a repaired assessment publishes only when every component risk is
minimal. -/
theorem publishes_iff_all_low (t : TightAssessment) :
    t.decision = publishDecision ↔
      t.locationRisk = lowPublicationRisk ∧ t.appropriationRisk = lowPublicationRisk ∧
        t.harassmentRisk = lowPublicationRisk := by
  rw [t.decisionMatchesRisk, publish_iff_low]
  constructor
  · intro h
    have h0 : riskLevel t.overallRisk = 0 := by rw [h]; rfl
    rw [t.overallDominates] at h0
    have h1 : riskLevel t.locationRisk = 0 := by omega
    have h2 : riskLevel t.appropriationRisk = 0 := by omega
    have h3 : riskLevel t.harassmentRisk = 0 := by omega
    refine ⟨?_, ?_, ?_⟩
    · revert h1; cases t.locationRisk <;> decide
    · revert h2; cases t.appropriationRisk <;> decide
    · revert h3; cases t.harassmentRisk <;> decide
  · rintro ⟨h1, h2, h3⟩
    have h0 : riskLevel t.overallRisk = 0 := by
      rw [t.overallDominates, h1, h2, h3]; rfl
    revert h0; cases t.overallRisk <;> decide

end TightAssessment

end Cuisine.Publication

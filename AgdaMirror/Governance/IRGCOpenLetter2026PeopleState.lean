import AgdaMirror.Governance.IRGCOpenLetter2026

namespace AgdaMirror.Governance.IRGCOpenLetter2026.PeopleState

inductive AmericanSituatedRole
  | ordinaryPeople | governingElite
  deriving DecidableEq, Repr

inductive NationalSurface
  | american
  deriving DecidableEq, Repr

inductive SourceLocalTarget
  | addressedAsPotentialPartner | targetedAsPoliticalAdversary
  deriving DecidableEq, Repr

def nationalProjection (_ : AmericanSituatedRole) : NationalSurface := .american

def sourceLocalTarget : AmericanSituatedRole → SourceLocalTarget
  | .ordinaryPeople => .addressedAsPotentialPartner
  | .governingElite => .targetedAsPoliticalAdversary

def FactorsThrough {State Flat Outcome : Type}
    (flatten : State → Flat) (outcome : State → Outcome) : Prop :=
  ∃ f : Flat → Outcome, ∀ s, outcome s = f (flatten s)

theorem american_identity_cannot_determine_source_target :
    ¬ FactorsThrough nationalProjection sourceLocalTarget := by
  intro h
  obtain ⟨f, hf⟩ := h
  have left := hf .ordinaryPeople
  have right := hf .governingElite
  have contradiction :
      SourceLocalTarget.addressedAsPotentialPartner =
        SourceLocalTarget.targetedAsPoliticalAdversary := by
    calc
      SourceLocalTarget.addressedAsPotentialPartner =
          f (nationalProjection .ordinaryPeople) := left
      _ = f (nationalProjection .governingElite) := by rfl
      _ = SourceLocalTarget.targetedAsPoliticalAdversary := right.symm
  cases contradiction

theorem any_nationality_rechart_still_cannot_determine_target
    {Chart : Type} (chart : NationalSurface → Chart) :
    ¬ FactorsThrough (fun r => chart (nationalProjection r)) sourceLocalTarget := by
  intro h
  obtain ⟨f, hf⟩ := h
  apply american_identity_cannot_determine_source_target
  exact ⟨fun n => f (chart n), hf⟩

end AgdaMirror.Governance.IRGCOpenLetter2026.PeopleState

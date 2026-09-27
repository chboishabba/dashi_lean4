import RequestProject.QuantumMereologySelection

/-!
# Finite selection regressions for quantum mereology

These are DASHI-owned countermodels for the generic selection interface. They
are not claims about the physical TPS space and are not attributed to the
external papers.
-/

namespace QuantumMereology

inductive Candidate2 where
  | left
  | right
deriving Repr, DecidableEq

def twoCandidateProblem : PreferredTPSSelectionProblem toyWorld where
  Candidate := Candidate2
  realizes := fun _ => toyTPS
  Admissible := fun _ => True
  EntanglementGrowthScore := Unit
  InternalSpreadingScore := Unit
  entanglementGrowth := fun _ => ()
  internalSpreading := fun _ => ()
  NoWorse := fun _ _ => True

theorem leftOptimal :
    twoCandidateProblem.Optimal Candidate2.left := by
  constructor
  · trivial
  · intro _ _
    trivial

theorem rightOptimal :
    twoCandidateProblem.Optimal Candidate2.right := by
  constructor
  · trivial
  · intro _ _
    trivial

def leftSelection :
    PreferredTPSSelectionReceipt twoCandidateProblem where
  selected := Candidate2.left
  selectedOptimal := leftOptimal

def rightSelection :
    PreferredTPSSelectionReceipt twoCandidateProblem where
  selected := Candidate2.right
  selectedOptimal := rightOptimal

theorem optimality_alone_does_not_force_identity_uniqueness
    (authority : UniquePreferredTPSAuthority twoCandidateProblem)
    (sameReflectsEquality :
      ∀ x y, authority.SameTPS x y → x = y) :
    False := by
  have hsame :=
    twoOptimalSelectionsAgreeGivenUniqueness
      authority leftSelection rightSelection
  have hEq : Candidate2.left = Candidate2.right :=
    sameReflectsEquality _ _ hsame
  cases hEq

def candidateIdentityConsumer :
    CriterionConsumerSurface twoCandidateProblem where
  Surface := Unit
  Outcome := Candidate2
  observeCriterion := fun _ => ()
  consumer := id

def criterionCollision :
    CriterionCollision candidateIdentityConsumer where
  left := Candidate2.left
  right := Candidate2.right
  sameCriterion := rfl
  differentOutcome := by
    intro h
    cases h

theorem criterion_observer_is_insufficient_for_candidate_identity :
    ¬ candidateIdentityConsumer.Sufficient :=
  criterionCollisionBlocksConsumerSufficiency criterionCollision

end QuantumMereology

import RequestProject.QuantumMereology

/-!
# Preferred-TPS selection and criterion sufficiency

Attribution boundary:
* Carroll--Singh own the external scientific proposal that quasiclassical
  factorisations can be searched by minimizing a combination of entanglement
  growth and internal spreading.
* DASHI owns the typed reconstruction and the generic selection/sufficiency
  theorems below.
* No source paper is attributed a local existence or uniqueness theorem.
-/

namespace QuantumMereology

structure PreferredTPSSelectionProblem (W : BareQuantumWorld) where
  Candidate : Type
  realizes : Candidate → TensorProductStructure W
  Admissible : Candidate → Prop

  EntanglementGrowthScore : Type
  InternalSpreadingScore : Type

  entanglementGrowth : Candidate → EntanglementGrowthScore
  internalSpreading : Candidate → InternalSpreadingScore

  /-- Application-supplied comparison relation. The framework does not choose
  a scalarisation implicitly. -/
  NoWorse : Candidate → Candidate → Prop

def PreferredTPSSelectionProblem.Optimal
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W)
    (candidate : P.Candidate) : Prop :=
  P.Admissible candidate ∧
    ∀ other, P.Admissible other → P.NoWorse candidate other

structure PreferredTPSSelectionReceipt
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) where
  selected : P.Candidate
  selectedOptimal : P.Optimal selected

structure UniquePreferredTPSAuthority
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) where
  SameTPS : P.Candidate → P.Candidate → Prop
  optimalCandidatesAgree :
    ∀ left right, P.Optimal left → P.Optimal right → SameTPS left right

theorem twoOptimalSelectionsAgreeGivenUniqueness
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (authority : UniquePreferredTPSAuthority P)
    (left right : PreferredTPSSelectionReceipt P) :
    authority.SameTPS left.selected right.selected :=
  authority.optimalCandidatesAgree
    left.selected right.selected
    left.selectedOptimal right.selectedOptimal

/-! ## Carroll--Singh source-objective realization

The paper owns the external scientific claim that the preferred-factorisation
search minimizes a combination of entanglement growth and internal spreading.
The application supplies the combined objective carrier/order and proves that
it matches the generic NoWorse relation. DASHI owns only the transport theorem.
-/

structure CarrollSinghObjectiveRealization
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) where
  CombinedObjective : Type
  combine :
    P.EntanglementGrowthScore →
    P.InternalSpreadingScore →
    CombinedObjective
  ObjectiveNoWorse : CombinedObjective → CombinedObjective → Prop
  noWorseToCombined :
    ∀ left right,
      P.NoWorse left right →
      ObjectiveNoWorse
        (combine (P.entanglementGrowth left) (P.internalSpreading left))
        (combine (P.entanglementGrowth right) (P.internalSpreading right))
  combinedToNoWorse :
    ∀ left right,
      ObjectiveNoWorse
        (combine (P.entanglementGrowth left) (P.internalSpreading left))
        (combine (P.entanglementGrowth right) (P.internalSpreading right)) →
      P.NoWorse left right

theorem selectionReceiptMinimizesRealizedCombinedObjective
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (objective : CarrollSinghObjectiveRealization P)
    (receipt : PreferredTPSSelectionReceipt P)
    (other : P.Candidate)
    (otherAdmissible : P.Admissible other) :
    objective.ObjectiveNoWorse
      (objective.combine
        (P.entanglementGrowth receipt.selected)
        (P.internalSpreading receipt.selected))
      (objective.combine
        (P.entanglementGrowth other)
        (P.internalSpreading other)) :=
  objective.noWorseToCombined
    receipt.selected other
    (receipt.selectedOptimal.2 other otherAdmissible)

/-! ## Criterion observer and downstream consumer sufficiency -/

structure CriterionConsumerSurface
    {W : BareQuantumWorld}
    (P : PreferredTPSSelectionProblem W) where
  Surface : Type
  Outcome : Type
  observeCriterion : P.Candidate → Surface
  consumer : P.Candidate → Outcome

def CriterionConsumerSurface.Sufficient
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : CriterionConsumerSurface P) : Prop :=
  ∀ left right,
    S.observeCriterion left = S.observeCriterion right →
    S.consumer left = S.consumer right

structure CriterionCollision
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : CriterionConsumerSurface P) where
  left right : P.Candidate
  sameCriterion :
    S.observeCriterion left = S.observeCriterion right
  differentOutcome :
    S.consumer left ≠ S.consumer right

theorem criterionCollisionBlocksConsumerSufficiency
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P}
    (collision : CriterionCollision S) :
    ¬ S.Sufficient := by
  intro sufficient
  exact collision.differentOutcome
    (sufficient collision.left collision.right collision.sameCriterion)

structure CriterionFactorisation
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : CriterionConsumerSurface P) where
  factor : S.Surface → S.Outcome
  factorizes :
    ∀ candidate,
      S.consumer candidate = factor (S.observeCriterion candidate)

theorem criterionFactorisationImpliesSufficient
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P}
    (factorisation : CriterionFactorisation S) :
    S.Sufficient := by
  intro left right h
  calc
    S.consumer left = factorisation.factor (S.observeCriterion left) :=
      factorisation.factorizes left
    _ = factorisation.factor (S.observeCriterion right) := by rw [h]
    _ = S.consumer right := (factorisation.factorizes right).symm

theorem criterionCollisionBlocksFactorisation
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P}
    (collision : CriterionCollision S) :
    ¬ Nonempty (CriterionFactorisation S) := by
  rintro ⟨factorisation⟩
  exact criterionCollisionBlocksConsumerSufficiency collision
    (criterionFactorisationImpliesSufficient factorisation)


structure CriterionRefinementRepair
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    (S : CriterionConsumerSurface P)
    (Refinement : Type)
    (refine : P.Candidate → Refinement) where
  repaired :
    ∀ left right,
      (S.observeCriterion left, refine left) =
        (S.observeCriterion right, refine right) →
      S.consumer left = S.consumer right

theorem criterionCollisionForcesSeparationInEveryRepair
    {W : BareQuantumWorld}
    {P : PreferredTPSSelectionProblem W}
    {S : CriterionConsumerSurface P}
    {Refinement : Type}
    {refine : P.Candidate → Refinement}
    (collision : CriterionCollision S)
    (repair : CriterionRefinementRepair S Refinement refine) :
    refine collision.left ≠ refine collision.right := by
  intro sameRefinement
  apply collision.differentOutcome
  apply repair.repaired collision.left collision.right
  exact Prod.ext collision.sameCriterion sameRefinement

structure PreferredTPSSelectionBoundary where
  sourceObjectiveCreatesLocalMinimizer : Bool := false
  oneOptimalReceiptCreatesUniqueness : Bool := false
  scalarizationChosenByDASHIWithoutApplication : Bool := false
  criterionAdequacyIsConsumerRelative : Bool := true
  criterionCollisionCreatesRefinementObligation : Bool := true
deriving Repr, DecidableEq

def canonicalPreferredTPSSelectionBoundary : PreferredTPSSelectionBoundary := {}

theorem source_objective_does_not_create_local_minimizer :
    canonicalPreferredTPSSelectionBoundary.sourceObjectiveCreatesLocalMinimizer = false := rfl

theorem one_optimal_receipt_does_not_create_uniqueness :
    canonicalPreferredTPSSelectionBoundary.oneOptimalReceiptCreatesUniqueness = false := rfl

theorem scalarisation_not_silently_chosen :
    canonicalPreferredTPSSelectionBoundary.scalarizationChosenByDASHIWithoutApplication = false := rfl

end QuantumMereology

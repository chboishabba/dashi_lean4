import Mathlib

/-!
# Projection-choice independence for a selected constituent action

Structural Lean mirror of
`Trialectic369Selected3BProjectionChoiceIndependenceExact.agda`.

For any inclusion i : C → V, invariant full-grade action A, and two
left inverses p,q of i, both projections agree on A (i c). Thus a
selected-action recognition equation cannot depend on which valid
retraction was chosen.

This is an abstract same-action lemma. It does not construct a Monster
representation, linear projection, or source-selected 3B action.
-/

namespace Integration.Selected3BProjectionChoice

variable {C V G : Type*}
variable (include : C → V) (fullAct : G → V → V)
variable (constituentAct : G → C → C)

/-- The already-owned representation-theoretic invariance condition. -/
def ConstituentInvariant : Prop :=
  ∀ (g : G) (c : C),
    fullAct g (include c) = include (constituentAct g c)

/-- A set-level left inverse. A genuine linear source retraction must also
provide the source's linear structure; this wrapper does not supply it. -/
structure Retraction where
  project : V → C
  leftInverse : ∀ c : C, project (include c) = c

theorem projected_full_recovers_constituent
    (hInv : ConstituentInvariant include fullAct constituentAct)
    (r : Retraction include)
    (g : G) (c : C) :
    r.project (fullAct g (include c)) = constituentAct g c := by
  rw [hInv g c, r.leftInverse]

theorem projected_action_independent_of_retraction
    (hInv : ConstituentInvariant include fullAct constituentAct)
    (first second : Retraction include)
    (g : G) (c : C) :
    first.project (fullAct g (include c)) =
      second.project (fullAct g (include c)) := by
  rw [projected_full_recovers_constituent include fullAct constituentAct hInv first,
      projected_full_recovers_constituent include fullAct constituentAct hInv second]

/-- The projected equation for an arbitrary selected action. -/
def ProjectedRecognition (selected : G → C → C)
    (r : Retraction include) : Prop :=
  ∀ (g : G) (c : C),
    selected g c = r.project (fullAct g (include c))

/-- The intrinsic same-action statement is independent of projection. -/
def IntrinsicRecognition (selected : G → C → C) : Prop :=
  ∀ (g : G) (c : C), selected g c = constituentAct g c

theorem projected_recognition_iff_intrinsic
    (hInv : ConstituentInvariant include fullAct constituentAct)
    (selected : G → C → C) (r : Retraction include) :
    ProjectedRecognition include fullAct selected r ↔
      IntrinsicRecognition constituentAct selected := by
  constructor
  · intro h g c
    rw [h g c, projected_full_recovers_constituent include fullAct constituentAct hInv r]
  · intro h g c
    rw [h g c, projected_full_recovers_constituent include fullAct constituentAct hInv r]

theorem projected_recognition_independent_of_retraction
    (hInv : ConstituentInvariant include fullAct constituentAct)
    (selected : G → C → C)
    (first second : Retraction include) :
    ProjectedRecognition include fullAct selected first ↔
      ProjectedRecognition include fullAct selected second := by
  rw [projected_recognition_iff_intrinsic include fullAct constituentAct hInv selected first,
      projected_recognition_iff_intrinsic include fullAct constituentAct hInv selected second]

structure Boundary where
  actionImageInclusionRequired : Bool
  projectionChoiceIndependence : Bool
  intrinsicSameActionCriterion : Bool
  sourceLinearRetractionConstructed : Bool
  monsterSelectedActionEstablished : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actionImageInclusionRequired := true
  projectionChoiceIndependence := true
  intrinsicSameActionCriterion := true
  sourceLinearRetractionConstructed := false
  monsterSelectedActionEstablished := false

end Integration.Selected3BProjectionChoice

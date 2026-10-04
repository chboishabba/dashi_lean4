import Integration.TrialecticIncomingFrickeSeparation
import Integration.MoonshineNeutralCuspRelationCrossPollination
import Mathlib

/-!
# Finite multiplicity basis chart vs linear multiplicity representation

Generic Lean WrongType mirror of the Agda Monster 3B audit.

The finite coordinate surface
  Completion10 × NinePoint
has 90 states and is a valid basis/index chart.

A genuine multiplicity representation is a vector-space carrier with a linear
group action. These are different types of object. A Fin 90 permutation action
is available only after an explicit basis-preservation specialisation.

This module deliberately does not import or manufacture the Agda-side
Barraclough-Wilson 12+78 source theorem.
-/

namespace Integration.TrialecticFiniteBasisLinearWrongType

open Integration.TrialecticIncomingFrickeSeparation
open Integration.MoonshineNeutralCuspRelationCrossPollination

abbrev FiniteMultiplicityChart90 :=
  Completion10 × NinePoint

theorem finite_multiplicity_chart_count :
    Fintype.card FiniteMultiplicityChart90 = 90 := by
  native_decide

structure LinearMultiplicityTarget where
  Scalar : Type
  [scalarField : Field Scalar]
  Carrier : Type
  [carrierAdd : AddCommGroup Carrier]
  [carrierModule : Module Scalar Carrier]
  Group : Type
  act : Group → Carrier →ₗ[Scalar] Carrier

attribute [instance] LinearMultiplicityTarget.scalarField
attribute [instance] LinearMultiplicityTarget.carrierAdd
attribute [instance] LinearMultiplicityTarget.carrierModule

structure FiniteBasisSpecialisation (linear : LinearMultiplicityTarget) where
  basisVector : Fin 90 → linear.Carrier
  basisPermutation : linear.Group → Fin 90 → Fin 90
  actionPreservesChosenBasis :
    ∀ g i,
      linear.act g (basisVector i) =
        basisVector (basisPermutation g i)

inductive FiniteNinetyLabelsCreateLinearRepresentation : Prop
inductive LinearRepresentationCreatesBasisPermutation : Prop
inductive EqualCardinalityCreatesLinearEquivalence : Prop

theorem finite_labels_do_not_create_linear_representation :
    ¬ FiniteNinetyLabelsCreateLinearRepresentation := by
  intro h
  cases h

theorem linear_representation_does_not_create_basis_permutation :
    ¬ LinearRepresentationCreatesBasisPermutation := by
  intro h
  cases h

theorem equal_cardinality_does_not_create_linear_equivalence :
    ¬ EqualCardinalityCreatesLinearEquivalence := by
  intro h
  cases h

/-! Optional finite-coordinate consumers may take a basis receipt, but the
receipt is a separate input. -/

def basisIndexAct
    (linear : LinearMultiplicityTarget)
    (receipt : FiniteBasisSpecialisation linear) :
    linear.Group → Fin 90 → Fin 90 :=
  receipt.basisPermutation

theorem basis_index_action_agrees_with_linear_action
    (linear : LinearMultiplicityTarget)
    (receipt : FiniteBasisSpecialisation linear)
    (g : linear.Group) (i : Fin 90) :
    linear.act g (receipt.basisVector i) =
      receipt.basisVector (basisIndexAct linear receipt g i) :=
  receipt.actionPreservesChosenBasis g i

structure Boundary where
  finiteNinetyCoordinateChartOwned : Bool
  finiteChartCount90 : Bool
  linearMultiplicityTypeSeparated : Bool
  explicitBasisSpecialisationRequired : Bool
  finiteLabelsCreateLinearRepresentation : Bool
  linearActionCreatesBasisPermutation : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteNinetyCoordinateChartOwned := true
  finiteChartCount90 := true
  linearMultiplicityTypeSeparated := true
  explicitBasisSpecialisationRequired := true
  finiteLabelsCreateLinearRepresentation := false
  linearActionCreatesBasisPermutation := false

end Integration.TrialecticFiniteBasisLinearWrongType

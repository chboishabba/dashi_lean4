namespace DASHITOE

inductive ValidationGrade where
  | conjecturalStructural
  | sharedCarrier
  | representationIntertwiner
  | dynamicsIntertwiner
  | sameActionHamiltonian
  | stressObservablePreserved
  | calibratedSamePhysicalObject
  | heldOutEmpiricalPrediction
  | independentReplication
  deriving Repr, DecidableEq

open ValidationGrade

def canonicalValidationGrades : List ValidationGrade :=
  [conjecturalStructural, sharedCarrier, representationIntertwiner,
   dynamicsIntertwiner, sameActionHamiltonian, stressObservablePreserved,
   calibratedSamePhysicalObject, heldOutEmpiricalPrediction,
   independentReplication]

inductive RealizationKind where
  | literalEquality
  | equivalenceIsomorphism
  | quotientFactor
  | restrictionInclusion
  | representationIntertwiner
  | sharedCharacterOnly
  | conjecturalPhysicalRealization
  | refutedNonDescent
  deriving Repr, DecidableEq

inductive RealizationObligation where
  | carrierAgreement
  | representationActionAgreement
  | dynamicsEquivariance
  | actionHamiltonianAgreement
  | metricVariationCommutes
  | stressObservableAgreement
  | scaleCalibrationAgreement
  | empiricalSameObjectAttachment
  | heldOutPredictionReceipt
  | independentReplicationReceipt
  | nonDescentWitness
  deriving Repr, DecidableEq

def composeGrade : ValidationGrade → ValidationGrade → ValidationGrade
  | conjecturalStructural, _ => conjecturalStructural
  | _, conjecturalStructural => conjecturalStructural
  | sharedCarrier, _ => sharedCarrier
  | _, sharedCarrier => sharedCarrier
  | representationIntertwiner, _ => representationIntertwiner
  | _, representationIntertwiner => representationIntertwiner
  | dynamicsIntertwiner, _ => dynamicsIntertwiner
  | _, dynamicsIntertwiner => dynamicsIntertwiner
  | sameActionHamiltonian, _ => sameActionHamiltonian
  | _, sameActionHamiltonian => sameActionHamiltonian
  | stressObservablePreserved, _ => stressObservablePreserved
  | _, stressObservablePreserved => stressObservablePreserved
  | calibratedSamePhysicalObject, _ => calibratedSamePhysicalObject
  | _, calibratedSamePhysicalObject => calibratedSamePhysicalObject
  | heldOutEmpiricalPrediction, _ => heldOutEmpiricalPrediction
  | _, heldOutEmpiricalPrediction => heldOutEmpiricalPrediction
  | independentReplication, independentReplication => independentReplication

structure SectorRealization (α β : Type) where
  realize : α → β
  kind : RealizationKind
  grade : ValidationGrade
  unpaid : List RealizationObligation
  reading : String

structure DASHIUniversalTheory where
  State : Type
  Refinement369 : Type
  OrientationC3 : Type
  Symmetry : Type
  Dynamics : Type
  Action : Type
  Observer : Type
  Scale : Type
  CausalStructure : Type
  refinementOf : State → Refinement369
  orientationOf : State → OrientationC3
  evolve : Dynamics → State → State
  actionOf : State → Action
  observe : Observer → State → State
  scaleOf : State → Scale
  causalOf : State → CausalStructure

end DASHITOE

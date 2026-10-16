import Integration.DASHITOE.Everything

open DASHITOE

example : canonicalValidationGrades =
    [ValidationGrade.conjecturalStructural,
     .sharedCarrier,
     .representationIntertwiner,
     .dynamicsIntertwiner,
     .sameActionHamiltonian,
     .stressObservablePreserved,
     .calibratedSamePhysicalObject,
     .heldOutEmpiricalPrediction,
     .independentReplication] := rfl

example : composeGrade .sharedCarrier .representationIntertwiner = .sharedCarrier := rfl
example : monsterPhysicalGrade = .conjecturalStructural := rfl
example : arithmeticCMGrade = .representationIntertwiner := rfl
example : currentTOEStatus = .candidateConstructed := rfl
example : currentPhysicalClosureStatus = .physicalClosureOpen := rfl

namespace AgdaMirror.Governance.CheRevolutionaryAuthorityCriteria

inductive AuthorityCoordinate
  | centralisedEconomicPlanning
  | administrativeControl
  | revolutionaryTribunalResponsibility
  | capitalPunishmentRole
  | singlePartyStateStructure
  | oppositionPluralismConstraint
  deriving DecidableEq, Repr

structure CoordinateReceipt where
  coordinate : AuthorityCoordinate
  actorOrStateRef : String
  sourceRef : String
  reading : String
  paid : Bool := true
  actorAuthoredLaterStateStructure : Bool := false

def cheCentralPlanning : CoordinateReceipt :=
  ⟨.centralisedEconomicPlanning,
   "Ernesto Che Guevara",
   "Yaffe, Third World Quarterly 2023",
   "Guevara treated centralised planning as a defining category of socialist construction."⟩

def cheAdministrativeControl : CoordinateReceipt :=
  ⟨.administrativeControl,
   "Ernesto Che Guevara",
   "Yaffe, Globalizations 2022",
   "The Budgetary Finance System used administrative control and moral incentives."⟩

def laterCubanPartyStructure : CoordinateReceipt :=
  ⟨.singlePartyStateStructure,
   "Republic of Cuba, later constitutional order",
   "Cuba Constitution 2019 Article 5",
   "The Communist Party is identified as unique and the superior driving force of society and state."⟩

structure ClassificationBoundary where
  coordinatesAreFactsNotVerdicts : Bool := true
  laterCubanStructureNotAutomaticallyCheAuthorship : Bool := true
  revolutionaryJustificationDoesNotEraseCoerciveStructure : Bool := true
  coerciveStructureDoesNotDetermineMotive : Bool := true
  contextDoesNotEraseAction : Bool := true
  classificationRequiresExplicitRule : Bool := true

def canonicalBoundary : ClassificationBoundary := {}

theorem later_state_not_personal_doctrine :
    laterCubanPartyStructure.actorAuthoredLaterStateStructure = false := by
  decide

end AgdaMirror.Governance.CheRevolutionaryAuthorityCriteria

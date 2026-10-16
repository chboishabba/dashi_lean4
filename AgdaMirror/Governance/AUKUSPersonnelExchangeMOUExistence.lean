namespace AgdaMirror.Governance.AUKUSPersonnelExchangeMOUExistence

structure MOUExistenceReceipt where
  officialSourceRef : String
  bilateralAustraliaUSMOUExists : Bool := true
  personnelExchangePurposePaid : Bool := true
  operativeDirectionClausesPublished : Bool := false
  thirdPartyHostilityRulesPublished : Bool := false
  exactIRISEpisodeTaskPaid : Bool := false


def canonicalMOUExistence : MOUExistenceReceipt :=
  ⟨"AUKUS Defence Ministers Joint Statement 2024 + Australian Submarine Agency Annual Report 2023-24"⟩

structure RemainingMOUResidual where
  residualRef : String
  alreadyPaid : String
  requiredObject : String
  existenceMustNotBeReacquired : Bool := true


def operativeMOUResidual : RemainingMOUResidual :=
  ⟨"residual:aukus:personnel-exchange-mou-operative-content",
   "primary official existence + personnel-exchange purpose",
   "actual Australia-US personnel-exchange MOU text and operative annexes/clauses relevant to direction authority, command and third-party hostilities"⟩

theorem existence_is_not_operative_content :
    canonicalMOUExistence.bilateralAustraliaUSMOUExists = true ∧
    canonicalMOUExistence.operativeDirectionClausesPublished = false ∧
    canonicalMOUExistence.thirdPartyHostilityRulesPublished = false ∧
    canonicalMOUExistence.exactIRISEpisodeTaskPaid = false := by
  decide

end AgdaMirror.Governance.AUKUSPersonnelExchangeMOUExistence

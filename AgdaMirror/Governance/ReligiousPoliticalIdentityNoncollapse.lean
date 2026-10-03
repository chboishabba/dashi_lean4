/-!
Religious / peoplehood / political-ideology / state noncollapse mirror.

This is a type boundary, not a classifier for concrete speech.  In particular,
Judaism, Jewish identity/peoplehood, Zionism, the State of Israel, an Israeli
government, particular Israeli policy and antisemitism are not definitionally
interchangeable categories.
-/

namespace AgdaMirror.Governance.ReligiousPoliticalIdentityNoncollapse

inductive Layer
  | judaismReligiousTradition
  | jewishPeoplehoodIdentity
  | jewishPoliticalPosition
  | zionistPoliticalIdeology
  | antiZionistPoliticalPosition
  | stateOfIsraelInstitution
  | israeliGovernmentInstitution
  | israeliPolicyPosition
  | antisemitismHateCategory
  deriving DecidableEq, Repr

inductive ContextualSpeechRisk
  | politicalCriticism | ambiguousProxyUse | antiJewishHateEvidence
  deriving DecidableEq, Repr

structure ContextualClassificationReceipt where
  risk : ContextualSpeechRisk
  utteranceReceipt : String
  targetReceipt : String
  surroundingContextReceipt : String
  politicalCriticismProtectedAsDistinctCategory : Bool := true
  hateClassificationRequiresContextualEvidence : Bool := true
  lexicalTermAloneClosesClassification : Bool := false

inductive JewishIdentityImpliesZionism : Prop
inductive ZionismImpliesReligiousJudaism : Prop
inductive StateOfIsraelEqualsJudaism : Prop
inductive IsraeliGovernmentRepresentsAllJewishPeople : Prop
inductive CriticismOfIsraelIsDefinitionallyAntisemitic : Prop
inductive AntiZionismIsDefinitionallyAntisemitic : Prop

theorem jewish_identity_does_not_definitionally_imply_zionism :
    ¬ JewishIdentityImpliesZionism := by intro h; cases h

theorem zionism_does_not_definitionally_imply_religious_judaism :
    ¬ ZionismImpliesReligiousJudaism := by intro h; cases h

theorem state_of_israel_does_not_definitionally_equal_judaism :
    ¬ StateOfIsraelEqualsJudaism := by intro h; cases h

theorem israeli_government_does_not_definitionally_represent_all_jewish_people :
    ¬ IsraeliGovernmentRepresentsAllJewishPeople := by intro h; cases h

theorem criticism_of_israel_is_not_definitionally_antisemitic :
    ¬ CriticismOfIsraelIsDefinitionallyAntisemitic := by intro h; cases h

theorem anti_zionism_is_not_definitionally_antisemitic :
    ¬ AntiZionismIsDefinitionallyAntisemitic := by intro h; cases h

end AgdaMirror.Governance.ReligiousPoliticalIdentityNoncollapse

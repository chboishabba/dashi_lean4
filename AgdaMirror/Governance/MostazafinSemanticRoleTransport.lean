namespace AgdaMirror.Governance.MostazafinSemanticRoleTransport

inductive MostazafinCarrier
  | quranicOppressedCarrier
  | shariatiRevolutionaryCarrier
  | khomeiniStateIdeologyCarrier
  | foundationCarrier
  | basijCarrier
  deriving DecidableEq, Repr

inductive RelationalRole
  | oppressedSubjectRole
  | revolutionaryConstituencyRole
  | claimedBeneficiaryRole
  | antiImperialForeignPolicyRole
  | economicInstitutionRole
  | securityMobilisationRole
  deriving DecidableEq, Repr

structure RoleTransportReceipt where
  carrier : MostazafinCarrier
  role : RelationalRole
  sourceRef : String
  lexicalContinuity : Bool := true
  sameRelationalRoleAsEveryOtherCarrier : Bool := false
  institutionalNamingProvesFidelity : Bool := false

def revolutionarySubjectTransport : RoleTransportReceipt :=
  ⟨.shariatiRevolutionaryCarrier, .revolutionaryConstituencyRole, "Glombitza 2026"⟩

def foundationTransport : RoleTransportReceipt :=
  ⟨.foundationCarrier, .economicInstitutionRole, "Encyclopaedia Iranica: Khomeini i. Life"⟩

def basijTransport : RoleTransportReceipt :=
  ⟨.basijCarrier, .securityMobilisationRole, "Encyclopaedia Iranica: Islamic Political Movements"⟩

theorem same_lexeme_does_not_force_same_role :
    revolutionarySubjectTransport.role != foundationTransport.role := by
  decide

theorem institutional_name_does_not_prove_fidelity :
    foundationTransport.institutionalNamingProvesFidelity = false ∧
    basijTransport.institutionalNamingProvesFidelity = false := by
  decide

end AgdaMirror.Governance.MostazafinSemanticRoleTransport

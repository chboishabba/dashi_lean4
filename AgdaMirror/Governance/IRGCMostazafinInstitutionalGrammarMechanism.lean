import AgdaMirror.Core.HistoricalMechanismCompiler

namespace AgdaMirror.Governance.IRGCMostazafinInstitutionalGrammarMechanism

open AgdaMirror.Core.HistoricalMechanismCompiler

structure InstitutionalGrammarMechanism where
  mechanismRef : String
  historicalSourceRef : String
  historicalJoinRef : String
  primaryLetterSpanRef : String
  relationPreserved : String
  ontologyPreserved : Bool := false
  directTextualBorrowingEstablished : Bool := false
  personalInfluenceEstablished : Bool := false
  institutionalGrammarContinuitySupported : Bool := true

def canonicalMostazafinContinuity : InstitutionalGrammarMechanism :=
  ⟨"mechanism:mostazafin-institutional-grammar-continuity",
   "Glombitza 2026 Iranian Studies",
   "reviewed joins: Marxian field -> Shariati; Iranian-left field -> Khomeini",
   "IRGC primary spans: people/state distinction + common-oppressor/shared-pain frame",
   "oppressed/public subject versus ruling/oppressor elite; anti-imperial solidarity and political agency"⟩

def compilerCausalReceipt : CausalMechanismReceipt :=
  ⟨"mechanism:mostazafin-institutional-grammar-continuity",
   "historical:Shariati-mostazafin/Khomeini-institutionalised-oppressed-oppressor-grammar",
   "2026-IRGC:people-state/common-oppressor/shared-pain/agency-argument",
   "independent Quranic/theological derivation; generic anti-imperial convergence; strategic wartime messaging; generic populist framing",
   "Glombitza 2026 + reviewed genealogy joins + Tasnim primary letter span receipts"⟩

theorem bounded_mechanism_preserves_nonidentity :
    canonicalMostazafinContinuity.ontologyPreserved = false ∧
    canonicalMostazafinContinuity.directTextualBorrowingEstablished = false ∧
    canonicalMostazafinContinuity.personalInfluenceEstablished = false ∧
    canonicalMostazafinContinuity.institutionalGrammarContinuitySupported = true := by
  decide

end AgdaMirror.Governance.IRGCMostazafinInstitutionalGrammarMechanism

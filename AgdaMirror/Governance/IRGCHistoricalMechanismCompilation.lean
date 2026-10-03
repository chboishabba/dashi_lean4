import AgdaMirror.Core.HistoricalMechanismCompiler
import AgdaMirror.Governance.IRGCMostazafinInstitutionalGrammarMechanism

namespace AgdaMirror.Governance.IRGCHistoricalMechanismCompilation

open AgdaMirror.Core.HistoricalMechanismCompiler
open AgdaMirror.Governance.IRGCMostazafinInstitutionalGrammarMechanism

def sourceTotal : SourceTotalReceipt :=
  ⟨"packet:irgc:selected-primary-spans"⟩

def reviewedJoin : ReviewedJoinReceipt :=
  ⟨"join:iran:iranian-left-to-khomeini-west-grammar",
   "node:marxian-left-field",
   "node:khomeini-anti-west-revolutionary-discourse",
   "Kamrava chapter summary / reviewed genealogy owner"⟩

def chronology : DualChronologyReceipt :=
  ⟨"chronology:irgc:historical-knowledge-vs-2026-letter",
   "event-time:2026-09-29:irgc-letter",
   "knowledge-time:2000/2014/2017/2018 scholarship plus 2026 reporting"⟩

def closedIRGCMechanism : HistoricalMechanismWitness :=
  compileHistoricalMechanism
    "mechanism:iranian-revolutionary-grammar-to-irgc-2026"
    sourceTotal reviewedJoin chronology compilerCausalReceipt

def currentCompilation : MechanismCompilation :=
  .closed closedIRGCMechanism

theorem closure_is_nonranking :
    closedIRGCMechanism.createsPoliticalVerdict = false ∧
    closedIRGCMechanism.createsUniversalRanking = false := by
  decide

end AgdaMirror.Governance.IRGCHistoricalMechanismCompilation

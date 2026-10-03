/-!
Fail-closed political-genealogy research frontier.

Pareto priority is research scheduling only:
priority != source authority
candidate discovery != corpus admission
shared vocabulary != historical genealogy
-/

namespace AgdaMirror.Governance.PoliticalGenealogySnowballPareto

inductive GenealogyResidual
  | rodneyToIranDirectInfluenceResidual
  | shariatiToKhomeiniTransmissionResidual
  | thirdWorldismToMostazafinResidual
  | pflpIranGrammarComparisonResidual
  | irgcLetterHistoricalLineageResidual
  | zionismJudaismConflationResidual
  deriving DecidableEq, Repr

structure ParetoCandidate where
  priority : Nat
  residual : GenealogyResidual
  sourceHint : String
  expectedFanOut : Nat
  exactPrimaryOrScholarlyReceiptRequired : Bool := true
  priorityCreatesTruth : Bool := false
  priorityCreatesAuthority : Bool := false
  discoveryCreatesGenealogy : Bool := false

def canonicalFrontier : List ParetoCandidate := [
  ⟨0, .shariatiToKhomeiniTransmissionResidual,
   "primary Shariati/Khomeini texts plus scholarship tracing uptake", 5⟩,
  ⟨1, .thirdWorldismToMostazafinResidual,
   "Iranian intellectual-history scholarship on Third Worldism, socialism and Quranic oppressed/oppressor translation", 5⟩,
  ⟨2, .irgcLetterHistoricalLineageResidual,
   "IRGC 2026 artifact plus earlier Khomeini/Khamenei texts", 4⟩,
  ⟨3, .pflpIranGrammarComparisonResidual,
   "PFLP primary programme/history plus Iranian revolutionary primary texts", 4⟩,
  ⟨4, .rodneyToIranDirectInfluenceResidual,
   "documentary transmission only; conceptual relevance cannot establish influence", 2⟩,
  ⟨5, .zionismJudaismConflationResidual,
   "UN human-rights sources plus plural Jewish/Zionist/anti-Zionist primary positions", 4⟩
]

theorem all_frontier_rows_fail_closed :
    ∀ row ∈ canonicalFrontier,
      row.priorityCreatesTruth = false ∧
      row.priorityCreatesAuthority = false ∧
      row.discoveryCreatesGenealogy = false := by
  intro row h
  simp [canonicalFrontier] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end AgdaMirror.Governance.PoliticalGenealogySnowballPareto

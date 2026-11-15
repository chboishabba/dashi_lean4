import OAI.Algorithms.SubexponentialSAT.SAT

/-!
# M01a: exact source LIST CNF to OpenAI's real Finset CNF semantics

Original finite list carrier: DASHI Golden original circuit/Tseitin modules
(especially OpenAIMathLiteralCodeTransportExact.agda).
External OAI SAT carrier and its evaluation: openai/math, October 2026.
Mathematical prior art: Tseitin/Cook--Levin, elementary finite sets.

This is a concrete *cross-language SAME-SEMANTICS candidate* targeting the
real OAI SAT.CNF (Fin n) and OAI SAT.count, NOT a surrogate SAT decision
algorithm. Keep in the staged **upstream Lean 4.34.1** adapter until it
builds/axiom-checks under its exact pinned source. The existing DASHI
Agda lists still require an actual decoded literal/index correspondence
and a source-bit equality to OAI Encoding.encodeCNF.

NO native Lean 4.28 kernel receipt / Agda theorem transport claimed.
-/

set_option autoImplicit false
noncomputable section
namespace DASHI.OpenAIMath34
open OAI.Algorithms.SubexponentialSAT
variable {n : ℕ}

/-- Literal polarity/index supplied by the separate original Agda M01a
adapter; list/Finset multiplicity and order are dropped by definition. -/
def normalizeListCNF
    (source : List (List (SAT.Literal (Fin n)))) : SAT.CNF (Fin n) := by
  classical
  exact source.toFinset.image (fun clause => clause.toFinset)

/-- Semantics on the REAL OAI SAT.CNF evaluator. A duplicate literal or
duplicate clause does not alter satisfaction; list order is irrelevant. -/
theorem normalizeListCNF_eval_true_iff
    (source : List (List (SAT.Literal (Fin n))))
    (a : SAT.Assignment (Fin n)) :
    SAT.CNF.eval a (normalizeListCNF source) = true ↔
      ∀ clause ∈ source,
        ∃ literal ∈ clause, SAT.Literal.eval a literal = true := by
  classical
  simp [normalizeListCNF, SAT.CNF.eval, SAT.Clause.eval,
    Finset.mem_image]

/-- Original-list model count on the same variable set Fin n.
Do NOT silently drop variables: a SAT.CNF (Fin n) counts *all*
2^n total assignments, even when some variables are unused. -/
def sourceListAcceptedCount
    (source : List (List (SAT.Literal (Fin n)))) : ℕ := by
  classical
  exact (Finset.univ.filter (fun a : SAT.Assignment (Fin n) =>
    decide (∀ clause ∈ source,
      ∃ literal ∈ clause, SAT.Literal.eval a literal = true))).card

/-- Exact model-count equality on all Fin n assignments; this is M01a
(semantics) only. M01b (normal form, sorting/bytes and actual primitive
input) and M02-M05 (machine running time and visited-space) stay open. -/
theorem normalizeListCNF_count_eq
    (source : List (List (SAT.Literal (Fin n)))) :
    SAT.count (normalizeListCNF source) = sourceListAcceptedCount source := by
  classical
  unfold SAT.count SAT.satisfyingAssignments sourceListAcceptedCount
  congr 1
  ext a
  simp [normalizeListCNF_eval_true_iff]

#print axioms DASHI.OpenAIMath34.normalizeListCNF_eval_true_iff
#print axioms DASHI.OpenAIMath34.normalizeListCNF_count_eq

end DASHI.OpenAIMath34

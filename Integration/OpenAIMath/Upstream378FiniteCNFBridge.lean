import Integration.OpenAIMath.ListFinsetCNFTransport
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.Encoding

/-!
# Version-gated same-object OpenAI 378 SAT/encoding consumer

Requires the **upstream 2026-10-26** source with
OAI.Algorithms.SubexponentialSAT.SAT and .Encoding and upstream's Lean 4.34.1.
The DASHI Lean pinned vendor/Mathlib 4.28 currently predates those declarations.
THIS MODULE IS INTENTIONALLY NOT IMPORTED BY `Everything.lean`.
Source-written only; no local Lean kernel acceptance.

Original proof owners:
* OpenAI 378: finite CNF semantics, `SAT.count`, `Encoding.formulaBitLength_upper`
* Classical finite-set/Boolean logic and Cook-Levin/Tseitin.
* DASHI original Agda P1/P2 source compiler and generic ListFinsetCNFTransport.
Do not infer an ETH speedup or equivalence to Agda merely from these names.
-/

namespace Integration.OpenAIMath.Upstream378FiniteCNFBridge

open OAI.Algorithms.SubexponentialSAT

/-- Preserve the original literal `Fin n` variable index and polarity. -/
def toUpstreamCNF {n : ℕ}
    (clauses : List (List (SAT.Literal (Fin n)))) : SAT.CNF (Fin n) :=
  ListFinsetCNFTransport.toFinsetCNF clauses

/-- Identical satisfying assignments, not only existence of one. -/
theorem exactAssignmentTruth {n : ℕ}
    (clauses : List (List (SAT.Literal (Fin n))))
    (assignment : SAT.Assignment (Fin n)) :
    (toUpstreamCNF clauses).eval assignment = true ↔
    ListFinsetCNFTransport.listCNFSatisfied
      (fun literal => literal.eval assignment) clauses := by
  rw [SAT.CNF.eval_eq_true]
  change (∀ C ∈ toUpstreamCNF clauses,
    (∃ literal ∈ C, literal.eval assignment = true)) ↔ _
  exact (ListFinsetCNFTransport.cnfSemanticsExact
    (fun literal => literal.eval assignment) clauses).symm

/-- No duplicates or tautologies can increase the number of upstream clauses. -/
theorem originalClauseBound {n : ℕ}
    (clauses : List (List (SAT.Literal (Fin n)))) :
    (toUpstreamCNF clauses).card ≤ clauses.length :=
  ListFinsetCNFTransport.clauseNumberUpper clauses

/-- Source width 3 transports to the exact upstream `SAT.WidthAtMost 3`. -/
theorem exactWidthAtMostThree {n : ℕ}
    (clauses : List (List (SAT.Literal (Fin n))))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3) :
    SAT.WidthAtMost 3 (toUpstreamCNF clauses) :=
  ListFinsetCNFTransport.normalizedClauseWidthUpper clauses 3 width

/-- The actual upstream `SAT.count`, not a surrogate number of models. -/
theorem exactUpstreamCount {n : ℕ}
    (clauses : List (List (SAT.Literal (Fin n)))) :
    SAT.count (toUpstreamCNF clauses) =
      ListFinsetCNFTransport.countedListModels n
        (fun literal assignment => literal.eval assignment) clauses := by
  classical
  unfold SAT.count SAT.satisfyingAssignments
  unfold ListFinsetCNFTransport.countedListModels
  congr 1
  ext assignment
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact exactAssignmentTruth clauses assignment

/-- Explicit numerical instance of original OpenAI bit-length theorem.
    `n` is the complete number of finite input+gate variables. -/
theorem upstreamExactBitLengthBound {n g : ℕ}
    (clauses : List (List (SAT.Literal (Fin n))))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (clauseCount : clauses.length ≤ 3 * g + 1) :
    Encoding.formulaBitLength (toUpstreamCNF clauses)
      ≤ n + 2 + (24 * n + 28) * (3 * g + 1) := by
  have hw : SAT.WidthAtMost 3 (toUpstreamCNF clauses) :=
    exactWidthAtMostThree clauses width
  have hc : (toUpstreamCNF clauses).card ≤ 3 * g + 1 :=
    (originalClauseBound clauses).trans clauseCount
  have upstream := Encoding.formulaBitLength_upper (toUpstreamCNF clauses) hw
  calc
    Encoding.formulaBitLength (toUpstreamCNF clauses)
        ≤ n + 2 + (4 + (8 * n + 8) * 3) *
            (toUpstreamCNF clauses).card := upstream
    _ ≤ n + 2 + (4 + (8 * n + 8) * 3) * (3 * g + 1) := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hc) _
    _ = n + 2 + (24 * n + 28) * (3 * g + 1) := by ring

/-- A closed quadratic source-variable bound, obtained from the
actual upstream length theorem, NOT a runtime estimate. For real source DAGs
the gate count is ≤ the complete variable count `n=inputs+g`. -/
theorem upstreamQuadraticBitLengthBound {n g : ℕ}
    (clauses : List (List (SAT.Literal (Fin n))))
    (width : ∀ clause ∈ clauses, clause.length ≤ 3)
    (clauseCount : clauses.length ≤ 3 * g + 1)
    (gateCountBound : g ≤ n) :
    Encoding.formulaBitLength (toUpstreamCNF clauses)
      ≤ 72 * (n + 1) ^ 2 := by
  have base := upstreamExactBitLengthBound
    (n := n) (g := g) clauses width clauseCount
  have hg : 3 * g + 1 ≤ 3 * n + 1 := by omega
  have hmul :
      (24 * n + 28) * (3 * g + 1) ≤
        (24 * n + 28) * (3 * n + 1) :=
    Nat.mul_le_mul_left _ hg
  have hstep :
      Encoding.formulaBitLength (toUpstreamCNF clauses)
        ≤ n + 2 + (24 * n + 28) * (3 * n + 1) :=
    base.trans (Nat.add_le_add_left hmul _)
  nlinarith

-- Open items: a kernel-checking receipt on the proper upstream Lean toolchain;
-- Agda source literal/Fin/polarity mapping as an imported SAME-OBJECT theorem;
-- a verified uniform compiler to this list; its bit-time and all-prefix space
-- cost; and composition with exact_count_and_sat on the primitive machine.

end Integration.OpenAIMath.Upstream378FiniteCNFBridge

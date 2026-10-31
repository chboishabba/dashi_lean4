import Integration.OpenAIMath.ListFinsetCNFTransport
import OAI.Algorithms.SubexponentialSAT.SAT
import OAI.Algorithms.SubexponentialSAT.Encoding
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Final

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


/-- SAME-MACHINE list-of-clauses consumer of the ACTUAL 378 theorem.
No fabricated fast SAT oracle or new machine: the upstream machine remains
fixed and its original complexity bounds are retained byte-for-byte.
The count word is rewritten to the exact finite SOURCE LIST model count
using the earlier per-assignment List/Finset normalization bridge. -/
theorem sourceListExactCountMachine :
    ∃ (machine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (countTape answerTape : Fin machine.tapeCount)
      (C A S : ℝ) (d e : ℕ),
      0 < C ∧ 0 < A ∧ 0 < S ∧ 0 < d ∧ 0 < e ∧
      ∀ (n : ℕ)
        (clauses : List (List (SAT.Literal (Fin n)))),
        (∀ clause ∈ clauses, clause.length ≤ 3) →
        ∃ (time : ℕ)
          (final : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LocatedCfg machine),
          OAI.Algorithms.SubexponentialSAT.Computation.Trace
            (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedStep machine)
            time
            (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedInit machine
              (Encoding.encodeCNF (toUpstreamCNF clauses))) final ∧
          final.config.tapes countTape =
            Turing.Tape.mk₁
              ((OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord
                (ListFinsetCNFTransport.countedListModels n
                  (fun literal assignment => literal.eval assignment) clauses)).map some) ∧
          final.config.tapes answerTape =
            Turing.Tape.mk₁
              [some (decide (0 <
                ListFinsetCNFTransport.countedListModels n
                  (fun literal assignment => literal.eval assignment) clauses))] ∧
          final.config.state = Sum.inl (decide (0 <
            ListFinsetCNFTransport.countedListModels n
              (fun literal assignment => literal.eval assignment) clauses)) ∧
          OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat
            (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord
              (ListFinsetCNFTransport.countedListModels n
                (fun literal assignment => literal.eval assignment) clauses)) =
            ListFinsetCNFTransport.countedListModels n
              (fun literal assignment => literal.eval assignment) clauses ∧
          (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.countWord
            (ListFinsetCNFTransport.countedListModels n
              (fun literal assignment => literal.eval assignment) clauses)).length ≤ n + 1 ∧
          (time : ℝ) ≤
            OAI.Algorithms.SubexponentialSAT.SqrtLog.Statement.runtimeBound C A d
              (Encoding.formulaBitLength (toUpstreamCNF clauses)) n ∧
          ∀ (prefixSteps : ℕ)
            (intermediate : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.LocatedCfg machine),
            prefixSteps ≤ time →
            OAI.Algorithms.SubexponentialSAT.Computation.Trace
              (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedStep machine)
              prefixSteps
              (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.locatedInit machine
                (Encoding.encodeCNF (toUpstreamCNF clauses))) intermediate →
            (OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.visitedSpace intermediate : ℝ) ≤
              S * ((Encoding.formulaBitLength (toUpstreamCNF clauses) : ℝ) + 1) ^ e := by
  obtain ⟨machine, countTape, answerTape, C, A, S, d, e,
    hC, hA, hS, hd, he, run⟩ :=
    OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat 3 (by decide)
  refine ⟨machine, countTape, answerTape, C, A, S, d, e,
    hC, hA, hS, hd, he, ?_⟩
  intro n clauses width
  have hw : SAT.WidthAtMost 3 (toUpstreamCNF clauses) :=
    exactWidthAtMostThree clauses width
  obtain ⟨time, final, trace, outputCount, outputAnswer,
    finalState, countWordCorrect, countWordLength, timeBound, prefixSpace⟩ :=
    run n (toUpstreamCNF clauses) hw
  have countId :
      SAT.count (toUpstreamCNF clauses) =
        ListFinsetCNFTransport.countedListModels n
          (fun literal assignment => literal.eval assignment) clauses :=
    exactUpstreamCount clauses
  refine ⟨time, final, trace, ?_, ?_, ?_, ?_, ?_, timeBound, prefixSpace⟩
  · simpa only [countId] using outputCount
  · simpa only [countId] using outputAnswer
  · simpa only [countId] using finalState
  · simpa only [countId] using countWordCorrect
  · simpa only [countId] using countWordLength

-- Open items: a kernel-checking receipt on the proper upstream Lean toolchain;
-- Agda source literal/Fin/polarity mapping as an imported SAME-OBJECT theorem;
-- a verified uniform compiler to this list; its bit-time and all-prefix space
-- cost; and composition with exact_count_and_sat on the primitive machine.

end Integration.OpenAIMath.Upstream378FiniteCNFBridge

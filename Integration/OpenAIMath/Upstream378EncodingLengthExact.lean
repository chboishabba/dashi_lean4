import OAI.Algorithms.SubexponentialSAT.Encoding

/-!
# Exact bit length for the original OAI 378 canonical encoder

Use the existing upstream `Encoding.length_encodeNat`,
`Encoding.length_frame`, and `Encoding.length_encodeList_cons` proofs
rather than re-proving unary and framing recurrences. This module pays only
the missing closed-form nested-list cost and its actual Finset-CNF consumer.

For the original sorted `Encoding.cnfNumbers`:
  L = n+2 + Σ clauses (4 + Σ literalCodes (4*code+8)).

Version-gated: upstream Lean 4.34.1 / OAI 378 sources required.
This is SOURCE-WRITTEN, NOT independently kernel-accepted in DASHI.
Original encoding and length-lemma ownership: OpenAI 378.
DASHI owns only this exact nested-cost adapter; no ETH runtime alteration.
-/

namespace Integration.OpenAIMath.Upstream378EncodingLengthExact

open OAI.Algorithms.SubexponentialSAT

/-- A framed inner list contributes four bits of overhead and
    `4*code+8` bits per unary literal code. -/
private theorem innerCost (codes : List ℕ) :
    2 * (Encoding.encodeList Encoding.encodeNat codes).length + 2 =
      4 + (codes.map (fun code => 4 * code + 8)).sum := by
  induction codes with
  | nil => rfl
  | cons code rest ih =>
      rw [Encoding.length_encodeList_cons]
      simp only [List.map_cons, List.sum_cons, Encoding.length_encodeNat]
      omega

def clauseBitCost (codes : List ℕ) : ℕ :=
  4 + (codes.map (fun code => 4 * code + 8)).sum

/-- Exact emitted-bit total for nested framing, on the upstream encoding,
    not on a second implementation of `encodeList`. -/
theorem encodedBodyLength (clauses : List (List ℕ)) :
    (Encoding.encodeList
      (Encoding.encodeList Encoding.encodeNat) clauses).length =
      1 + (clauses.map clauseBitCost).sum := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      rw [Encoding.length_encodeList_cons]
      simp only [List.map_cons, List.sum_cons, ih]
      have h := innerCost clause
      dsimp [clauseBitCost]
      omega

/-- Actual upstream Finset CNF, actual canonical sorted literal order.
    Exact size, strictly stronger information than an O(v²) envelope. -/
theorem exactFormulaBitLength {n : ℕ} (cnf : SAT.CNF (Fin n)) :
    Encoding.formulaBitLength cnf =
      n + 2 + ((Encoding.cnfNumbers cnf).map clauseBitCost).sum := by
  change (Encoding.encodeNat n ++
    Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (Encoding.cnfNumbers cnf)).length =
    n + 2 + ((Encoding.cnfNumbers cnf).map clauseBitCost).sum
  rw [List.length_append, Encoding.length_encodeNat, encodedBodyLength]
  omega

end Integration.OpenAIMath.Upstream378EncodingLengthExact

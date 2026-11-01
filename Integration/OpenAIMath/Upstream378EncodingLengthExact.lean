import Mathlib
import OAI.Algorithms.SubexponentialSAT.Encoding

/-!
# Exact bit length for the original OAI 378 canonical encoder

The upstream encoder is the authority; these are elementary structural
length theorems over its actual unary `encodeNat`, framed `encodeList`,
`cnfNumbers` and `encodeCNF`. In particular there is no surrogate binary
encoding and no appeal to the machine-complexity result.

The exact numeric identity is shared with the deterministic Python frontend:
  L = n+2 + Σ clauses (4 + Σ literalCodes (4*code+8)).

Version-gated: upstream Lean 4.34.1 / OAI 378 sources required.
This is source-written only, NOT independently kernel-accepted in DASHI.
Attribution: OAI 378 owns the encoding; DASHI owns this adapter proof.
-/

namespace Integration.OpenAIMath.Upstream378EncodingLengthExact

open OAI.Algorithms.SubexponentialSAT

private theorem encodeNat_length (n : ℕ) :
    (Encoding.encodeNat n).length = n + 1 := by
  simp [Encoding.encodeNat]

private theorem frame_length (bits : List Bool) :
    (Encoding.frame bits).length = 2 * bits.length + 1 := by
  induction bits with
  | nil => rfl
  | cons b rest ih =>
      change (true :: b :: Encoding.frame rest).length =
        2 * (b :: rest).length + 1
      simp only [List.length_cons, ih]
      omega

private theorem encodeList_length {α : Type*}
    (enc : α → List Bool) (xs : List α) :
    (Encoding.encodeList enc xs).length =
      1 + (xs.map (fun x => 2 * (enc x).length + 2)).sum := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      change (true :: (Encoding.frame (enc x) ++
          Encoding.encodeList enc rest)).length =
        1 + ((x :: rest).map
          (fun y => 2 * (enc y).length + 2)).sum
      simp only [List.length_cons, List.length_append,
        List.map_cons, List.sum_cons, frame_length, ih]
      omega

/-- One inner unary/framed literal list incurs four framing bits and
    `4*code+8` bits for each literal code. -/
private theorem innerCost (codes : List ℕ) :
    2 * (Encoding.encodeList Encoding.encodeNat codes).length + 2 =
      4 + (codes.map (fun code => 4 * code + 8)).sum := by
  induction codes with
  | nil => rfl
  | cons code rest ih =>
      change 2 * (true :: (Encoding.frame (Encoding.encodeNat code) ++
          Encoding.encodeList Encoding.encodeNat rest)).length + 2 =
        4 + ((code :: rest).map (fun c => 4 * c + 8)).sum
      simp only [List.length_cons, List.length_append,
        List.map_cons, List.sum_cons, frame_length, encodeNat_length]
      omega

def clauseBitCost (codes : List ℕ) : ℕ :=
  4 + (codes.map (fun code => 4 * code + 8)).sum

/-- Exact number of emitted bits in the encoded clause list.
    This is an equality on the original upstream `encodeList`. -/
theorem encodedBodyLength (clauses : List (List ℕ)) :
    (Encoding.encodeList
      (Encoding.encodeList Encoding.encodeNat) clauses).length =
      1 + (clauses.map clauseBitCost).sum := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      change (true :: (Encoding.frame
          (Encoding.encodeList Encoding.encodeNat clause) ++
          Encoding.encodeList
            (Encoding.encodeList Encoding.encodeNat) rest)).length =
        1 + ((clause :: rest).map clauseBitCost).sum
      simp only [List.length_cons, List.length_append,
        List.map_cons, List.sum_cons, frame_length, ih]
      have h := innerCost clause
      dsimp [clauseBitCost]
      omega

/-- An exact arithmetic output-size certificate for each actual upstream
    Finset CNF. The sorted list is the original `Encoding.cnfNumbers`. -/
theorem exactFormulaBitLength {n : ℕ} (cnf : SAT.CNF (Fin n)) :
    Encoding.formulaBitLength cnf =
      n + 2 + ((Encoding.cnfNumbers cnf).map clauseBitCost).sum := by
  change (Encoding.encodeNat n ++
    Encoding.encodeList (Encoding.encodeList Encoding.encodeNat)
      (Encoding.cnfNumbers cnf)).length =
    n + 2 + ((Encoding.cnfNumbers cnf).map clauseBitCost).sum
  rw [List.length_append, encodeNat_length, encodedBodyLength]
  omega

end Integration.OpenAIMath.Upstream378EncodingLengthExact

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Postulate-free rational square-class bit invariants

Lean producer for the exact arithmetic seam left open in the Agda BSD lane.
It uses mathlib's unbounded rational p-adic valuation.

The two invariants are:
* sign of a nonzero rational;
* parity of the 2-adic valuation.

Both are proved invariant under multiplication by a nonzero rational square.
-/

namespace Synthesis.Millennium.BSD

def signBit (q : ℚ) : Bool :=
  decide (q < 0)

def v2Parity (q : ℚ) : ZMod 2 :=
  (padicValRat 2 q : ZMod 2)

theorem signBit_mul_sq
    (q s : ℚ) (hs : s ≠ 0) :
    signBit (q * s ^ 2) = signBit q := by
  have hspos : 0 < s ^ 2 := sq_pos_of_ne_zero hs
  simp only [signBit, Bool.decide_eq_decide]
  constructor <;> intro h
  · exact (mul_neg_iff_of_pos_right hspos).mp h
  · exact (mul_neg_iff_of_pos_right hspos).mpr h

theorem v2Parity_mul_sq
    (q s : ℚ) (hq : q ≠ 0) (hs : s ≠ 0) :
    v2Parity (q * s ^ 2) = v2Parity q := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [v2Parity, padicValRat.mul hq (pow_ne_zero 2 hs), padicValRat.pow]
  push_cast
  ring

theorem signBit_one : signBit (1 : ℚ) = false := by
  native_decide

theorem signBit_neg_one : signBit (-1 : ℚ) = true := by
  native_decide

theorem v2Parity_one : v2Parity (1 : ℚ) = 0 := by
  simp [v2Parity]

theorem v2Parity_neg_one : v2Parity (-1 : ℚ) = 0 := by
  simp [v2Parity]

theorem v2Parity_two : v2Parity (2 : ℚ) = 1 := by
  change ((padicValRat 2 (2 : ℚ) : ℤ) : ZMod 2) = 1
  rw [padicValRat.self (by norm_num : 1 < 2)]
  norm_num

theorem v2Parity_neg_two : v2Parity (-2 : ℚ) = 1 := by
  simp only [v2Parity, padicValRat.neg]
  exact v2Parity_two

/-- The four torsion dictionary values have exactly the two bit coordinates
used by the Agda finite C2 x C2 seed: sign of the first coordinate and v₂
parity of the second coordinate. -/
theorem torsion_dictionary_bits :
    (signBit (1 : ℚ), v2Parity (1 : ℚ)) = (false, 0) ∧
    (signBit (-1 : ℚ), v2Parity (-1 : ℚ)) = (true, 0) ∧
    (signBit (1 : ℚ), v2Parity (2 : ℚ)) = (false, 1) ∧
    (signBit (-1 : ℚ), v2Parity (-2 : ℚ)) = (true, 1) := by
  simp [signBit_one, signBit_neg_one, v2Parity_one, v2Parity_neg_one,
    v2Parity_two, v2Parity_neg_two]

end Synthesis.Millennium.BSD

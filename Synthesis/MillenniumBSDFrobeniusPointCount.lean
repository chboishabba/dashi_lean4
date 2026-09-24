import Synthesis.MillenniumBSDCMInertCharacterSum
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# Literal Frobenius coefficient from finite-field point counting

For the curve

  E : y² = x³ - x,

define the affine point count fibrewise over x.  Mathlib's exact theorem
`quadraticChar_card_sqrts` identifies each y-fibre with
`1 + χ(x³-x)`.  Therefore

  #E(F_p) = p + 1 + Σ_x χ(x³-x)

for odd primes, and the literal Frobenius coefficient

  a_p = p + 1 - #E(F_p)

is exactly the negative character sum.

Combining this with `inert_cm_character_sum_zero` proves the actual signed
coefficient `a_p = 0` for p ≡ 3 (mod 4).
-/

namespace Synthesis.Millennium.BSD

open scoped BigOperators

def affineFiberCount (p : ℕ) [Fact p.Prime] : ℕ :=
  ∑ x : ZMod p,
    ({y : ZMod p | y ^ 2 = cmCubic x}.toFinset.card)

def projectivePointCount (p : ℕ) [Fact p.Prime] : ℕ :=
  affineFiberCount p + 1

def frobeniusCoefficient (p : ℕ) [Fact p.Prime] : ℤ :=
  (p : ℤ) + 1 - projectivePointCount p

theorem fiberCount_eq_character_add_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (x : ZMod p) :
    (({y : ZMod p | y ^ 2 = cmCubic x}.toFinset.card : ℕ) : ℤ)
      = quadraticChar (ZMod p) (cmCubic x) + 1 := by
  simpa using
    (quadraticChar_card_sqrts
      ((ringChar_zmod_n p).substr hp2)
      (cmCubic x))

theorem affineFiberCount_cast_eq
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (affineFiberCount p : ℤ)
      = (p : ℤ) + cmCharacterSum p := by
  unfold affineFiberCount cmCharacterSum cmCharacterTerm
  rw [Nat.cast_sum]
  calc
    ∑ x : ZMod p,
        (({y : ZMod p | y ^ 2 = cmCubic x}.toFinset.card : ℕ) : ℤ)
        =
      ∑ x : ZMod p,
        (quadraticChar (ZMod p) (cmCubic x) + 1) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact fiberCount_eq_character_add_one hp2 x
    _ =
      (∑ x : ZMod p, quadraticChar (ZMod p) (cmCubic x))
        + ∑ _x : ZMod p, (1 : ℤ) := by
          rw [Finset.sum_add_distrib]
    _ = cmCharacterSum p + (Fintype.card (ZMod p) : ℤ) := by
          simp [cmCharacterSum, cmCharacterTerm]
    _ = cmCharacterSum p + (p : ℤ) := by
          simp
    _ = (p : ℤ) + cmCharacterSum p := by ring

theorem projectivePointCount_cast_eq
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (projectivePointCount p : ℤ)
      = (p : ℤ) + 1 + cmCharacterSum p := by
  unfold projectivePointCount
  rw [Nat.cast_add, affineFiberCount_cast_eq hp2]
  norm_num
  ring

theorem frobeniusCoefficient_eq_neg_characterSum
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    frobeniusCoefficient p = - cmCharacterSum p := by
  unfold frobeniusCoefficient
  rw [projectivePointCount_cast_eq hp2]
  ring

theorem inert_frobeniusCoefficient_eq_zero
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    frobeniusCoefficient p = 0 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  rw [frobeniusCoefficient_eq_neg_characterSum hp2]
  simp [inert_cm_character_sum_zero hmod]

theorem inert_projectivePointCount_eq_p_add_one
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    projectivePointCount p = p + 1 := by
  have hp2 : p ≠ 2 := by
    intro hp
    subst p
    norm_num at hmod
  apply Int.ofNat.inj
  change (projectivePointCount p : ℤ) = ((p + 1 : ℕ) : ℤ)
  rw [projectivePointCount_cast_eq hp2,
    inert_cm_character_sum_zero hmod]
  norm_num

end Synthesis.Millennium.BSD

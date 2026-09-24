import Synthesis.MillenniumBSDCMPrimeClassification
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

/-!
# Inert CM character-sum cancellation for y² = x³ - x

For an odd prime p ≡ 3 mod 4, -1 is a nonsquare in ZMod p.  Since

  f(-x) = -(f x),   f(x) = x³ - x,

the quadratic character changes sign under x ↦ -x.  Reindexing the complete
finite sum by negation therefore proves the character sum is exactly zero.

This is the arithmetic core of the signed inert-prime trace a_p = 0.  The
remaining same-object theorem is to identify this character sum with the
repository's literal elliptic Frobenius trace/local Euler coefficient.
-/

namespace Synthesis.Millennium.BSD

open scoped BigOperators

def cmCubic {p : ℕ} (x : ZMod p) : ZMod p :=
  x ^ 3 - x

theorem cmCubic_neg {p : ℕ} (x : ZMod p) :
    cmCubic (-x) = -(cmCubic x) := by
  simp [cmCubic]
  ring

theorem inert_neg_one_nonsquare
    {p : ℕ} [Fact p.Prime] (hmod : p % 4 = 3) :
    ¬ IsSquare (-1 : ZMod p) := by
  rw [FiniteField.isSquare_neg_one_iff]
  simp [hmod]

theorem inert_quadraticChar_neg_one
    {p : ℕ} [Fact p.Prime] (hmod : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  exact quadraticChar_neg_one_iff_not_isSquare.mpr
    (inert_neg_one_nonsquare hmod)

def cmCharacterTerm (p : ℕ) [Fact p.Prime] (x : ZMod p) : ℤ :=
  quadraticChar (ZMod p) (cmCubic x)

def cmCharacterSum (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ x : ZMod p, cmCharacterTerm p x

theorem cmCharacterTerm_neg
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) (x : ZMod p) :
    cmCharacterTerm p (-x) = - cmCharacterTerm p x := by
  rw [cmCharacterTerm, cmCubic_neg]
  change quadraticChar (ZMod p) ((-1) * cmCubic x) =
    - quadraticChar (ZMod p) (cmCubic x)
  rw [map_mul, inert_quadraticChar_neg_one hmod]
  simp

theorem inert_cm_character_sum_zero
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    cmCharacterSum p = 0 := by
  have hreindex :
      (∑ x : ZMod p, cmCharacterTerm p (-x)) =
        ∑ x : ZMod p, cmCharacterTerm p x :=
    Fintype.sum_equiv (Equiv.neg _) _ _
      (fun _ => rfl)
  have hneg :
      (∑ x : ZMod p, cmCharacterTerm p (-x)) =
        -(∑ x : ZMod p, cmCharacterTerm p x) := by
    simp_rw [cmCharacterTerm_neg hmod]
    exact Finset.sum_neg_distrib
  have hself : cmCharacterSum p = - cmCharacterSum p := by
    unfold cmCharacterSum
    exact hreindex.symm.trans hneg
  linarith

def inertTraceCandidate (p : ℕ) [Fact p.Prime] : ℤ :=
  - cmCharacterSum p

theorem inertTraceCandidate_eq_zero
    {p : ℕ} [Fact p.Prime]
    (hmod : p % 4 = 3) :
    inertTraceCandidate p = 0 := by
  simp [inertTraceCandidate, inert_cm_character_sum_zero hmod]

end Synthesis.Millennium.BSD

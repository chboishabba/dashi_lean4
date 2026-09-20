import Synthesis.MillenniumBSDCMEta32QProduct
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic

/-!
# Rotational symmetry of the eta32 q-product

The level-32 CM eta product has the literal shape

  q * G(q^4,q^8).

Hence quarter-turning q multiplies the function by i.  This is the analytic
source of the familiar support restriction to Fourier exponents n ≡ 1 mod 4.

We prove the exact function symmetry here.  The remaining coefficient theorem
is to transport this symmetry through the Taylor/q-expansion coefficient API;
that transport is separate from the much harder identification with elliptic
coefficients.
-/

namespace Synthesis.Millennium.BSD

open Complex

theorem cmEta32QProduct_neg (q : ℂ) :
    cmEta32QProduct (-q) = - cmEta32QProduct q := by
  unfold cmEta32QProduct
  have h4 : ∀ n : ℕ, (-q) ^ (4 * (n + 1)) = q ^ (4 * (n + 1)) := by
    intro n
    rw [neg_pow]
    simp
  have h8 : ∀ n : ℕ, (-q) ^ (8 * (n + 1)) = q ^ (8 * (n + 1)) := by
    intro n
    rw [neg_pow]
    simp
  simp_rw [h4, h8]
  ring

theorem cmEta32QProduct_mul_I (q : ℂ) :
    cmEta32QProduct (Complex.I * q) =
      Complex.I * cmEta32QProduct q := by
  unfold cmEta32QProduct
  have h4 : ∀ n : ℕ, (Complex.I * q) ^ (4 * (n + 1)) =
      q ^ (4 * (n + 1)) := by
    intro n
    rw [mul_pow]
    have hi : Complex.I ^ (4 * (n + 1)) = (1 : ℂ) := by
      rw [pow_mul]
      simp
    rw [hi, one_mul]
  have h8 : ∀ n : ℕ, (Complex.I * q) ^ (8 * (n + 1)) =
      q ^ (8 * (n + 1)) := by
    intro n
    rw [mul_pow]
    have hi : Complex.I ^ (8 * (n + 1)) = (1 : ℂ) := by
      rw [pow_mul]
      simp
    rw [hi, one_mul]
  simp_rw [h4, h8]
  ring

theorem cmEta32QProduct_mul_neg_I (q : ℂ) :
    cmEta32QProduct (-Complex.I * q) =
      -Complex.I * cmEta32QProduct q := by
  calc
    cmEta32QProduct (-Complex.I * q)
        = cmEta32QProduct (-(Complex.I * q)) := by congr 1 <;> ring
    _ = - cmEta32QProduct (Complex.I * q) := cmEta32QProduct_neg _
    _ = -Complex.I * cmEta32QProduct q := by
      rw [cmEta32QProduct_mul_I]
      ring

/--
Abstract coefficient consequence of quarter-turn covariance.  Any power-series
coefficient family satisfying the displayed expansion law must vanish away
from the congruence class 1 mod 4.  This formulation lets a future native
q-expansion/Taylor API instantiate the result without redoing the algebra.
-/
theorem quarterTurn_covariance_forces_coefficient_zero
    (a : ℕ → ℂ)
    (n : ℕ)
    (hcoeff : Complex.I ^ n * a n = Complex.I * a n)
    (hmod : n % 4 ≠ 1) :
    a n = 0 := by
  have hI : Complex.I ^ n ≠ Complex.I := by
    intro h
    have hpow : Complex.I ^ (n % 4) = Complex.I := by
      simpa [pow_eq_pow_mod_four] using h
    interval_cases hrem : n % 4 <;> simp [hrem] at hpow hmod
  apply (sub_eq_zero.mp ?_)
  have hmul : (Complex.I ^ n - Complex.I) * a n = 0 := by
    calc
      (Complex.I ^ n - Complex.I) * a n
          = Complex.I ^ n * a n - Complex.I * a n := by ring
      _ = 0 := by rw [hcoeff]; ring
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hI)

end Synthesis.Millennium.BSD

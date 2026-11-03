import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic

/-!
# K05-PRODUCT: every finite mixed signed-factorial Cauchy coefficient

The literal pure-imaginary exponential series has nth term
  (I * x)^n / n!.
The real/imaginary parts are precisely the alternating even factorial
cosine and alternating odd factorial sine terms already represented by
DASHI's Bishop Round11 configured source.

This module proves the *all-n* Cauchy coefficient theorem via the
factorial/binomial identity, before taking any infinite limit.
There is no assumed sine/cosine addition theorem and no invocation
of `Complex.exp_add` in the coefficient proof.

A second, separate source-identity gate is to connect the existing
Agda configured signed-factorial `E.sineTerm`/`E.cosineTerm` (on
vendor/bishop `Real`) to these complex coefficients and transport
the absolutely convergent Cauchy sums. A Lean finite coefficient
theorem is not by itself an Agda-kernel proof of that gate.

Attribution: Cauchy; Newton/binomial theorem; Bishop/Bridges;
Zachary Murray and pinned Viktor Csimma Bishop; Mathlib;
original DASHI finite factorial/Cauchy proof owners.
-/

namespace Integration.BishopPureImaginaryFiniteCauchyCoefficientsExact

open scoped BigOperators

noncomputable section

/-- The literal complex coefficient with one imaginary variable. -/
def imaginaryCoefficient (x : ℝ) (n : ℕ) : ℂ :=
  (Complex.I * (x : ℂ)) ^ n / (n.factorial : ℂ)

/-- The finite Cauchy convolution uses the *same* factorial degrees
as the original source, without any limit or trigonometric identity. -/
def imaginaryCauchyCoefficient (x y : ℝ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    imaginaryCoefficient x k * imaginaryCoefficient y (n - k)

/-- The underlying algebraic statement holds for any two complex
arguments. This exactly isolates the mixed signed-factorial step. -/
theorem factorialCauchyCoefficient
    (u v : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (u ^ k / (k.factorial : ℂ)) *
        (v ^ (n - k) / ((n - k).factorial : ℂ))) =
      (u + v) ^ n / (n.factorial : ℂ) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
      (u ^ k / (k.factorial : ℂ)) *
        (v ^ (n - k) / ((n - k).factorial : ℂ)))
        = (∑ k ∈ Finset.range (n + 1),
            u ^ k * v ^ (n - k) * ((n.choose k : ℕ) : ℂ)) /
              (n.factorial : ℂ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k hk
          have hle : k ≤ n :=
            Nat.le_of_lt_succ (Finset.mem_range.mp hk)
          rw [Nat.cast_choose ℂ hle]
          have hkfac : (k.factorial : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_pos k).ne'
          have hsubfac : ((n - k).factorial : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_pos (n - k)).ne'
          have hnfac : (n.factorial : ℂ) ≠ 0 := by
            exact_mod_cast (Nat.factorial_pos n).ne'
          field_simp [hkfac, hsubfac, hnfac]
          <;> ring
    _ = (u + v) ^ n / (n.factorial : ℂ) := by
          rw [add_pow]

/-- ALL-n coefficient multiplication for the true pure-imaginary
series. No missing finite index, parity case, or real-only product. -/
theorem imaginaryCauchyCoefficient_eq_add
    (x y : ℝ) (n : ℕ) :
    imaginaryCauchyCoefficient x y n =
      imaginaryCoefficient (x + y) n := by
  let u : ℂ := Complex.I * (x : ℂ)
  let v : ℂ := Complex.I * (y : ℂ)
  have huv : u + v = Complex.I * ((x + y : ℝ) : ℂ) := by
    dsimp [u, v]
    push_cast
    ring
  change
    (∑ k ∈ Finset.range (n + 1),
      (u ^ k / (k.factorial : ℂ)) *
        (v ^ (n - k) / ((n - k).factorial : ℂ))) =
      (Complex.I * ((x + y : ℝ) : ℂ)) ^ n /
        (n.factorial : ℂ)
  rw [factorialCauchyCoefficient u v n, huv]

end

end Integration.BishopPureImaginaryFiniteCauchyCoefficientsExact

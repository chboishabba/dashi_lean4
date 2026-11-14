import Synthesis.MillenniumBSDCMQ2ActualCurveValuationExact
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic

/-!
# BSD K1: actual Q_2 square root of 3705 via the native Mathlib Hensel lemma

This attempts the *original* required statement, not just a ZMod(2^n)
finite approximation and not a renamed auxiliary square-class carrier.
The input is the genuine dyadic inequality for f(X)=X^2-3705 at a=1:
  f(1)=-3704=-8*463, f'(1)=2,
  ‖f(1)‖_2 ≤ 1/8 < (1/2)^2 = ‖f'(1)‖_2^2.
The root lives in Z_2 and is cast to Q_2.

SOURCE-WRITTEN CANDIDATE. Local Lean 4.28 + pinned Mathlib build is
required before this can be marked kernel accepted. No PadicQuadratic-
KummerCompatibility, local H1 or classical Sha theorem is asserted.
-/

noncomputable section

namespace Synthesis.Millennium.BSD

private def cm3705HenselPolynomial : Polynomial ℤ_[2] :=
  Polynomial.X ^ 2 - Polynomial.C 3705

/-- A true dyadic root, supplied by the existing Mathlib Hensel theorem,
not by finite modular regression. -/
theorem cmQ2SquareRoot3705 :
    ∃ z : ℚ_[2], z ^ 2 = (3705 : ℚ_[2]) := by
  have hdiv : (2 : ℤ) ^ 3 ∣ (3704 : ℤ) := by norm_num
  have hnorm3704 :
      ‖(3704 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-(3 : ℤ)) := by
    simpa using
      ((PadicInt.norm_int_le_pow_iff_dvd
        (p := 2) (k := 3704) (n := 3)).2 hdiv)
  have hnorm2 : ‖(2 : ℤ_[2])‖ = (1 / 2 : ℝ) := by
    simpa using (PadicInt.norm_p (p := 2))
  have heval :
      (Polynomial.aeval (1 : ℤ_[2])) cm3705HenselPolynomial =
        -(3704 : ℤ_[2]) := by
    simp [cm3705HenselPolynomial]
    norm_num
  have hderiv :
      (Polynomial.aeval (1 : ℤ_[2]))
        cm3705HenselPolynomial.derivative = (2 : ℤ_[2]) := by
    simp [cm3705HenselPolynomial]
  have hnorm :
      ‖(Polynomial.aeval (1 : ℤ_[2])) cm3705HenselPolynomial‖ <
        ‖(Polynomial.aeval (1 : ℤ_[2]))
          cm3705HenselPolynomial.derivative‖ ^ 2 := by
    rw [heval, hderiv, norm_neg, hnorm2]
    have hsmall : ‖(3704 : ℤ_[2])‖ ≤ (1 / 8 : ℝ) := by
      norm_num at hnorm3704 ⊢
      exact hnorm3704
    linarith
  obtain ⟨z, hz, _, _, _⟩ :=
    hensels_lemma (p := 2) (R := ℤ_[2])
      (F := cm3705HenselPolynomial) (a := 1) hnorm
  have hzSq : z ^ 2 = (3705 : ℤ_[2]) := by
    have hh : z ^ 2 - (3705 : ℤ_[2]) = 0 := by
      simpa [cm3705HenselPolynomial] using hz
    exact sub_eq_zero.mp hh
  refine ⟨(z : ℚ_[2]), ?_⟩
  exact_mod_cast hzSq

end Synthesis.Millennium.BSD

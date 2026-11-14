import Integration.BishopRound11ImaginaryProductSemanticReflection
import Integration.BishopVendoredMachinPiSemantics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Original Bishop K05-PI arctangent-to-Cayley theorem

For the exact already constructed Bishop arctangent series at 1/5
and 1/239 (not a newly selected pi or arctangent), prove the
complex Cayley representation of exp(2i atan x).

The underlying arbitrary-real formula uses Mathlib's actual
sin_arctan, cos_arctan and complex Euler relation, rather than
postulating a Machin identity or a new transcendental.

This is a faithful Lean semantic donor. Original Agda Bishop
setoid exponential/atan-to-Cayley acceptance is STILL a separate
golden proof obligation. No Lean kernel receipt is claimed.
-/

namespace Integration.BishopRound11OriginalArctanCayleyExact

open Integration.BishopVendoredRealEvaluation
open Integration.BishopVendoredMachinPiSemantics
open Integration.BishopRound11MachinSourceBinding

noncomputable section

private theorem arctan_cos_double (x : ℝ) :
    Real.cos (2 * Real.arctan x) = (1 - x ^ 2) / (1 + x ^ 2) := by
  have hp : 0 ≤ 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hp
  rw [Real.cos_two_mul', Real.cos_arctan, Real.sin_arctan]
  field_simp
  nlinarith

private theorem arctan_sin_double (x : ℝ) :
    Real.sin (2 * Real.arctan x) = (2 * x) / (1 + x ^ 2) := by
  have hp : 0 ≤ 1 + x ^ 2 := by positivity
  have hs : Real.sqrt (1 + x ^ 2) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hsq : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt hp
  rw [Real.sin_two_mul, Real.cos_arctan, Real.sin_arctan]
  field_simp
  nlinarith

/-- Cayley equality for a genuine real arctangent; the `2` is
essential, and the denominator is proved nonzero. -/
theorem realArctanExponentialCayley (x : ℝ) :
    Complex.exp (((2 * Real.arctan x : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) + (x : ℂ) * Complex.I) /
      ((1 : ℂ) - (x : ℂ) * Complex.I) := by
  have hx : (1 : ℂ) - (x : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  apply (div_eq_iff hx).2
  rw [Complex.exp_ofReal_mul_I, arctan_cos_double, arctan_sin_double]
  push_cast
  have hq : (((1 + x ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (show (1 + x ^ 2 : ℝ) ≠ 0 by positivity)
  field_simp [hq]
  ring_nf
  simp [Complex.I_sq] <;> ring

/-- Exact original first Machin Bishop source limit, evaluated
through its proven source-series semantics: x = 1/5. -/
theorem originalBishopAtanOneFifthCayley
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    Complex.exp (((2 * eval B.atanOneFifth : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) + (((1 / 5 : ℝ) : ℂ) * Complex.I)) /
      ((1 : ℂ) - (((1 / 5 : ℝ) : ℂ) * Complex.I)) := by
  rw [eval_atanOneFifth A (machinMirror A B)]
  exact realArctanExponentialCayley (1 / 5 : ℝ)

/-- Exact original second Machin Bishop source limit, evaluated
through its proven source-series semantics: x = 1/239. -/
theorem originalBishopAtanOneTwoHundredThirtyNinthCayley
    (A : VendoredArithmeticMirror)
    (B : Round11MachinSourceBinding A) :
    Complex.exp
      (((2 * eval B.atanOneTwoHundredThirtyNinth : ℝ) : ℂ) * Complex.I) =
      ((1 : ℂ) + (((1 / 239 : ℝ) : ℂ) * Complex.I)) /
      ((1 : ℂ) - (((1 / 239 : ℝ) : ℂ) * Complex.I)) := by
  rw [eval_atanOneTwoHundredThirtyNinth A (machinMirror A B)]
  exact realArctanExponentialCayley (1 / 239 : ℝ)

end

end Integration.BishopRound11OriginalArctanCayleyExact

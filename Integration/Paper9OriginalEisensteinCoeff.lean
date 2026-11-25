import Integration.MoonshineEisensteinAgdaTarget
import Mathlib.NumberTheory.ModularForms.QExpansion

/-! SOURCE-WRITTEN, UNCOMPILED.
Pinned Mathlib qExpansion_coeff_unique (Chris Birkbeck and original
Mathlib contributors) applied to the existing Agda-shaped E4/E6 limits.
This sits upstream of Paper9OriginalEisensteinDerivative so that the
constant and first coefficients also consume the same all-index source. -/
namespace Integration.Paper9OriginalEisensteinCoeff
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass
open ArithmeticFunction
open scoped BigOperators ArithmeticFunction.sigma MatrixGroups

-- Exactly the divisor streams of check_cm163_junit_discriminant_reflection.py:
-- no extra contribution at the zero index.
def e4Z (n : ℕ) : ℤ := if n = 0 then 1 else 240 * (sigma 3 n : ℤ)
def e6Z (n : ℕ) : ℤ := if n = 0 then 1 else -504 * (sigma 5 n : ℤ)

-- Reuse the actual shifted term and limit owners, rather than proving a
-- second summability theorem. The original source includes the zero term
-- separately; HasSum's finite-prefix reflection restores precisely that term.
theorem qOfTargetPeriodic (τ : ℍ) :
    Integration.MoonshineEisensteinAgdaTarget.qOfTarget τ=Periodic.qParam 1 τ := by
  rw [Integration.MoonshineEisensteinAgdaTarget.qOfTarget_eq_qParam]
  simp [Integration.MoonshineEisensteinAnalytic.qParam, Periodic.qParam]

theorem e4HasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (e4Z n : ℂ) • Periodic.qParam 1 τ ^ n)
      (Integration.MoonshineEisensteinAnalytic.E4 τ) := by
  let f := fun n : ℕ => (e4Z n : ℂ) • Periodic.qParam 1 τ ^ n
  have hs : HasSum (fun n : ℕ => f (n+1))
      (∑' n : ℕ, Integration.MoonshineEisensteinAgdaTarget.e4Term τ n) := by
    convert (Integration.MoonshineEisensteinAgdaTarget.summable_e4Term τ).hasSum using 1
    funext n
    simp [f, e4Z, Integration.MoonshineEisensteinAgdaTarget.e4Term,
      Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,
      qOfTargetPeriodic, smul_eq_mul, mul_assoc]
  have h := (hasSum_nat_add_iff' 1).mp hs
  rw [← Integration.MoonshineEisensteinAgdaTarget.e4Limit_eq_mathlib_E4 τ]
  simpa [f, e4Z, Integration.MoonshineEisensteinAgdaTarget.e4Limit, add_comm] using h

theorem e6HasSum (τ : ℍ) :
    HasSum (fun n : ℕ => (e6Z n : ℂ) • Periodic.qParam 1 τ ^ n)
      (Integration.MoonshineEisensteinAnalytic.E6 τ) := by
  let f := fun n : ℕ => (e6Z n : ℂ) • Periodic.qParam 1 τ ^ n
  have hs : HasSum (fun n : ℕ => f (n+1))
      (-(∑' n : ℕ, Integration.MoonshineEisensteinAgdaTarget.e6Term τ n)) := by
    convert (Integration.MoonshineEisensteinAgdaTarget.summable_e6Term τ).hasSum.neg using 1
    funext n
    simp [f, e6Z, Integration.MoonshineEisensteinAgdaTarget.e6Term,
      Integration.MoonshineEisensteinAgdaTarget.scaleNatTarget,
      qOfTargetPeriodic, smul_eq_mul, mul_assoc, neg_mul]
  have h := (hasSum_nat_add_iff' 1).mp hs
  rw [← Integration.MoonshineEisensteinAgdaTarget.e6Limit_eq_mathlib_E6 τ]
  simpa [f, e6Z, Integration.MoonshineEisensteinAgdaTarget.e6Limit,
    sub_eq_add_neg, add_comm] using h

theorem e4Coeff (n : ℕ) :
    (qExpansion 1 Integration.MoonshineEisensteinAnalytic.E4).coeff n = (e4Z n : ℂ) := by
  symm
  exact qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL e4HasSum n

theorem e6Coeff (n : ℕ) :
    (qExpansion 1 Integration.MoonshineEisensteinAnalytic.E6).coeff n = (e6Z n : ℂ) := by
  symm
  exact qExpansion_coeff_unique (h := 1) one_pos one_mem_strictPeriods_SL e6HasSum n

end Integration.Paper9OriginalEisensteinCoeff

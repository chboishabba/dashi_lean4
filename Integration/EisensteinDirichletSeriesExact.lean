import Integration.EisensteinGeometricRepresentationFormulaExact
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Dirichlet

namespace Dashi.EisensteinDirichletSeriesExact

open Complex LSeries
open ArithmeticFunction
open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinDivisorCharacterProductExact
open Dashi.EisensteinGeometricRepresentationFormulaExact

/-- Complex-valued copy of the exact signed mod-3 character already used by
the coefficient theorem. -/
def chiMinus3ComplexAF : ArithmeticFunction ℂ where
  toFun n := (chiMinus3Int n : ℂ)
  map_zero' := by simp [chiMinus3Int]

@[simp] theorem chiMinus3ComplexAF_apply (n : Nat) :
    chiMinus3ComplexAF n = (chiMinus3Int n : ℂ) := rfl

/-- The complex divisor-character arithmetic function. -/
noncomputable def chiMinus3DivisorComplexAF : ArithmeticFunction ℂ :=
  (ζ : ArithmeticFunction ℂ) * chiMinus3ComplexAF

/-- Same positive coefficients as the signed integer divisor sum, now in ℂ. -/
theorem chiMinus3DivisorComplexAF_apply
    (n : Nat) (hn : n ≠ 0) :
    chiMinus3DivisorComplexAF n = (chiMinus3DivisorSum n : ℂ) := by
  unfold chiMinus3DivisorComplexAF chiMinus3DivisorSum
  rw [coe_zeta_mul_apply]
  rw [← positiveDivisors_eq_divisors n hn]
  simp [chiMinus3ComplexAF, signedChiMinus3DivisorSum]

/-- The literal geometric coefficient sequence; its value at zero is harmless
for `LSeries`, whose zero term is ignored. -/
def eisensteinGeometricCoefficient (n : Nat) : ℂ :=
  (geometricNormShellCount n : ℂ)

/-- Positive geometric coefficients are exactly six times the convolution
`ζ * χ₋₃`. -/
theorem eisensteinGeometricCoefficient_eq_convolution
    (n : Nat) (hn : n ≠ 0) :
    eisensteinGeometricCoefficient n
      = 6 * chiMinus3DivisorComplexAF n := by
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hgeo := geometricNormShell_eq_signedDivisorShell n hnpos
  have hsigned := signedShell_eq_six_mul_character_sum n hn
  calc
    eisensteinGeometricCoefficient n
        = (signedEisensteinDivisorShellCount n : ℂ) := by
            exact_mod_cast hgeo
    _ = 6 * (chiMinus3DivisorSum n : ℂ) := by
          rw [hsigned]
          norm_num
    _ = 6 * chiMinus3DivisorComplexAF n := by
          rw [chiMinus3DivisorComplexAF_apply n hn]

/-- The character is uniformly bounded by one. -/
theorem chiMinus3ComplexAF_norm_le_one (n : Nat) :
    ‖chiMinus3ComplexAF n‖ ≤ 1 := by
  simp only [chiMinus3ComplexAF_apply]
  simp [chiMinus3Int]
  split_ifs <;> norm_num

/-- Hence its L-series is absolutely summable throughout `re(s) > 1`. -/
theorem chiMinus3ComplexAF_summable
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (chiMinus3ComplexAF ·) s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (m := 1) (fun n _ => chiMinus3ComplexAF_norm_le_one n) hs

/-- Name the character L-series used in the final factorization. -/
def chiMinus3LSeries (s : ℂ) : ℂ :=
  LSeries (chiMinus3ComplexAF ·) s

/-- Analytic downstream theorem.  On the common half-plane `re(s)>1`, the
literal geometric Eisenstein shell series factors as

`6 * ζ(s) * L(s, χ₋₃)`.

This is derived from the proved coefficient theorem and Mathlib's native
Dirichlet-convolution/L-series multiplication theorem; no Cantor/scaling
identity is used. -/
theorem eisensteinGeometricLSeries_factorization
    (s : ℂ) (hs : 1 < s.re) :
    LSeries eisensteinGeometricCoefficient s
      = 6 * riemannZeta s * chiMinus3LSeries s := by
  have hzeta : LSeriesSummable ((ζ : ArithmeticFunction ℂ) ·) s :=
    LSeriesSummable_zeta_iff.mpr hs
  have hchi : LSeriesSummable (chiMinus3ComplexAF ·) s :=
    chiMinus3ComplexAF_summable hs
  calc
    LSeries eisensteinGeometricCoefficient s
        = LSeries ((6 : ℂ) • (chiMinus3DivisorComplexAF ·)) s := by
            apply LSeries_congr
            intro n hn
            simpa [Pi.smul_apply] using
              eisensteinGeometricCoefficient_eq_convolution n hn
    _ = 6 * LSeries (chiMinus3DivisorComplexAF ·) s := by
          simpa using LSeries_smul (chiMinus3DivisorComplexAF ·) (6 : ℂ) s
    _ = 6 *
        (LSeries ((ζ : ArithmeticFunction ℂ) ·) s *
          LSeries (chiMinus3ComplexAF ·) s) := by
          rw [chiMinus3DivisorComplexAF]
          rw [ArithmeticFunction.LSeries_mul' hzeta hchi]
    _ = 6 * riemannZeta s * chiMinus3LSeries s := by
          rw [LSeries_zeta_eq_riemannZeta hs]
          simp [chiMinus3LSeries, mul_assoc]

structure EisensteinDirichletSeriesBoundary where
  complexCharacterCarrierPaid : Bool := true
  positiveCoefficientConvolutionPaid : Bool := true
  characterSummabilityOnReGtOnePaid : Bool := true
  zetaCharacterProductPaid : Bool := true
  geometricLSeriesFactorizationPaid : Bool := true
  analyticContinuationBeyondCommonHalfPlaneClaimed : Bool := false
  cantorScalingSeriesIdentified : Bool := false

def canonicalBoundary : EisensteinDirichletSeriesBoundary := {}

end Dashi.EisensteinDirichletSeriesExact

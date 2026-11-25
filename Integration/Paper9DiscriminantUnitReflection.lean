import Integration.Paper9LaurentTriangularReflection
import Mathlib.RingTheory.PowerSeries.Inverse

/-! SOURCE-WRITTEN, UNCOMPILED.
Use the original Mathlib qExpansion of the normalized Delta target.
Avoid reflecting the eta product logarithmic derivative merely to get
J's coefficients. Actual analytic Taylor identification and the
integer packet reflection remain unpaid. -/
namespace Integration.Paper9DiscriminantUnitReflection

open Complex Function UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass
open scoped BigOperators
open Integration.Paper9OriginalEisensteinDerivative

noncomputable section

def E4PS : PowerSeries ℂ :=
  qExpansion 1 Integration.MoonshineEisensteinAnalytic.E4
def E6PS : PowerSeries ℂ :=
  qExpansion 1 Integration.MoonshineEisensteinAnalytic.E6
def deltaPS : PowerSeries ℂ :=
  qExpansion 1 Integration.MoonshineEisensteinAgdaTarget.normalizedDeltaForm

theorem deltaSource :
    deltaPS = (1728 : ℂ)⁻¹ • (E4PS^3-E6PS^2) := by
  unfold deltaPS E4PS E6PS
  rw [Integration.MoonshineDeltaIdentityPinned.normalizedDeltaForm_qExpansion_eq]
  simp [pow_succ,mul_assoc]

theorem deltaZero : deltaPS.coeff 0=0 :=
  Integration.MoonshineDeltaIdentityPinned.normalizedDeltaForm_qExpansion_coeff_zero

theorem deltaOne : deltaPS.coeff 1=1 :=
  Integration.MoonshineDeltaIdentityPinned.normalizedDeltaForm_qExpansion_coeff_one

-- Keep the actual zero mode: shift exactly once, not a Laurent inverse.
def U : PowerSeries ℂ := PowerSeries.mk fun n => deltaPS.coeff (n+1)

theorem UZero : U.constantCoeff=1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simpa [U,PowerSeries.coeff_mk] using deltaOne

theorem shiftDelta : PowerSeries.X*U=deltaPS := by
  ext n
  cases n with
  | zero => simp [deltaZero]
  | succ n => simp [U,PowerSeries.coeff_succ_X_mul,PowerSeries.coeff_mk]

def J : PowerSeries ℂ := E4PS^3*U⁻¹

theorem JZero : J.constantCoeff=1 := by
  have he : E4PS.constantCoeff=1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact e4Coeff0
  simp [J,he,PowerSeries.constantCoeff_inv,UZero]

theorem JRelation : U*J=E4PS^3 := by
  have hu : U.constantCoeff≠0 := by rw [UZero]; norm_num
  unfold J
  calc
    _ = E4PS^3*(U*U⁻¹) := by ring
    _ = _ := by rw [PowerSeries.mul_inv_cancel _ hu,mul_one]

-- Reverse direction: J is uniquely forced by this source identity.
theorem JUnique (v : PowerSeries ℂ) (hv : U*v=E4PS^3) : v=J := by
  have hu : U.constantCoeff≠0 := by rw [UZero]; norm_num
  calc
    v = (U⁻¹*U)*v := by rw [PowerSeries.inv_mul_cancel _ hu,one_mul]
    _ = U⁻¹*(U*v) := by ring
    _ = J := by rw [hv]; unfold J; ring

theorem JCoefficient (n : ℕ) :
    (∑ ij ∈ Finset.Nat.antidiagonal n,
      U.coeff ij.1*J.coeff ij.2) = (E4PS^3).coeff n := by
  rw [← PowerSeries.coeff_mul,JRelation]

-- Exact shifted coefficient formula for the actual discriminant.
theorem UCoefficient (n : ℕ) :
    U.coeff n =
      (1728 : ℂ)⁻¹*((E4PS^3).coeff (n+1)-(E6PS^2).coeff (n+1)) := by
  unfold U
  rw [PowerSeries.coeff_mk,deltaSource,PowerSeries.coeff_smul,map_sub]
  rfl

end
end Integration.Paper9DiscriminantUnitReflection

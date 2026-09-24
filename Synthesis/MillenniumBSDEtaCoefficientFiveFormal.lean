import Synthesis.MillenniumBSDEllipticCoefficientFive
import Synthesis.MillenniumBSDCMEta32TaylorSupport
import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Tactic

/-!
# The first nontrivial eta coefficient: c_5 = -2

We use exactly the amount of q-series algebra needed for the Clay-facing
same-object check.  Let P be Euler's pentagonal power series.  The formal
eta-product is

  X * P(X^4)^2 * P(X^8)^2.

Its coefficient at X^5 is -2.  The analytic Euler product agrees locally
with this formal series on the unit disc, so uniqueness of the Taylor series
transports the finite coefficient calculation to `cmEta32TaylorCoeff 5`.
-/

namespace Synthesis.Millennium.BSD

open PowerSeries Filter Set

noncomputable def cmEtaEulerFormal : PowerSeries ℂ :=
  PowerSeries.pentagonalSeries ℂ

noncomputable def cmEta32FormalSeries : PowerSeries ℂ :=
  X * (cmEtaEulerFormal.subst (X ^ 4)) ^ 2 *
    (cmEtaEulerFormal.subst (X ^ 8)) ^ 2

@[simp] theorem cmEtaEulerFormal_coeff_zero :
    cmEtaEulerFormal.coeff 0 = 1 := by
  simpa [cmEtaEulerFormal] using
    (PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℂ) (0 : ℤ))

@[simp] theorem cmEtaEulerFormal_coeff_one :
    cmEtaEulerFormal.coeff 1 = -1 := by
  simpa [cmEtaEulerFormal] using
    (PowerSeries.coeff_pentagonalSeries_pentagonal (R := ℂ) (1 : ℤ))

@[simp] theorem cmEtaEulerFormal_subst4_coeff_zero :
    (cmEtaEulerFormal.subst (X ^ 4)).coeff 0 = 1 := by
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by norm_num)]
  simp

@[simp] theorem cmEtaEulerFormal_subst4_coeff_four :
    (cmEtaEulerFormal.subst (X ^ 4)).coeff 4 = -1 := by
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by norm_num)]
  norm_num

theorem cmEtaEulerFormal_subst4_coeff_lt_four
    {n : ℕ} (hn : 0 < n) (hn4 : n < 4) :
    (cmEtaEulerFormal.subst (X ^ 4)).coeff n = 0 := by
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by norm_num)]
  simp [Nat.not_dvd_of_pos_of_lt hn hn4]

theorem cmEtaEulerFormal_subst8_coeff_pos_lt_eight
    {n : ℕ} (hn : 0 < n) (hn8 : n < 8) :
    (cmEtaEulerFormal.subst (X ^ 8)).coeff n = 0 := by
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by norm_num)]
  simp [Nat.not_dvd_of_pos_of_lt hn hn8]

@[simp] theorem cmEtaEulerFormal_subst8_coeff_zero :
    (cmEtaEulerFormal.subst (X ^ 8)).coeff 0 = 1 := by
  rw [PowerSeries.coeff_subst_X_pow (R := ℂ) (S := ℂ) (by norm_num)]
  simp

theorem cmEtaEulerFormal_subst4_sq_coeff_four :
    ((cmEtaEulerFormal.subst (X ^ 4)) ^ 2).coeff 4 = -2 := by
  simp only [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_eq_map_range]
  norm_num [cmEtaEulerFormal_subst4_coeff_lt_four]

theorem cmEtaEulerFormal_subst8_sq_coeff_zero :
    ((cmEtaEulerFormal.subst (X ^ 8)) ^ 2).coeff 0 = 1 := by
  simp [pow_two]

theorem cmEtaEulerFormal_subst8_sq_coeff_pos_le_four
    {n : ℕ} (hn : 0 < n) (hn4 : n ≤ 4) :
    ((cmEtaEulerFormal.subst (X ^ 8)) ^ 2).coeff n = 0 := by
  simp only [pow_two, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_eq_map_range]
  apply Finset.sum_eq_zero
  intro ij hij
  rcases ij with ⟨i,j⟩
  simp only [Prod.fst, Prod.snd]
  have hijsum : i + j = n := by
    simpa using Finset.mem_antidiagonal.mp hij
  by_cases hi : i = 0
  · subst i
    have hj : 0 < j := by omega
    rw [cmEtaEulerFormal_subst8_coeff_pos_lt_eight hj (by omega)]
    simp
  · have hi' : 0 < i := Nat.pos_of_ne_zero hi
    rw [cmEtaEulerFormal_subst8_coeff_pos_lt_eight hi' (by omega)]
    simp

theorem cmEta32FormalSeries_coeff_five :
    cmEta32FormalSeries.coeff 5 = -2 := by
  unfold cmEta32FormalSeries
  rw [show X = X ^ 1 := by simp, ← mul_assoc,
    PowerSeries.coeff_X_pow_mul]
  simp only [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_eq_map_range]
  norm_num [cmEtaEulerFormal_subst4_sq_coeff_four,
    cmEtaEulerFormal_subst8_sq_coeff_zero,
    cmEtaEulerFormal_subst8_sq_coeff_pos_le_four]

/-- Euler's analytic function has the pentagonal formal series at zero. -/
theorem cmEtaEulerFunction_hasFPowerSeriesAt_zero :
    HasFPowerSeriesAt
      (eulerFunction : ℂ → ℂ)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => cmEtaEulerFormal.coeff n)) 0 := by
  rw [hasFPowerSeriesAt_iff]
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
  have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  simpa [cmEtaEulerFormal, smul_eq_mul, mul_comm] using
    (hasSum_eulerFunction_pentagonalSeries (R := ℂ) hz')

/-- The analytic Euler product equals Euler's pentagonal function near zero. -/
theorem cmEtaEulerProduct_eventuallyEq_eulerFunction :
    cmEtaEulerProduct =ᶠ[𝓝 0] (eulerFunction : ℂ → ℂ) := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
  have hz' : ‖z‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  symm
  exact eulerFunction_eq_tprod hz'

/-- The finite coefficient computation on the formal eta series. -/
theorem cmEta32_formal_coefficient_five :
    cmEta32FormalSeries.coeff 5 = (-2 : ℂ) :=
  cmEta32FormalSeries_coeff_five

end Synthesis.Millennium.BSD

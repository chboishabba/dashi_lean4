import Synthesis.MillenniumBSDEtaCoefficientFiveFormal
import Synthesis.MillenniumBSDEllipticCoefficientFive
import Synthesis.MillenniumBSDCMEta32TaylorSupport
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Tactic

/-!
# Weld the formal eta coefficient at 5 to the canonical Taylor coefficient

This is deliberately specialized to the existing eta32 object.  We do not
build a general q-expansion library.

On the open unit disk the formal series

  X * P(X^4)^2 * P(X^8)^2

evaluates to the literal eta product, by Euler's pentagonal theorem.  Hence
its coefficient series is an alternate local analytic expansion of
`cmEta32QProduct`.  Uniqueness of `HasFPowerSeriesAt` identifies it with the
canonical iterated-derivative Taylor series.  The already-computed formal
coefficient `5 = -2` therefore gives the actual eta coefficient.
-/

namespace Synthesis.Millennium.BSD

open Complex Set Filter

private theorem hasEval_of_norm_lt_one {q : ℂ} (hq : ‖q‖ < 1) :
    PowerSeries.HasEval q := by
  change Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 0)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq

theorem evalPentagonal_eq_eulerFunction
    {q : ℂ} (hq : ‖q‖ < 1) :
    PowerSeries.eval₂ (RingHom.id ℂ) q cmEtaEulerFormal = eulerFunction q := by
  have heval := PowerSeries.hasSum_eval₂
    (continuous_id : Continuous (RingHom.id ℂ))
    (hasEval_of_norm_lt_one hq) cmEtaEulerFormal
  have heuler :
      HasSum (fun n : ℕ => PowerSeries.coeff n cmEtaEulerFormal * q ^ n)
        (eulerFunction q) := by
    simpa [cmEtaEulerFormal, smul_eq_mul] using
      hasSum_eulerFunction_pentagonalSeries hq
  exact heval.unique heuler

/-- Evaluation commutes with the two monomial substitutions used by eta32. -/
theorem evalEtaEulerFormal4_eq
    {q : ℂ} (hq : ‖q‖ < 1) :
    PowerSeries.eval₂ (RingHom.id ℂ) q cmEtaEulerFormal4 =
      eulerFunction (q ^ 4) := by
  have hq4 : ‖q ^ 4‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  rw [cmEtaEulerFormal4]
  simpa [PowerSeries.subst_def] using
    (MvPowerSeries.eval₂_subst
      (PowerSeries.HasSubst.X_pow (R := ℂ) (by norm_num : (4 : ℕ) ≠ 0))
      (hasEval_of_norm_lt_one hq)
      cmEtaEulerFormal).trans
      (evalPentagonal_eq_eulerFunction hq4)

theorem evalEtaEulerFormal8_eq
    {q : ℂ} (hq : ‖q‖ < 1) :
    PowerSeries.eval₂ (RingHom.id ℂ) q cmEtaEulerFormal8 =
      eulerFunction (q ^ 8) := by
  have hq8 : ‖q ^ 8‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)
  rw [cmEtaEulerFormal8]
  simpa [PowerSeries.subst_def] using
    (MvPowerSeries.eval₂_subst
      (PowerSeries.HasSubst.X_pow (R := ℂ) (by norm_num : (8 : ℕ) ≠ 0))
      (hasEval_of_norm_lt_one hq)
      cmEtaEulerFormal).trans
      (evalPentagonal_eq_eulerFunction hq8)

theorem evalEta32Formal_eq_qProduct
    {q : ℂ} (hq : ‖q‖ < 1) :
    PowerSeries.eval₂ (RingHom.id ℂ) q cmEta32FormalSeries =
      cmEta32QProduct q := by
  rw [cmEta32FormalSeries]
  simp only [map_mul, map_pow, PowerSeries.eval₂_X]
  rw [evalEtaEulerFormal4_eq hq, evalEtaEulerFormal8_eq hq]
  rw [cmEta32QProduct_eventually_eq_pentagonal] <;>
    simp only [Filter.EventuallyEq] at *
  exact (cmEta32QProduct_eventually_eq_pentagonal.self_of_nhds
    (Metric.isOpen_ball.mem_nhds (by simpa using hq))).symm

theorem hasSum_cmEta32FormalSeries
    {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum
      (fun n : ℕ => PowerSeries.coeff n cmEta32FormalSeries * q ^ n)
      (cmEta32QProduct q) := by
  have h := PowerSeries.hasSum_eval₂
    (continuous_id : Continuous (RingHom.id ℂ))
    (hasEval_of_norm_lt_one hq) cmEta32FormalSeries
  simpa [evalEta32Formal_eq_qProduct hq] using h

/-- A local coefficient sum on the unit disk determines an analytic F-power series. -/
theorem hasFPowerSeriesAt_of_hasSum_unitDisk
    {f : ℂ → ℂ} {c : ℕ → ℂ}
    (hsum : ∀ q : ℂ, ‖q‖ < 1 →
      HasSum (fun n : ℕ => c n * q ^ n) (f q)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ c) 0 := by
  have hball :
      HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ c) 0 1 := by
    constructor
    · refine le_of_forall_lt_imp_le_of_dense fun r hr => ?_
      rcases eq_or_ne r 0 with rfl | hr0
      · simp
      · lift r to NNReal using hr.ne_top
        letI : FiniteDimensional ℝ ℂ := basisOneI.finiteDimensional_of_finite
        apply FormalMultilinearSeries.le_radius_of_summable
        simpa [FormalMultilinearSeries.ofScalars_apply_eq, norm_mul, mul_comm] using
          (hsum (r : ℂ) (by simpa using hr)).summable.norm
    · simp
    · intro q hq
      rw [← ENNReal.coe_one, Metric.eball_coe, NNReal.coe_one,
        Metric.mem_ball, dist_zero_right] at hq
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] using hsum q hq
  exact hball.hasFPowerSeriesAt

theorem cmEta32_hasFormalPentagonalSeriesAt_zero :
    HasFPowerSeriesAt cmEta32QProduct
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => PowerSeries.coeff n cmEta32FormalSeries)) 0 := by
  apply hasFPowerSeriesAt_of_hasSum_unitDisk
  intro q hq
  exact hasSum_cmEta32FormalSeries hq

theorem cmEta32_formal_coeff_eq_TaylorCoeff (n : ℕ) :
    PowerSeries.coeff n cmEta32FormalSeries = cmEta32TaylorCoeff n := by
  have hEq := cmEta32_hasFormalPentagonalSeriesAt_zero.eq_formalMultilinearSeries
    cmEta32_hasCanonicalTaylorSeriesAt_zero
  have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) hEq
  simpa [FormalMultilinearSeries.coeff_ofScalars] using hc

theorem cmEta32TaylorCoeff_five :
    cmEta32TaylorCoeff 5 = -2 := by
  rw [← cmEta32_formal_coeff_eq_TaylorCoeff 5]
  exact cmEta32FormalSeries_coeff_five

theorem etaElliptic_agree_at_five :
    cmEta32TaylorCoeff 5 = cmEllipticCoefficientComplex 5 := by
  rw [cmEta32TaylorCoeff_five, cmEllipticCoefficientComplex_five]

end Synthesis.Millennium.BSD

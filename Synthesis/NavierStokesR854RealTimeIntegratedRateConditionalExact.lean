import Synthesis.NavierStokesR854RealTimeAffineRateConditionalExact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# NS R854 — same real-time selected-rate uniform negative integral

The source-selected rational initial rate r0, conservative Lipschitz L,
and explicit horizon T are the EXACT source constants of the original
Agda Round829/850/853/854 finite 3-4-5 Galerkin setup.

No rational-valued continuous-in-real-time fictitious trajectory is
introduced: the rate is an ordinary real function, integrable over
the exact real interval [0,T].  The unproved original R853 physical
source Lipschitz envelope remains an EXPLICIT hypothesis.

Under that hypothesis, the already-proved terminal rate cap
C=r0+L*T<0 dominates rate(t) for every t in [0,T], so its actual
Lebesgue interval integral is strictly negative.

This is a genuine measure-integral consumer of existing R854
pointwise real arithmetic, not merely arithmetic on a fake integral.
It does NOT construct the actual Galerkin ODE solution, identify
its R853/R408 rate, or imply a Clay global-regularity statement.

Attribution: classical integral monotonicity, Picard–Lindelöf;
the literal finite selected rate is original DASHI R829/R854 source.
Current-head Lean kernel acceptance remains pending.
-/

open MeasureTheory intervalIntegral

namespace Synthesis

noncomputable section

/-- The actual real-time R854 rate integral is negative once the
original real-time source envelope has been supplied. The integrand
and the integration interval are real, rather than rational. -/
theorem nsR854OriginalRealRateIntegralStrictlyNegative
    (rate : ℝ → ℝ)
    (hIntegrable :
      IntervalIntegrable rate volume (0 : ℝ) nsR854Horizon)
    (hOriginalRateEnvelope :
      ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
        rate t ≤ nsR854InitialRate + nsR854Lipschitz * t) :
    (∫ t in (0 : ℝ)..nsR854Horizon, rate t) < 0 := by
  let cap : ℝ :=
    nsR854InitialRate + nsR854Lipschitz * nsR854Horizon
  have hcapNegative : cap < 0 := by
    exact nsR854AffineFinalRate_neg
  have hrateCap :
      ∀ t ∈ Set.Icc (0 : ℝ) nsR854Horizon,
        rate t ≤ cap := by
    intro t ht
    have hsource := hOriginalRateEnvelope t ht
    have hmult :
        nsR854Lipschitz * t ≤
          nsR854Lipschitz * nsR854Horizon :=
      mul_le_mul_of_nonneg_left ht.2 nsR854Lipschitz_nonneg
    exact hsource.trans (add_le_add_left hmult nsR854InitialRate)
  have hcapIntegrable :
      IntervalIntegrable (fun _ : ℝ => cap) volume
        (0 : ℝ) nsR854Horizon :=
    continuous_const.intervalIntegrable _ _
  have hint :
      (∫ t in (0 : ℝ)..nsR854Horizon, rate t) ≤
      (∫ t in (0 : ℝ)..nsR854Horizon, cap) :=
    intervalIntegral.integral_mono_on
      nsR854Horizon_pos.le hIntegrable hcapIntegrable hrateCap
  have hcapIntegral :
      (∫ t in (0 : ℝ)..nsR854Horizon, cap) =
        nsR854Horizon * cap := by
    simp [intervalIntegral.integral_const, smul_eq_mul]
  have hstrict : nsR854Horizon * cap < 0 :=
    mul_neg_of_pos_of_neg nsR854Horizon_pos hcapNegative
  rw [hcapIntegral] at hint
  exact lt_of_le_of_lt hint hstrict

end

end Synthesis

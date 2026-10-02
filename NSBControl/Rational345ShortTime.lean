import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Rational 3-4-5 reserve witness: real short-time transport

Standard-analysis companion to Agda R828-R831.

It proves:
1. an explicit state-displacement bound plus a one-sided Lipschitz bound for
   the selected rate preserves strict negativity on a short interval;
2. a continuous strictly negative real rate has strictly negative interval
   integral on every nondegenerate interval.

It does not assert that the concrete radius-four Galerkin vector field already
inhabits these hypotheses. That concrete instantiation is the remaining
R830-real-ODE leaf.
-/

open Set
open scoped Interval

namespace NSBControl
namespace Rational345ShortTime

def initialRate : ℝ := -(28273644 : ℝ) / 125

def integerMargin : ℝ := 226189

def rateUpper : ℝ := -(226189 : ℝ) / 2

def odeComponentBound : ℝ := 5032512

def rateLipschitzBound : ℝ := 391309593930357307785216

def certifiedTime : ℝ :=
  (226189 : ℝ) / 3938540454339300631433585885184

theorem initialRate_exact : initialRate = -(28273644 : ℝ) / 125 := rfl

theorem initialRate_lt_negIntegerMargin :
    initialRate < -integerMargin := by
  norm_num [initialRate, integerMargin]

theorem certifiedTime_pos : 0 < certifiedTime := by
  norm_num [certifiedTime]

theorem rateUpper_neg : rateUpper < 0 := by
  norm_num [rateUpper]

theorem odeComponentBound_nonneg : 0 ≤ odeComponentBound := by
  norm_num [odeComponentBound]

theorem rateLipschitzBound_nonneg : 0 ≤ rateLipschitzBound := by
  norm_num [rateLipschitzBound]

theorem certifiedBudget_exact :
    rateLipschitzBound * odeComponentBound * certifiedTime
      = integerMargin / 2 := by
  norm_num [rateLipschitzBound, odeComponentBound, certifiedTime, integerMargin]

theorem certifiedBudget_le :
    rateLipschitzBound * odeComponentBound * certifiedTime
      ≤ integerMargin / 2 := by
  rw [certifiedBudget_exact]

/-- A reusable short-time sign theorem. -/
theorem rate_le_negativeHalfMargin
    {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    (L K margin T : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hmargin : 0 < margin)
    (hT : 0 ≤ T)
    (hinitial : rate u₀ ≤ -margin)
    (hdisp : ∀ t ∈ Icc (0 : ℝ) T, ‖u t - u₀‖ ≤ K * t)
    (hrate : ∀ x, rate x - rate u₀ ≤ L * ‖x - u₀‖)
    (hbudget : L * K * T ≤ margin / 2) :
    ∀ t ∈ Icc (0 : ℝ) T, rate (u t) ≤ -margin / 2 := by
  intro t ht
  have htT : t ≤ T := ht.2
  have hdisp_t := hdisp t ht
  have hrate_t := hrate (u t)
  have hLKt : L * (K * t) ≤ L * (K * T) := by
    gcongr
  have hstep : L * ‖u t - u₀‖ ≤ L * (K * t) := by
    gcongr
  have hgrowth : rate (u t) - rate u₀ ≤ margin / 2 := by
    calc
      rate (u t) - rate u₀ ≤ L * ‖u t - u₀‖ := hrate_t
      _ ≤ L * (K * t) := hstep
      _ ≤ L * (K * T) := hLKt
      _ ≤ margin / 2 := hbudget
  linarith

/-- Continuous strict negativity on a nondegenerate interval implies a
strictly negative ordinary interval integral. -/
theorem intervalIntegral_strictlyNegative
    {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T)
    (hcont : ContinuousOn f (Icc (0 : ℝ) T))
    (hneg : ∀ t ∈ Icc (0 : ℝ) T, f t < 0) :
    (∫ t in (0 : ℝ)..T, f t) < 0 := by
  have hcompare :
      (∫ t in (0 : ℝ)..T, f t) <
        ∫ _t in (0 : ℝ)..T, (0 : ℝ) := by
    refine intervalIntegral.integral_lt_integral_of_continuous_on_of_le_of_exists_lt
      hT hcont continuousOn_const ?_ ?_
    · intro t ht
      exact le_of_lt (hneg t ⟨le_of_lt ht.1, ht.2⟩)
    · refine ⟨0, ?_, ?_⟩
      · exact ⟨le_rfl, le_of_lt hT⟩
      · simpa using hneg 0 ⟨le_rfl, le_of_lt hT⟩
  simpa using hcompare

/-- Terminal transport theorem for the R828/R830 strategy. -/
theorem negativeIntegral_of_bootstrap
    {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    (L K margin T : ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hmargin : 0 < margin)
    (hT : 0 < T)
    (hinitial : rate u₀ ≤ -margin)
    (hdisp : ∀ t ∈ Icc (0 : ℝ) T, ‖u t - u₀‖ ≤ K * t)
    (hrate : ∀ x, rate x - rate u₀ ≤ L * ‖x - u₀‖)
    (hbudget : L * K * T ≤ margin / 2)
    (hcont : ContinuousOn (fun t => rate (u t)) (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, rate (u t)) < 0 := by
  have hnonnegT : 0 ≤ T := le_of_lt hT
  have hbound :=
    rate_le_negativeHalfMargin u u₀ rate L K margin T
      hL hK hmargin hnonnegT hinitial hdisp hrate hbudget
  apply intervalIntegral_strictlyNegative hT hcont
  intro t ht
  have hb := hbound t ht
  have hm2 : 0 < margin / 2 := by positivity
  linarith

end Rational345ShortTime
end NSBControl


namespace ConcreteConstants

/-- R828's exact constants discharge the generic short-time budget
definitionally/arithmeticly.  A concrete Galerkin trajectory only has to supply
the displacement, one-sided rate Lipschitz, and continuity hypotheses. -/
theorem negativeIntegral_from_R828_bounds
    {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    (hinitial : rate u₀ ≤ -integerMargin)
    (hdisp :
      ∀ t ∈ Set.Icc (0 : ℝ) certifiedTime,
        ‖u t - u₀‖ ≤ odeComponentBound * t)
    (hrate :
      ∀ x,
        rate x - rate u₀ ≤ rateLipschitzBound * ‖x - u₀‖)
    (hcont :
      ContinuousOn (fun t => rate (u t))
        (Set.Icc (0 : ℝ) certifiedTime)) :
    (∫ t in (0 : ℝ)..certifiedTime, rate (u t)) < 0 := by
  apply negativeIntegral_of_bootstrap
    u u₀ rate
    rateLipschitzBound odeComponentBound integerMargin certifiedTime
  · exact rateLipschitzBound_nonneg
  · exact odeComponentBound_nonneg
  · norm_num [integerMargin]
  · exact certifiedTime_pos
  · exact hinitial
  · exact hdisp
  · exact hrate
  · exact certifiedBudget_le
  · exact hcont

end ConcreteConstants

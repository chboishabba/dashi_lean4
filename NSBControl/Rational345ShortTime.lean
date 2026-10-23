import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import NSBControl.Rational345QuadraticODE
import NSBControl.Rational345ReserveWitness

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

open NSBControl.Rational345ShortTime

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


/-- The R828 budget is monotone in the time horizon: any positive local
interval no longer than `certifiedTime` inherits the certified half-margin
budget.  This is the form needed to compose with an arbitrary Picard interval;
there is no obligation to prove that the local solution exists all the way to
the particular rational endpoint chosen by the certificate. -/
theorem certifiedBudget_le_of_le_certifiedTime
    {T : ℝ}
    (hT : 0 ≤ T)
    (hTcert : T ≤ certifiedTime) :
    rateLipschitzBound * odeComponentBound * T
      ≤ integerMargin / 2 := by
  have hcoeff :
      0 ≤ rateLipschitzBound * odeComponentBound := by
    positivity
  calc
    rateLipschitzBound * odeComponentBound * T
        ≤ rateLipschitzBound * odeComponentBound * certifiedTime := by
          gcongr
    _ ≤ integerMargin / 2 := certifiedBudget_le

/-- Concrete R828 transport on any positive subinterval of the certified
horizon.  This removes the exact-horizon/existence-interval matching problem
from R830. -/
theorem negativeIntegral_from_R828_bounds_up_to
    {E : Type*} [NormedAddCommGroup E]
    (u : ℝ → E) (u₀ : E) (rate : E → ℝ)
    (T : ℝ)
    (hT : 0 < T)
    (hTcert : T ≤ certifiedTime)
    (hinitial : rate u₀ ≤ -integerMargin)
    (hdisp :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ‖u t - u₀‖ ≤ odeComponentBound * t)
    (hrate :
      ∀ x,
        rate x - rate u₀ ≤ rateLipschitzBound * ‖x - u₀‖)
    (hcont :
      ContinuousOn (fun t => rate (u t))
        (Set.Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, rate (u t)) < 0 := by
  apply negativeIntegral_of_bootstrap
    u u₀ rate
    rateLipschitzBound odeComponentBound integerMargin T
  · exact rateLipschitzBound_nonneg
  · exact odeComponentBound_nonneg
  · norm_num [integerMargin]
  · exact hT
  · exact hinitial
  · exact hdisp
  · exact hrate
  · exact certifiedBudget_le_of_le_certifiedTime (le_of_lt hT) hTcert
  · exact hcont

end ConcreteConstants


namespace NSBControl
namespace Rational345RealSource

open Set
open scoped Interval

/--
The exact rational eight-output snapshot is transported to the REAL scalar
used by the real-time Galerkin flow. This is a theorem about the original
rational rate, not an invented rational-valued time trajectory.
-/
theorem snapshot_rate_real_exact :
    (Rational345ReserveWitness.canonicalSignedRate : ℝ) =
      Rational345ShortTime.initialRate := by
  rw [Rational345ReserveWitness.canonicalSignedRate_exact]
  norm_num [Rational345ShortTime.initialRate]

theorem snapshot_rate_real_negative :
    (Rational345ReserveWitness.canonicalSignedRate : ℝ) < 0 := by
  rw [snapshot_rate_real_exact]
  norm_num [Rational345ShortTime.initialRate]

/-- Native source-row calculation agrees with the real initial-rate constant. -/
theorem physical_rows_real_initial_rate :
    Rational345ReserveWitness.selectedRealRateFromSourceRows =
      Rational345ShortTime.initialRate := by
  rw [Rational345ReserveWitness.selectedRealRateFromSourceRows_eq_cast,
      snapshot_rate_real_exact]

theorem physical_rows_real_initial_rate_negative :
    Rational345ReserveWitness.selectedRealRateFromSourceRows < 0 := by
  rw [physical_rows_real_initial_rate]
  norm_num [Rational345ShortTime.initialRate]

/--
One analytic transport for the existing R828 witness:
* the flow is the REAL local ODE of a linear+bounded-bilinear field;
* rate is a continuous REAL observable on precisely that same state;
* its initial value is identified with the EXACT rational R829/R850 seed.

No quantitative Lipschitz/rate-budget premise and no prescribed interval:
the positive interval comes directly from local Picard and continuity.
The physical bridge still required is to identify the linear/quadratic
field and real rate with the literal R408/R823 Fourier definitions.
-/
theorem exists_real_negative_signed_integral
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear)
    (seed : E)
    (rate : E → ℝ)
    (hrate : Continuous rate)
    (hseed :
      rate seed = Rational345ReserveWitness.selectedRealRateFromSourceRows) :
    ∃ (u : ℝ → E) (T : ℝ),
      0 < T ∧
      u 0 = seed ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt u (linear (u t) + bilinear (u t, u t)) t) ∧
      (∫ t in (0 : ℝ)..T, rate (u t)) < 0 := by
  obtain ⟨u, hu0, ε, hε, huODE⟩ :=
    Rational345QuadraticODE.exists_local_solution_quadraticField
      linear bilinear hbilinear seed
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have huCont0 : ContinuousAt u 0 :=
    (huODE 0 hzero).continuousAt
  have hRateAtZero : rate (u 0) < 0 := by
    rw [hu0, hseed]
    exact physical_rows_real_initial_rate_negative
  have hnear : {t : ℝ | rate (u t) < 0} ∈ nhds (0 : ℝ) := by
    exact (hrate.continuousAt.comp huCont0).preimage_mem_nhds
      (isOpen_Iio.mem_nhds hRateAtZero)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  let T : ℝ := min (ε / 2) (δ / 2)
  have hTpos : 0 < T := by
    dsimp [T]
    apply lt_min <;> linarith
  have htODE : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∈ Set.Ioo (-ε) ε := by
    intro t ht
    dsimp [T] at ht
    constructor
    · linarith [ht.1]
    · have hupper : t ≤ ε / 2 :=
        le_trans ht.2 (min_le_left _ _)
      linarith
  have hrateNeg : ∀ t ∈ Set.Icc (0 : ℝ) T, rate (u t) < 0 := by
    intro t ht
    apply hδball
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_nonneg ht.1]
    have hupper : t ≤ δ / 2 :=
      le_trans ht.2 (min_le_right _ _)
    linarith
  have hcont : ContinuousOn (fun t : ℝ => rate (u t))
      (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hrate.continuousAt.comp (huODE t (htODE t ht)).continuousAt)
      .continuousWithinAt
  refine ⟨u, T, hTpos, hu0, ?_, ?_⟩
  · intro t ht
    exact huODE t (htODE t ht)
  · exact Rational345ShortTime.intervalIntegral_strictlyNegative
      hTpos hcont hrateNeg

/--
R823's finite signed reserve-minus-demand algebra is valid over the REAL
codomain. This is not the R815-to-R823 physical source-identification
theorem; that equality needs the same real Fourier state on both sides.
-/
theorem signed_reserve_sub_demand_real
    (nonlinear quintic core dissipation : ℝ) :
    2 * (9 * nonlinear - quintic) + core + 6 * dissipation
      = (core + 6 * dissipation) -
        2 * (quintic - 9 * nonlinear) := by
  ring

end Rational345RealSource
end NSBControl


namespace NSBControl
namespace Rational345RealSource

/--
The R823 reserve-vs-demand logical endpoint, now over the genuine real
integral. This uses exactly the same selected real rate/terminal: an
unrelated signed witness cannot be substituted.
-/
theorem negative_real_integral_refutes_reserve
    {actualIntegral signedReserve integratedDemand : ℝ}
    (hnegative : actualIntegral < 0)
    (hsame : actualIntegral = signedReserve - integratedDemand) :
    ¬ (integratedDemand ≤ signedReserve) := by
  intro hpays
  have hnonneg : 0 ≤ actualIntegral := by
    rw [hsame]
    linarith
  exact (not_le_of_gt hnegative) hnonneg

end Rational345RealSource
end NSBControl


namespace NSBControl
namespace Rational345RealSource

/-!
## Direct physical-component acceptance theorem for the R850 seed

The actual selected physical rate is the R853 normal form
  6*(12*C-P+D) at nu=delta=1.
R850 proves the individual Q seed quantities; the REAL Fourier evaluator
must preserve their values under the Q-to-R seed embedding. A generic
scalar matching premise is replaced by the three concrete component
equations, exactly corresponding to the Agda theorem owners.
-/

/-- Real normal-form rate on the SAME physical state. -/
def physicalSelectedRate {E : Type*}
    (coherent production dissipation : E → ℝ) (u : E) : ℝ :=
  6 * (12 * coherent u - production u + dissipation u)

/-- The three real source components determine the exact R850 initial rate. -/
theorem physicalSelectedRate_seed_exact
    {E : Type*}
    (coherent production dissipation : E → ℝ)
    (seed : E)
    (hcoherent :
      coherent seed = Rational345ReserveWitness.realCoherentWork)
    (hproduction :
      production seed = Rational345ReserveWitness.realCriticalProduction)
    (hdissipation :
      dissipation seed = Rational345ReserveWitness.realCriticalDissipation) :
    physicalSelectedRate coherent production dissipation seed =
      Rational345ReserveWitness.selectedRealRateFromSourceRows := by
  simp only [physicalSelectedRate, hcoherent, hproduction, hdissipation,
    Rational345ReserveWitness.selectedRealRateFromSourceRows]

/--
Combines precisely the existing real quadratic local-flow theorem, R850's
THREE physical initial components after exact row casting, and the R853
normal-form scalar on the SAME finite state. No artificial rational-time
trajectory or fixed horizon.

The physical-input proof that remains is to construct the three concrete
REAL Fourier observables and match the actual radius-four seed to them.
The R823 signed reserve identity along this REAL flow remains an additional
source-semantics requirement for promotion of the auxiliary refutation.
-/
theorem exists_negative_integral_from_R850_components
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear)
    (seed : E)
    (coherent production dissipation : E → ℝ)
    (hcoherentCont : Continuous coherent)
    (hproductionCont : Continuous production)
    (hdissipationCont : Continuous dissipation)
    (hcoherentSeed :
      coherent seed = Rational345ReserveWitness.realCoherentWork)
    (hproductionSeed :
      production seed = Rational345ReserveWitness.realCriticalProduction)
    (hdissipationSeed :
      dissipation seed = Rational345ReserveWitness.realCriticalDissipation) :
    ∃ (u : ℝ → E) (T : ℝ),
      0 < T ∧
      u 0 = seed ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt u (linear (u t) + bilinear (u t, u t)) t) ∧
      (∫ t in (0 : ℝ)..T,
        physicalSelectedRate coherent production dissipation (u t)) < 0 := by
  have hcont :
      Continuous (physicalSelectedRate coherent production dissipation) := by
    unfold physicalSelectedRate
    fun_prop
  have hseed :=
    physicalSelectedRate_seed_exact coherent production dissipation seed
      hcoherentSeed hproductionSeed hdissipationSeed
  exact exists_real_negative_signed_integral
    linear bilinear hbilinear seed
    (physicalSelectedRate coherent production dissipation)
    hcont hseed

end Rational345RealSource
end NSBControl

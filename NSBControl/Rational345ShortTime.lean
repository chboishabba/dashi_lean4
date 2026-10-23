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


namespace NSBControl
namespace Rational345RealSource

/-!
R853/R823 SAME-STATE REAL INTEGRATION.
The Agda R853 theorem already proves the finite signed-orbit identity on
its rational packet. In the REAL codomain, the *only* source-specific premise
below is that the identical physical Fourier finite-sum identity holds for
the real Galerkin state's coherent, production, dissipation, nested, quotient
and core terms. It must not be inferred from a Q-valued trajectory.
-/

def realSignedReserveRate {E : Type*}
    (core dissipation : E → ℝ) (x : E) : ℝ :=
  core x + 6 * dissipation x

def realSignedDemandRate {E : Type*}
    (nested quotient : E → ℝ) (x : E) : ℝ :=
  2 * (quotient x - 9 * nested x)

/-- Pointwise R853 is precisely the missing source equation, not a new
    inequality or a second independent signed observable. -/
theorem realR823_from_R853_pointwise
    {E : Type*}
    (coherent production dissipation nested quotient core : E → ℝ)
    (hR853 : ∀ x : E,
      2 * (9 * nested x - quotient x) + core x =
        6 * (12 * coherent x - production x))
    (x : E) :
    realSignedReserveRate core dissipation x -
      realSignedDemandRate nested quotient x =
      physicalSelectedRate coherent production dissipation x := by
  unfold realSignedReserveRate realSignedDemandRate physicalSelectedRate
  have h := hR853 x
  linarith

/-- Real interval integrals of the reserve and demand agree with the SAME
    selected R853 signed-rate integral, using actual integral linearity. -/
theorem realR823_R853_integral_on_same_flow
    {E : Type*}
    (u : ℝ → E) (T : ℝ)
    (coherent production dissipation nested quotient core : E → ℝ)
    (hR853 : ∀ x : E,
      2 * (9 * nested x - quotient x) + core x =
        6 * (12 * coherent x - production x))
    (hreserve : IntervalIntegrable
      (fun t : ℝ => realSignedReserveRate core dissipation (u t))
      MeasureTheory.volume 0 T)
    (hdemand : IntervalIntegrable
      (fun t : ℝ => realSignedDemandRate nested quotient (u t))
      MeasureTheory.volume 0 T) :
    (∫ t in (0 : ℝ)..T,
      physicalSelectedRate coherent production dissipation (u t)) =
    (∫ t in (0 : ℝ)..T, realSignedReserveRate core dissipation (u t)) -
    (∫ t in (0 : ℝ)..T, realSignedDemandRate nested quotient (u t)) := by
  have hfunctions :
      (fun t : ℝ => physicalSelectedRate coherent production dissipation (u t)) =
      (fun t : ℝ => realSignedReserveRate core dissipation (u t) -
        realSignedDemandRate nested quotient (u t)) := by
    funext t
    exact (realR823_from_R853_pointwise
      coherent production dissipation nested quotient core hR853 (u t)).symm
  rw [hfunctions]
  exact intervalIntegral.integral_sub hreserve hdemand

/-- This theorem is the complete REAL analytic + integrated signed-reserve
    max-cut, with the source-specific R853 same-real-Fourier-operator law
    represented as ONE explicit input (the literal geometric lift).
    The three seed components are exactly R850, not arbitrary rate data. -/
theorem exists_negative_real_R823_reserve_difference
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (linear : E →L[ℝ] E)
    (bilinear : E × E → E)
    (hbilinear : IsBoundedBilinearMap ℝ bilinear)
    (seed : E)
    (coherent production dissipation nested quotient core : E → ℝ)
    (hcoherentCont : Continuous coherent)
    (hproductionCont : Continuous production)
    (hdissipationCont : Continuous dissipation)
    (hnestedCont : Continuous nested)
    (hquotientCont : Continuous quotient)
    (hcoreCont : Continuous core)
    (hcoherentSeed :
      coherent seed = Rational345ReserveWitness.realCoherentWork)
    (hproductionSeed :
      production seed = Rational345ReserveWitness.realCriticalProduction)
    (hdissipationSeed :
      dissipation seed = Rational345ReserveWitness.realCriticalDissipation)
    (hR853 : ∀ x : E,
      2 * (9 * nested x - quotient x) + core x =
        6 * (12 * coherent x - production x)) :
    ∃ (u : ℝ → E) (T : ℝ),
      0 < T ∧ u 0 = seed ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt u (linear (u t) + bilinear (u t, u t)) t) ∧
      ¬ ((∫ t in (0 : ℝ)..T, realSignedDemandRate nested quotient (u t)) ≤
          (∫ t in (0 : ℝ)..T, realSignedReserveRate core dissipation (u t))) := by
  obtain ⟨u, T, hT, hu0, hODE, hnegative⟩ :=
    exists_negative_integral_from_R850_components
      linear bilinear hbilinear seed coherent production dissipation
      hcoherentCont hproductionCont hdissipationCont
      hcoherentSeed hproductionSeed hdissipationSeed
  have huCont : ContinuousOn u (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (hODE t ht).continuousAt.continuousWithinAt
  have hrcont : ContinuousOn
      (fun t : ℝ => realSignedReserveRate core dissipation (u t))
      (Set.Icc (0 : ℝ) T) := by
    change ContinuousOn (fun t : ℝ => core (u t) + 6 * dissipation (u t)) _
    exact (hcoreCont.comp_continuousOn huCont).add
      ((hdissipationCont.comp_continuousOn huCont).const_mul _)
  have hdcont : ContinuousOn
      (fun t : ℝ => realSignedDemandRate nested quotient (u t))
      (Set.Icc (0 : ℝ) T) := by
    change ContinuousOn (fun t : ℝ => 2 * (quotient (u t) - 9 * nested (u t))) _
    exact ((hquotientCont.comp_continuousOn huCont).sub
      ((hnestedCont.comp_continuousOn huCont).const_mul _)).const_mul _
  have hrint : IntervalIntegrable
      (fun t : ℝ => realSignedReserveRate core dissipation (u t))
      MeasureTheory.volume 0 T :=
    hrcont.intervalIntegrable_of_Icc (le_of_lt hT)
  have hdint : IntervalIntegrable
      (fun t : ℝ => realSignedDemandRate nested quotient (u t))
      MeasureTheory.volume 0 T :=
    hdcont.intervalIntegrable_of_Icc (le_of_lt hT)
  have hsame := realR823_R853_integral_on_same_flow u T
    coherent production dissipation nested quotient core hR853 hrint hdint
  refine ⟨u, T, hT, hu0, hODE, ?_⟩
  exact negative_real_integral_refutes_reserve hnegative hsame

end Rational345RealSource
end NSBControl


namespace NSBControl
namespace Rational345RealSource

/-!
## Literal real-helical signed-rate observables on the eight-mode chart

These are the actual finite Fourier definitions used by the independent
full-physical 728-mode snapshot evaluator. They are now bound to precisely
the SAME eight-complex-vector state and RHS as the Lean Galerkin ODE,
not to unrelated real functions. This is the concrete source of C, P, D
in the R853 normal form.
-/

open Rational345QuadraticODE

abbrev RealFourierState345 := PhysicalEightModeState
abbrev RealFourierVector345 := FourierVector345
abbrev FourierMode345 := Mode345

/-- Euclidean square length of the physical Fourier mode. -/
def physicalModeNormSq345 (k : FourierMode345) : ℝ :=
  ∑ i : Fin 3, (k i : ℝ) ^ 2

/-- Physical three-dimensional Fourier cross product k cross v. -/
def physicalModeCross345
    (k : FourierMode345) (v : RealFourierVector345) :
    RealFourierVector345 :=
  ![(k 1 : ℂ) * v 2 - (k 2 : ℂ) * v 1,
    (k 2 : ℂ) * v 0 - (k 0 : ℂ) * v 2,
    (k 0 : ℂ) * v 1 - (k 1 : ℂ) * v 0]

/-- Genuine real-mode Leray projection on each physical Fourier vector. -/
def physicalLeray345
    (k : FourierMode345) (v : RealFourierVector345) :
    RealFourierVector345 :=
  fun j => v j - (k j : ℂ) *
    (∑ i : Fin 3, (k i : ℂ) * v i) /
    (∑ i : Fin 3, (k i : ℂ) * (k i : ℂ))

/-- Real physical helical modes H± = (Pv ± i k×v / |k|)/2. -/
def physicalHelical345
    (positive : Bool)
    (k : FourierMode345) (v : RealFourierVector345) :
    RealFourierVector345 :=
  let norm : ℝ := Real.sqrt (physicalModeNormSq345 k)
  let dir : ℂ := if positive then Complex.I else -Complex.I
  fun j => (physicalLeray345 k v j +
    dir * physicalModeCross345 k v j / (norm : ℂ)) / 2

/-- Non-viscous physical projected quadratic forcing at an arbitrary mode. -/
def physicalProjectedForce345
    (u : RealFourierState345) (k : FourierMode345) :
    RealFourierVector345 :=
  projectedNonlinearMode345 k
    ((selected345ModeFinset.product selected345ModeFinset).sum
      (fun pq =>
        if pq.1 + pq.2 = k then
          rawFourierTriad345 pq.2
            (extendPhysicalEight u pq.1)
            (extendPhysicalEight u pq.2)
        else 0))

/-- Complex-vector cross product. -/
def physicalCrossVec345
    (a b : RealFourierVector345) : RealFourierVector345 :=
  ![a 1 * b 2 - a 2 * b 1,
    a 2 * b 0 - a 0 * b 2,
    a 0 * b 1 - a 1 * b 0]

/-- Complete actual mixed helical output from supported pairs. -/
def physicalMixedOutput345
    (u : RealFourierState345) (k : FourierMode345) :
    RealFourierVector345 :=
  (selected345ModeFinset.product selected345ModeFinset).sum
    (fun pq => if pq.1 + pq.2 = k then
      physicalCrossVec345
        (physicalHelical345 true pq.1
          (extendPhysicalEight u pq.1))
        (physicalHelical345 false pq.2
          (extendPhysicalEight u pq.2))
      else 0)

/-- Complete actual R230 forcing commutator at a fixed output. -/
def physicalCommutatorOutput345
    (u : RealFourierState345) (k : FourierMode345) :
    RealFourierVector345 :=
  (selected345ModeFinset.product selected345ModeFinset).sum
    (fun pq => if pq.1 + pq.2 = k then
      physicalCrossVec345
        (physicalHelical345 true pq.1 (physicalProjectedForce345 u pq.1))
        (physicalHelical345 false pq.2 (extendPhysicalEight u pq.2))
      -
      physicalCrossVec345
        (physicalHelical345 false pq.1 (physicalProjectedForce345 u pq.1))
        (physicalHelical345 true pq.2 (extendPhysicalEight u pq.2))
      else 0)

/-- The same physical coherent Hermitian real work as the Agda R692 owner. -/
def physicalCoherentWork345 (u : RealFourierState345) : ℝ :=
  ∑ k in selected345ModeFinset,
    2 * (∑ j : Fin 3,
      (Complex.conj (physicalMixedOutput345 u k j) *
        physicalCommutatorOutput345 u k j).re)

/-- All selected modes have dyadic critical weight four. -/
def physicalProduction345 (u : RealFourierState345) : ℝ :=
  ∑ k ∈ selected345ModeFinset,
    8 * (∑ j : Fin 3,
      (Complex.conj (extendPhysicalEight u k j) *
        physicalProjectedForce345 u k j).re)

def physicalDissipation345 (u : RealFourierState345) : ℝ :=
  ∑ k ∈ selected345ModeFinset,
    4 * physicalModeNormSq345 k *
      (∑ j : Fin 3, Complex.normSq (extendPhysicalEight u k j))

/-- The *literal real Fourier* R853 selected rate, not a free rate argument. -/
def physicalSelectedSignedRate345 (u : RealFourierState345) : ℝ :=
  physicalSelectedRate physicalCoherentWork345
    physicalProduction345 physicalDissipation345 u

theorem physicalSelectedSignedRate345_is_R853_formula
    (u : RealFourierState345) :
    physicalSelectedSignedRate345 u =
      6 * (12 * physicalCoherentWork345 u -
        physicalProduction345 u + physicalDissipation345 u) := by
  rfl

end Rational345RealSource
end NSBControl


namespace NSBControl
namespace Rational345RealSource

/-!
## The literal rational 3-4-5 physical initial state

Mode order is exactly selected345ModeAt:
  (-3,-4),(-3,0),(-3,4),(0,-4),(0,4),(3,-4),(3,0),(3,4).
This is the same six-mode velocity seed used in the Agda R841/R850
physical system and the independent 728-mode exact-source evaluator.
All values are actual complex Fourier amplitudes with explicit conjugacy.
-/

def physical345Seed : RealFourierState345 :=
  fun j =>
    if j.val = 0 then
      ![-6 * Complex.I, (9 / 2 : ℂ) * Complex.I, -2 - 2 * Complex.I]
    else if j.val = 1 then
      ![0, 2 - 2 * Complex.I, -2 + Complex.I]
    else if j.val = 2 then 0
    else if j.val = 3 then
      ![2 - 2 * Complex.I, 0, 2 - 2 * Complex.I]
    else if j.val = 4 then
      ![2 + 2 * Complex.I, 0, 2 + 2 * Complex.I]
    else if j.val = 5 then 0
    else if j.val = 6 then
      ![0, 2 + 2 * Complex.I, -2 - Complex.I]
    else
      ![6 * Complex.I, -(9 / 2 : ℂ) * Complex.I, -2 + 2 * Complex.I]

/-- The 3-4-5 seed remains inside the same eight-mode Fourier chart,
    including the two initially empty off-diagonal active-output modes. -/
theorem physical345Seed_empty_cross_modes :
    physical345Seed ⟨2, by decide⟩ = 0 ∧
    physical345Seed ⟨5, by decide⟩ = 0 := by
  constructor <;> rfl

/-- The six actual nonzero-mode entries (not a scalar surrogate) are
    reproduced definitionally in the physical eight-mode chart. -/
theorem physical345Seed_positive_inputs :
    physical345Seed ⟨4, by decide⟩ =
      ![2 + 2 * Complex.I, 0, 2 + 2 * Complex.I] ∧
    physical345Seed ⟨6, by decide⟩ =
      ![0, 2 + 2 * Complex.I, -2 - Complex.I] ∧
    physical345Seed ⟨7, by decide⟩ =
      ![6 * Complex.I, -(9 / 2 : ℂ) * Complex.I,
        -2 + 2 * Complex.I] := by
  constructor
  · rfl
  constructor <;> rfl

/--
These are the literal real-operator seed receipts required to instantiate
the existing negative real-time integral theorem. They are now concrete
closed propositions over the genuine eight-mode source, not fresh
uninterpreted observation symbols. Their exact values are independently
recomputed by the physical SymPy evaluator; kernel proofs of these three
finite definitions still need to be supplied before closure is promoted.
-/
def RealPhysicalSeedReceipt : Prop :=
  physicalCoherentWork345 physical345Seed =
      Rational345ReserveWitness.realCoherentWork ∧
  physicalProduction345 physical345Seed =
      Rational345ReserveWitness.realCriticalProduction ∧
  physicalDissipation345 physical345Seed =
      Rational345ReserveWitness.realCriticalDissipation

end Rational345RealSource
end NSBControl


namespace NSBControl
namespace Rational345RealSource

/-!
## Real negative integral for the LITERAL eight-mode Fourier Galerkin flow

No arbitrary field or rate is supplied: both are the concrete selected
physical Leray/Galerkin finite-source definitions above. This theorem
requires only the remaining exact rational-to-real finite seed-evaluation
receipt; the physical real R853 signed-orbit identity is a separate
pointwise finite-source equality needed only to refute R823.
-/

theorem physicalSelectedSignedRate345_continuous :
    Continuous physicalSelectedSignedRate345 := by
  unfold physicalSelectedSignedRate345 physicalSelectedRate
    physicalCoherentWork345 physicalProduction345 physicalDissipation345
    physicalMixedOutput345 physicalCommutatorOutput345
    physicalProjectedForce345 physicalHelical345 physicalLeray345
    physicalModeCross345 physicalCrossVec345 physicalModeNormSq345
    Rational345QuadraticODE.extendPhysicalEight
    Rational345QuadraticODE.rawFourierTriad345
    Rational345QuadraticODE.projectedNonlinearMode345
  fun_prop

/-- A local real solution of the ACTUAL eight-mode Galerkin equation has
    strictly negative physical R853 selected-rate integral, conditional
    solely on the finite actual seed Fourier evaluation receipt. -/
theorem physical345_real_negative_integral_of_seed_receipt
    (hseed : RealPhysicalSeedReceipt) :
    ∃ (u : ℝ → RealFourierState345) (T : ℝ),
      0 < T ∧
      u 0 = physical345Seed ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivAt u
          (Rational345QuadraticODE.physicalEightModeField (u t)) t) ∧
      (∫ t in (0 : ℝ)..T, physicalSelectedSignedRate345 (u t)) < 0 := by
  obtain ⟨u, hu0, ε, hε, hODE⟩ :=
    Rational345QuadraticODE.physicalEightModeField_real_local_solution
      physical345Seed
  rcases hseed with ⟨hcoherent, hproduction, hdissipation⟩
  have hnegativeSeed : physicalSelectedSignedRate345 physical345Seed < 0 := by
    have hsame := physicalSelectedRate_seed_exact
      physicalCoherentWork345 physicalProduction345 physicalDissipation345
      physical345Seed hcoherent hproduction hdissipation
    rw [physicalSelectedSignedRate345, hsame]
    exact Rational345ReserveWitness.selectedRealRateFromSourceRows_negative
  have hzero : (0 : ℝ) ∈ Set.Ioo (-ε) ε := by
    constructor <;> linarith
  have huCont0 : ContinuousAt u 0 :=
    (hODE 0 hzero).continuousAt
  have hRateAtZero : physicalSelectedSignedRate345 (u 0) < 0 := by
    rw [hu0]
    exact hnegativeSeed
  have hnear :
      {t : ℝ | physicalSelectedSignedRate345 (u t) < 0} ∈ nhds (0 : ℝ) := by
    exact (physicalSelectedSignedRate345_continuous.continuousAt.comp huCont0)
      .preimage_mem_nhds (isOpen_Iio.mem_nhds hRateAtZero)
  obtain ⟨δ, hδ, hδball⟩ := Metric.mem_nhds_iff.mp hnear
  let T : ℝ := min (ε / 2) (δ / 2)
  have hTpos : 0 < T := by
    dsimp [T]
    apply lt_min <;> linarith
  have htODE : ∀ t ∈ Set.Icc (0 : ℝ) T, t ∈ Set.Ioo (-ε) ε := by
    intro t ht
    constructor
    · linarith [ht.1]
    · have hupper : t ≤ ε / 2 := le_trans ht.2 (min_le_left _ _)
      linarith
  have hrateNeg :
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        physicalSelectedSignedRate345 (u t) < 0 := by
    intro t ht
    apply hδball
    rw [Metric.mem_ball, Real.dist_0_eq_abs, abs_of_nonneg ht.1]
    have hupper : t ≤ δ / 2 := le_trans ht.2 (min_le_right _ _)
    linarith
  have hcont : ContinuousOn
      (fun t : ℝ => physicalSelectedSignedRate345 (u t))
      (Set.Icc (0 : ℝ) T) := by
    intro t ht
    exact (physicalSelectedSignedRate345_continuous.continuousAt.comp
      (hODE t (htODE t ht)).continuousAt).continuousWithinAt
  refine ⟨u, T, hTpos, hu0, ?_, ?_⟩
  · intro t ht
    exact hODE t (htODE t ht)
  · exact Rational345ShortTime.intervalIntegral_strictlyNegative
      hTpos hcont hrateNeg

end Rational345RealSource
end NSBControl

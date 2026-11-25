import Integration.MoonshineDeltaFinalMinCut
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
Paper 9, source-written, NOT compiled.
Use the actual pinned modular forms and their Mathlib cusp functions.
Do not infer analytic slash/cusp packaging or Agda proof replay from
these coefficient and algebra lemmas.
-/
namespace Integration.Paper9OriginalEisensteinDerivative

open Function Complex Filter
open UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass
open EisensteinSeries
open scoped MatrixGroups Topology Real

noncomputable section

namespace A
open Integration.MoonshineEisensteinAnalytic
end A
namespace T
open Integration.MoonshineEisensteinAgdaTarget
end T
namespace Delta
open Integration.MoonshineDeltaIdentityPinned
end Delta
namespace Eta
open Integration.MoonshineEta24CuspPinned
end Eta
namespace Scalar
open Integration.MoonshineWeight12Eta24ScalarPinned
end Scalar
namespace Final
open Integration.MoonshineDeltaFinalMinCut
end Final

def x (q : ℂ) : ℂ := cuspFunction 1 A.E4 q
def y (q : ℂ) : ℂ := cuspFunction 1 A.E6 q

theorem xAnalyticZero : AnalyticAt ℂ x 0 :=
  analyticAt_cuspFunction_zero A.E4 one_pos one_mem_strictPeriods_SL

theorem yAnalyticZero : AnalyticAt ℂ y 0 :=
  analyticAt_cuspFunction_zero A.E6 one_pos one_mem_strictPeriods_SL

theorem xDifferentiable (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ x q :=
  differentiableAt_cuspFunction A.E4 one_pos one_mem_strictPeriods_SL hq

theorem yDifferentiable (q : ℂ) (hq : ‖q‖ < 1) :
    DifferentiableAt ℂ y q :=
  differentiableAt_cuspFunction A.E6 one_pos one_mem_strictPeriods_SL hq

-- Same normalized Mathlib objects, not a second Fourier evaluator.
theorem xAtQ (τ : ℍ) : x (Periodic.qParam 1 τ) = A.E4 τ :=
  eq_cuspFunction A.E4 τ one_mem_strictPeriods_SL one_ne_zero

theorem yAtQ (τ : ℍ) : y (Periodic.qParam 1 τ) = A.E6 τ :=
  eq_cuspFunction A.E6 τ one_mem_strictPeriods_SL one_ne_zero

theorem e4Coeff0 : (qExpansion 1 A.E4).coeff 0 = 1 := by
  simpa [A.E4] using
    (EisensteinSeries.E_qExpansion_coeff_zero (k := 4)
      (by norm_num : 3 ≤ 4) (by norm_num : Even 4))

theorem e6Coeff0 : (qExpansion 1 A.E6).coeff 0 = 1 := by
  simpa [A.E6] using
    (EisensteinSeries.E_qExpansion_coeff_zero (k := 6)
      (by norm_num : 3 ≤ 6) (by norm_num : Even 6))

theorem e4Coeff1 : (qExpansion 1 A.E4).coeff 1 = 240 := by
  rw [EisensteinSeries.E_qExpansion_coeff (k := 4)
    (by norm_num : 3 ≤ 4) (by norm_num : Even 4) (m := 1)]
  norm_num [show bernoulli 4 = -1 / 30 by decide +kernel]

theorem e6Coeff1 : (qExpansion 1 A.E6).coeff 1 = -504 := by
  rw [EisensteinSeries.E_qExpansion_coeff (k := 6)
    (by norm_num : 3 ≤ 6) (by norm_num : Even 6) (m := 1)]
  norm_num [show bernoulli 6 = 1 / 42 by decide +kernel]

theorem xZero : x 0 = 1 := by
  simpa [qExpansion_coeff, x] using e4Coeff0

theorem yZero : y 0 = 1 := by
  simpa [qExpansion_coeff, y] using e6Coeff0

theorem xDerivZero : deriv x 0 = 240 := by
  simpa [qExpansion_coeff, x] using e4Coeff1

theorem yDerivZero : deriv y 0 = -504 := by
  simpa [qExpansion_coeff, y] using e6Coeff1

def euler (f : ℂ → ℂ) (q : ℂ) : ℂ := q * deriv f q

-- Actual cusp-coordinate derivative bracket, including the zero mode.
def bracketQ (q : ℂ) : ℂ :=
  3 * y q * euler x q - 2 * x q * euler y q

def bracketUnit (q : ℂ) : ℂ := 3 * y q * deriv x q - 2 * x q * deriv y q

theorem bracketFactor (q : ℂ) : bracketQ q = q * bracketUnit q := by
  unfold bracketQ bracketUnit euler
  ring

theorem bracketZero : bracketQ 0 = 0 := by simp [bracketFactor]

theorem bracketUnitZero : bracketUnit 0 = 1728 := by
  rw [bracketUnit, xZero, yZero, xDerivZero, yDerivZero]
  norm_num

theorem bracketHasDerivAtZero : HasDerivAt bracketQ 1728 0 := by
  have ha : AnalyticAt ℂ bracketUnit 0 := by
    unfold bracketUnit
    exact ((analyticAt_const.mul yAnalyticZero).mul xAnalyticZero.deriv).sub
      ((analyticAt_const.mul xAnalyticZero).mul yAnalyticZero.deriv)
  have hd := ha.differentiableAt.hasDerivAt
  have hp := (hasDerivAt_id (0 : ℂ)).mul hd
  convert hp using 1
  · funext q
    exact bracketFactor q
  · simp [bracketUnitZero]

-- Need actual analytic slash action and cusp packaging: no arbitrary
-- bracket value is accepted. This consumer is deliberately conditional.
theorem bracketCuspValue (f : CuspForm 𝒮ℒ 12)
    (hc : (qExpansion 1 f).coeff 1 = 1728) (τ : ℍ) :
    f τ = 1728 * T.normalizedDeltaLimit τ := by
  obtain ⟨c, h⟩ := Scalar.exists_smul_eta24 f
  have hfun : (c • Eta.eta24CuspForm : ℍ → ℂ) = (f : ℍ → ℂ) :=
    congrArg DFunLike.coe h
  have hq := ModularForm.qExpansion_smul
    one_pos one_mem_strictPeriods_SL c Eta.eta24CuspForm
  rw [hfun] at hq
  have hcoeff := congrArg (fun p : PowerSeries ℂ => p.coeff 1) hq
  have hc' : c = 1728 := by
    simpa [PowerSeries.coeff_smul, Eta.eta24_qExpansion_coeff_one, hc]
      using hcoeff.symm
  subst c
  have hz := congrArg (fun g : CuspForm 𝒮ℒ 12 => g τ) h
  simpa [Delta.eta24_eq_normalizedDelta] using hz.symm

-- Pointwise original target values. The differential inputs are tied
-- to the actual q functions, not free replacement scalar sequences.
def dx (τ : ℍ) : ℂ := euler x (Periodic.qParam 1 τ)
def dy (τ : ℍ) : ℂ := euler y (Periodic.qParam 1 τ)
def e2 (τ : ℍ) : ℂ :=
  euler (cuspFunction 1 T.normalizedDeltaForm) (Periodic.qParam 1 τ) /
    T.normalizedDeltaLimit τ

theorem bracketSource (τ : ℍ) :
    bracketQ (Periodic.qParam 1 τ) =
      3 * A.E6 τ * dx τ - 2 * A.E4 τ * dy τ := by
  simp [bracketQ, dx, dy, xAtQ, yAtQ]

-- Remaining inputs: actual derivative product/quotient law for Delta,
-- and actual bracket cusp form plus first coefficient. The original
-- discriminant's nonvanishing is discharged by the pinned theorem.
theorem ramanujan46 (τ : ℍ)
    (hDisc : A.E4 τ ^ 2 * (3 * dx τ) - A.E6 τ * (2 * dy τ) =
      e2 τ * (A.E4 τ ^ 3 - A.E6 τ ^ 2))
    (hBracket : bracketQ (Periodic.qParam 1 τ) =
      1728 * T.normalizedDeltaLimit τ) :
    3 * dx τ = e2 τ * A.E4 τ - A.E6 τ ∧
    2 * dy τ = e2 τ * A.E6 τ - A.E4 τ ^ 2 := by
  let X := A.E4 τ
  let Y := A.E6 τ
  let U := 3 * dx τ
  let V := 2 * dy τ
  let E := e2 τ
  let d := X^3 - Y^2
  have hd : d = 1728 * T.normalizedDeltaLimit τ := by
    unfold d X Y T.normalizedDeltaLimit T.discriminantNumeratorLimit
    ring
  have hn : d ≠ 0 := by
    rw [hd]
    exact mul_ne_zero (by norm_num) (Final.normalizedDelta_ne_zero_canonical τ)
  have hD : X^2 * U - Y * V = E*d := hDisc
  have hB : Y*U-X*V=d := by
    rw [hd, ← hBracket, bracketSource]
    dsimp [X,Y,U,V]
    ring
  have h4 : d*(U-E*X+Y)=0 := by
    dsimp [d] at *
    linear_combination X*hD-Y*hB
  have h6 : d*(V-E*Y+X^2)=0 := by
    dsimp [d] at *
    linear_combination Y*hD-X^2*hB
  have h4' := (mul_eq_zero.mp h4).resolve_left hn
  have h6' := (mul_eq_zero.mp h6).resolve_left hn
  constructor
  · change U = E*X-Y
    linear_combination h4'
  · change V = E*Y-X^2
    linear_combination h6'


-- Original normalized Delta on the entire cusp coordinate, including zero.
-- This uses the pinned Mathlib product/sum cusp laws rather than equality
-- at an isolated point (which would not justify differentiating).
theorem deltaCuspFunction :
    cuspFunction 1 T.normalizedDeltaForm =
      fun q => (x q ^ 3 - y q ^ 2) / 1728 := by
  have hx := xAnalyticZero.continuousAt
  have hy := yAnalyticZero.continuousAt
  have hc : cuspFunction 1 T.e4CubeWeight12 = fun q => x q ^ 3 := by
    change cuspFunction 1 (((A.E4.mul A.E4).mul A.E4 :
      ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
    rw [ModularForm.cuspFunction_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.cuspFunction_mul one_pos one_mem_strictPeriods_SL]
    funext q
    simp only [Pi.mul_apply, x]
    ring
  have hs : cuspFunction 1 T.e6SquareWeight12 = fun q => y q ^ 2 := by
    change cuspFunction 1 ((A.E6.mul A.E6 : ModularForm 𝒮ℒ 12) : ℍ → ℂ) = _
    rw [ModularForm.cuspFunction_mul one_pos one_mem_strictPeriods_SL]
    funext q
    simp only [Pi.mul_apply, y]
    ring
  have hdiff : cuspFunction 1 ((T.e4CubeWeight12 - T.e6SquareWeight12 :
      ModularForm 𝒮ℒ 12) : ℍ → ℂ) =
      fun q => x q ^ 3 - y q ^ 2 := by
    change cuspFunction 1 ((T.e4CubeWeight12 : ℍ → ℂ) -
      (T.e6SquareWeight12 : ℍ → ℂ)) = _
    rw [cuspFunction_sub
      (analyticAt_cuspFunction_zero T.e4CubeWeight12 one_pos one_mem_strictPeriods_SL).continuousAt
      (analyticAt_cuspFunction_zero T.e6SquareWeight12 one_pos one_mem_strictPeriods_SL).continuousAt,
      hc, hs]
    rfl
  change cuspFunction 1 (((1728 : ℂ)⁻¹) •
    ((T.e4CubeWeight12 - T.e6SquareWeight12 : ModularForm 𝒮ℒ 12) : ℍ → ℂ)) = _
  rw [cuspFunction_smul
    (analyticAt_cuspFunction_zero (T.e4CubeWeight12 - T.e6SquareWeight12)
      one_pos one_mem_strictPeriods_SL).continuousAt, hdiff]
  funext q
  simp [div_eq_mul_inv, mul_comm]

theorem deltaCuspDeriv (q : ℂ) (hq : ‖q‖ < 1) :
    deriv (cuspFunction 1 T.normalizedDeltaForm) q =
      (3 * x q ^ 2 * deriv x q - 2 * y q * deriv y q) / 1728 := by
  have hx := (xDifferentiable q hq).hasDerivAt
  have hy := (yDifferentiable q hq).hasDerivAt
  have h := ((hx.pow 3).sub (hy.pow 2)).div_const (1728 : ℂ)
  rw [deltaCuspFunction]
  convert h.deriv using 1 <;> ring

theorem actualDiscDerivative (τ : ℍ)
    (hq : ‖Periodic.qParam 1 τ‖ < 1) :
    A.E4 τ ^ 2 * (3 * dx τ) - A.E6 τ * (2 * dy τ) =
      e2 τ * (A.E4 τ ^ 3 - A.E6 τ ^ 2) := by
  have hn := Final.normalizedDelta_ne_zero_canonical τ
  have hd : A.E4 τ ^ 3 - A.E6 τ ^ 2 = 1728 * T.normalizedDeltaLimit τ := by
    unfold T.normalizedDeltaLimit T.discriminantNumeratorLimit
    ring
  rw [hd]
  unfold e2 dx dy euler
  rw [deltaCuspDeriv _ hq, xAtQ, yAtQ]
  field_simp [hn]
  <;> ring

-- Cusp packaging now only needs to be paid for the actual bracket.
-- The disk premise is the existing qParam norm theorem, not a derivative oracle.
theorem ramanujan46FromBracket (τ : ℍ)
    (hq : ‖Periodic.qParam 1 τ‖ < 1)
    (hBracket : bracketQ (Periodic.qParam 1 τ) =
      1728 * T.normalizedDeltaLimit τ) :
    3 * dx τ = e2 τ * A.E4 τ - A.E6 τ ∧
    2 * dy τ = e2 τ * A.E6 τ - A.E4 τ ^ 2 :=
  ramanujan46 τ (actualDiscDerivative τ hq) hBracket

end
end Integration.Paper9OriginalEisensteinDerivative

import Mathlib
import YangMills.LiteralSU2BoundaryHaarTranslation
import YangMills.LiteralSU2WilsonOSFactorization

/-!
# Analytic properties of the positive Wilson half

For nonnegative Wilson coupling every literal positive-half plaquette factor is
in `(0,1]`.  The positive half is measurable and uniformly bounded by one.
Consequently multiplying an L1 positive-time test by the positive half preserves
integrability.  This removes the last analytic side condition before the final
boundary gauge-projector calculation.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- A literal plaquette holonomy is measurable as a function of the link field. -/
theorem su2_plaquette_measurable
    {L : ℕ}
    (x : SU2TorusSite L) (μ ν : Fin 4) :
    Measurable (fun links : SU2TorusLinks L => su2Plaquette links x μ ν) := by
  unfold su2Plaquette
  fun_prop

/-- The positive plaquette cost is measurable. -/
theorem su2_positive_plaquette_cost_measurable :
    Measurable su2PositivePlaquetteCost := by
  rw [show su2PositivePlaquetteCost = fun U => 1 - U.a by
    funext U
    exact su2_real_trace_normalization U]
  fun_prop

/-- Each literal Wilson plaquette factor is measurable in the link field. -/
theorem su2_literal_wilson_factor_measurable
    {L : ℕ}
    (p : SU2LiteralPlaquetteIndex L)
    (β : ℝ) :
    Measurable (fun links : SU2TorusLinks L =>
      Real.exp (-(β *
        su2PositivePlaquetteCost
          (su2Plaquette links p.1 p.2.1 p.2.2)))) := by
  fun_prop

/-- Any finite literal Wilson product is measurable. -/
theorem su2_literal_wilson_product_measurable
    {L : ℕ}
    (plaquettes : Finset (SU2LiteralPlaquetteIndex L))
    (β : ℝ) :
    Measurable (fun links : SU2TorusLinks L =>
      su2LiteralWilsonProduct plaquettes links β) := by
  classical
  unfold su2LiteralWilsonProduct
  fun_prop

/-- The selected positive Wilson half is measurable. -/
theorem su2_positive_half_measurable
    (n : ℕ) [NeZero n]
    (β : ℝ) :
    Measurable (fun links : SU2TorusLinks (2 * n) =>
      su2EvenTimePositiveWilsonHalf n links β) := by
  unfold su2EvenTimePositiveWilsonHalf
  exact su2_literal_wilson_product_measurable
    (su2EvenTimePositivePlaquettes n) β

/-- Every nonnegative-coupling plaquette Boltzmann factor lies in `(0,1]`. -/
theorem su2_literal_wilson_factor_pos_le_one
    {L : ℕ}
    (p : SU2LiteralPlaquetteIndex L)
    (links : SU2TorusLinks L)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 < Real.exp (-(β *
        su2PositivePlaquetteCost
          (su2Plaquette links p.1 p.2.1 p.2.2))) ∧
      Real.exp (-(β *
        su2PositivePlaquetteCost
          (su2Plaquette links p.1 p.2.1 p.2.2))) ≤ 1 := by
  constructor
  · positivity
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr
      (mul_nonneg hβ
        (su2_positive_plaquette_cost_bounds
          (su2Plaquette links p.1 p.2.1 p.2.2)).1))

/-- Any finite Wilson product is positive and at most one for `β ≥ 0`. -/
theorem su2_literal_wilson_product_pos_le_one
    {L : ℕ}
    (plaquettes : Finset (SU2LiteralPlaquetteIndex L))
    (links : SU2TorusLinks L)
    (β : ℝ) (hβ : 0 ≤ β) :
    0 < su2LiteralWilsonProduct plaquettes links β ∧
      su2LiteralWilsonProduct plaquettes links β ≤ 1 := by
  classical
  unfold su2LiteralWilsonProduct
  constructor
  · apply Finset.prod_pos
    intro p hp
    exact (su2_literal_wilson_factor_pos_le_one p links β hβ).1
  · apply Finset.prod_le_one
    · intro p hp
      exact (su2_literal_wilson_factor_pos_le_one p links β hβ).1.le
    · intro p hp
      exact (su2_literal_wilson_factor_pos_le_one p links β hβ).2

/-- The positive half is positive and bounded by one. -/
theorem su2_positive_half_pos_le_one
    (n : ℕ) [NeZero n]
    (β : ℝ) (hβ : 0 ≤ β)
    (links : SU2TorusLinks (2 * n)) :
    0 < su2EvenTimePositiveWilsonHalf n links β ∧
      su2EvenTimePositiveWilsonHalf n links β ≤ 1 := by
  unfold su2EvenTimePositiveWilsonHalf
  exact su2_literal_wilson_product_pos_le_one
    (su2EvenTimePositivePlaquettes n) links β hβ

/-- Multiplying an L1 test by a measurable `[0,1]` half factor preserves L1. -/
theorem integrable_mul_of_measurable_zero_one
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    (f h : X → ℝ)
    (hf : Integrable f μ)
    (hhMeas : Measurable h)
    (hhNonneg : ∀ x, 0 ≤ h x)
    (hhLeOne : ∀ x, h x ≤ 1) :
    Integrable (fun x => f x * h x) μ := by
  apply hf.mono'
  · exact hf.1.mul hhMeas.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hhNonneg x)]
    nlinarith [norm_nonneg (f x)]

end RequestProject.YangMills

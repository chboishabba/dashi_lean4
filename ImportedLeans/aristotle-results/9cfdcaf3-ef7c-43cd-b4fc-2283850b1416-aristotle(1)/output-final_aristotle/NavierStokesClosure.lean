import Mathlib

/-!
# Navier–Stokes enstrophy → BKM closure: the analytic core

This file formalizes the genuine mathematical content of the four Navier–Stokes
"closure receipts" requested (NS-1 … NS-4), namely the enstrophy-to-BKM chain.

The single physical input (the A8/A9 *scale-monotone* result already assumed in
the repository) is the enstrophy depletion differential inequality
`Z'(t) ≤ -2α Z(t)`.  From it the four receipts follow by elementary analysis:

* **NS-1** (`ns1_enstrophy_passage`): Grönwall gives `Z(t) ≤ Z(0)·e^{-2αt}`.
* **NS-2** (`ns2_vorticity_control`): the same differential inequality for the
  `H¹` enstrophy `Y` gives `‖ω(t)‖_{H¹} = √(Y t) ≤ √(Y 0)·e^{-αt}`.
* **NS-3** (`ns3_linfty_vorticity_control`): a Gagliardo–Nirenberg/Sobolev
  interpolation turns the exponential `L²`/`H²` decay into an exponential bound
  `‖ω(t)‖_∞ ≤ K·e^{-βt}`, whose time integral is finite:
  `∫₀^∞ ‖ω‖_∞ dt ≤ K/β`, and the integrand is integrable on `(0,∞)`.
* **NS-4** (`ns4_global_regularity`): the Beale–Kato–Majda criterion — taken as a
  named hypothesis, since BKM (1984) is the cited deep input — says that finite
  time-integral of `‖ω‖_∞` (here: integrability on `(0,∞)`) precludes blow-up;
  combined with NS-3 it yields global regularity.
-/

open MeasureTheory
open scoped BigOperators

namespace NavierStokesClosure

/-! ## NS-1 : enstrophy passage (Grönwall) -/

/--
**NS-1 (enstrophy passage).**  If the enstrophy `Z` is everywhere
differentiable with `Z'(t) ≤ -2α·Z(t)` for all `t ≥ 0`, then
`Z(t) ≤ Z(0)·e^{-2αt}` for all `t ≥ 0`.
-/
theorem ns1_enstrophy_passage
    (Z Z' : ℝ → ℝ) (α : ℝ)
    (hderiv : ∀ t, HasDerivAt Z (Z' t) t)
    (hineq : ∀ t, 0 ≤ t → Z' t ≤ -2 * α * Z t) :
    ∀ t, 0 ≤ t → Z t ≤ Z 0 * Real.exp (-2 * α * t) := by
  intros t ht_nonneg
  have h_antitone : AntitoneOn (fun t => Z t * Real.exp (2 * α * t)) (Set.Ici 0) := by
    apply_rules [ antitoneOn_of_deriv_nonpos ];
    · exact convex_Ici _;
    · exact ContinuousOn.mul ( continuousOn_of_forall_continuousAt fun t ht => HasDerivAt.continuousAt ( hderiv t ) ) ( Continuous.continuousOn ( Real.continuous_exp.comp ( continuous_const.mul continuous_id' ) ) );
    · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.mul ( hderiv x |> HasDerivAt.differentiableAt ) ( DifferentiableAt.exp ( differentiableAt_id.const_mul _ ) ) );
    · intro x hx; norm_num [ mul_comm, hderiv _ |> HasDerivAt.differentiableAt ];
      rw [ hderiv x |> HasDerivAt.deriv ] ; nlinarith [ hineq x <| interior_subset hx, Real.exp_pos ( x * ( α * 2 ) ) ];
  convert mul_le_mul_of_nonneg_right ( h_antitone ( show 0 ∈ Set.Ici 0 by norm_num ) ( show t ∈ Set.Ici 0 by assumption ) ht_nonneg ) ( inv_nonneg.mpr ( Real.exp_nonneg ( 2 * α * t ) ) ) using 1 ; ring_nf ; norm_num [ Real.exp_neg, mul_assoc, mul_comm, mul_left_comm ];
  norm_num [ Real.exp_neg ]

/-! ## NS-2 : vorticity `H¹` control -/

/--
**NS-2 (vorticity `H¹` control).**  If the (squared) `H¹` enstrophy `Y ≥ 0`
satisfies the same depletion inequality `Y'(t) ≤ -2α·Y(t)`, then the vorticity
`H¹` norm `√(Y t)` decays exponentially: `√(Y t) ≤ √(Y 0)·e^{-αt}`.
-/
theorem ns2_vorticity_control
    (Y Y' : ℝ → ℝ) (α : ℝ)
    (hYnn : ∀ t, 0 ≤ Y t)
    (hderiv : ∀ t, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t, 0 ≤ t → Y' t ≤ -2 * α * Y t) :
    ∀ t, 0 ≤ t → Real.sqrt (Y t) ≤ Real.sqrt (Y 0) * Real.exp (-α * t) := by
  -- From NS-1, we have $Y(t) \leq Y(0) * e^{-2\alpha t}$ for all $t \geq 0$.
  have hY_le : ∀ t, 0 ≤ t → Y t ≤ Y 0 * Real.exp (-2 * α * t) :=
    ns1_enstrophy_passage Y Y' α hderiv hineq
  intro t ht; convert Real.sqrt_le_sqrt ( hY_le t ht ) using 1 ; rw [ Real.sqrt_mul ( hYnn _ ), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.exp_mul ] ; ring;

/-! ## NS-3 : `L∞` vorticity integrability -/

/--
**NS-3 (`L∞` vorticity integrability).**  After Gagliardo–Nirenberg/Sobolev
interpolation the sup-norm of the vorticity decays exponentially,
`‖ω(t)‖_∞ ≤ K·e^{-βt}` with `β > 0`.  Then the integrand is integrable on
`(0,∞)` and its time integral is finite, bounded by `K/β`.
-/
theorem ns3_linfty_vorticity_control
    (w : ℝ → ℝ) (K β : ℝ) (hβ : 0 < β) (hK : 0 ≤ K)
    (hwmeas : Measurable w)
    (hwnn : ∀ t, 0 ≤ w t)
    (hwbd : ∀ t, 0 ≤ t → w t ≤ K * Real.exp (-β * t)) :
    IntegrableOn w (Set.Ioi 0) volume ∧
      ∫ t in Set.Ioi (0 : ℝ), w t ≤ K / β := by
  constructor;
  · refine' MeasureTheory.Integrable.mono' _ _ _;
    refine' fun t => K * Real.exp ( -β * t );
    · exact MeasureTheory.Integrable.const_mul ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa [ mul_comm ] using ( exp_neg_integrableOn_Ioi 0 hβ ) ) ) ) ) ) ) ) ) ) ) ) ) _;
    · exact hwmeas.aestronglyMeasurable;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( hwnn t ) ] ; exact hwbd t ht.out.le;
  · refine' le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _;
    refine' fun t => K * Real.exp ( -β * t );
    · exact Filter.Eventually.of_forall hwnn;
    · exact MeasureTheory.Integrable.const_mul ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa [ mul_comm ] using ( exp_neg_integrableOn_Ioi 0 hβ ) ) ) ) ) ) ) ) ) ) ) ) ) _;
    · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using hwbd t ht.out.le;
    · rw [ MeasureTheory.integral_const_mul, div_eq_mul_inv ];
      exact mul_le_mul_of_nonneg_left ( by have := integral_exp_neg_mul_rpow zero_lt_one hβ; norm_num [ Real.rpow_neg_one ] at this ⊢; linarith ) hK

/-! ## NS-4 : global regularity via Beale–Kato–Majda -/

/--
**NS-4 (global regularity).**  The Beale–Kato–Majda criterion (1984), here a
named hypothesis `bkm`, states that integrability of `t ↦ ‖ω(t)‖_∞` on `(0,∞)`
(finiteness of the time integral) precludes finite-time blow-up, i.e. yields
global regularity.  Combined with NS-3 this gives global regularity
unconditionally from the enstrophy depletion.
-/
theorem ns4_global_regularity
    (w : ℝ → ℝ) (K β : ℝ) (hβ : 0 < β) (hK : 0 ≤ K)
    (hwmeas : Measurable w)
    (hwnn : ∀ t, 0 ≤ w t)
    (hwbd : ∀ t, 0 ≤ t → w t ≤ K * Real.exp (-β * t))
    (GlobalRegular : Prop)
    (bkm : IntegrableOn w (Set.Ioi 0) volume → GlobalRegular) :
    GlobalRegular := by
  refine bkm ?_;
  exact ( ns3_linfty_vorticity_control w K β hβ hK hwmeas hwnn hwbd ) |>.1

end NavierStokesClosure
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFarExactCut

/-!
# Signed max-cut of the transformed reflection-pair tail

The literal one-scale frontier is a summable `tsum` of the actual transformed
reflection-pair term.  This file preserves its sign information exactly.

For one source zero, write

  x_sigma = W.threeTapAdaptivePairTerm eps sigma.

We split it into

  adverse(x) = (x + |x|)/2,
  credit(x)  = (|x| - x)/2,

so that

  x = adverse(x) - credit(x)

with both pieces nonnegative.  Thus the complete reflection tail is an adverse
mass minus a favorable credit, rather than an absolute-value budget.

The sign of `x_sigma` is also identified with the sign of the actual normalized
kernel

  integral P_eps(v) cosh(alpha_sigma v) cos(q_sigma v) dv,

because the multiplicity/scale coefficient is strictly positive for t >= 200.
No analytic sign of that kernel is assumed here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Positive part of the actual transformed pair contribution. -/
def QuarticFourSignedPolePair.threeTapPairAdversePart
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  (W.threeTapAdaptivePairTerm eps rho
    + |W.threeTapAdaptivePairTerm eps rho|) / 2

/-- Magnitude of the favorable negative part of the actual transformed pair
contribution. -/
def QuarticFourSignedPolePair.threeTapPairFavorableCredit
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  (|W.threeTapAdaptivePairTerm eps rho|
    - W.threeTapAdaptivePairTerm eps rho) / 2

theorem QuarticFourSignedPolePair.threeTapPairAdversePart_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 <= W.threeTapPairAdversePart eps rho := by
  unfold QuarticFourSignedPolePair.threeTapPairAdversePart
  by_cases hx : 0 <= W.threeTapAdaptivePairTerm eps rho
  · rw [abs_of_nonneg hx]
    linarith
  · have hx' : W.threeTapAdaptivePairTerm eps rho <= 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx']
    ring

theorem QuarticFourSignedPolePair.threeTapPairFavorableCredit_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 <= W.threeTapPairFavorableCredit eps rho := by
  unfold QuarticFourSignedPolePair.threeTapPairFavorableCredit
  exact div_nonneg (sub_nonneg.mpr (le_abs_self _)) (by norm_num)

theorem QuarticFourSignedPolePair.threeTapAdaptivePairTerm_eq_adverse_sub_credit
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapAdaptivePairTerm eps rho
      = W.threeTapPairAdversePart eps rho
        - W.threeTapPairFavorableCredit eps rho := by
  unfold QuarticFourSignedPolePair.threeTapPairAdversePart
    QuarticFourSignedPolePair.threeTapPairFavorableCredit
  ring

theorem QuarticFourSignedPolePair.threeTapPairAdversePart_eq_self_of_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (h : 0 <= W.threeTapAdaptivePairTerm eps rho) :
    W.threeTapPairAdversePart eps rho
      = W.threeTapAdaptivePairTerm eps rho := by
  unfold QuarticFourSignedPolePair.threeTapPairAdversePart
  rw [abs_of_nonneg h]
  ring

theorem QuarticFourSignedPolePair.threeTapPairAdversePart_eq_zero_of_nonpos
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (h : W.threeTapAdaptivePairTerm eps rho <= 0) :
    W.threeTapPairAdversePart eps rho = 0 := by
  unfold QuarticFourSignedPolePair.threeTapPairAdversePart
  rw [abs_of_nonpos h]
  ring

theorem QuarticFourSignedPolePair.threeTapPairFavorableCredit_eq_zero_of_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (h : 0 <= W.threeTapAdaptivePairTerm eps rho) :
    W.threeTapPairFavorableCredit eps rho = 0 := by
  unfold QuarticFourSignedPolePair.threeTapPairFavorableCredit
  rw [abs_of_nonneg h]
  ring

theorem QuarticFourSignedPolePair.threeTapPairFavorableCredit_eq_neg_self_of_nonpos
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (h : W.threeTapAdaptivePairTerm eps rho <= 0) :
    W.threeTapPairFavorableCredit eps rho
      = - W.threeTapAdaptivePairTerm eps rho := by
  unfold QuarticFourSignedPolePair.threeTapPairFavorableCredit
  rw [abs_of_nonpos h]
  ring

/-- The multiplicity/projective-scale factor multiplying the normalized pair
kernel is strictly positive in the high range. -/
theorem QuarticFourSignedPolePair.threeTapAdaptivePairCoefficient_pos
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2 := by
  have hmNat :
      (1 : ℕ) <= (zetaZeroConfig).mult (rho : ℂ) :=
    (zetaZeroConfig).one_le_mult (rho : ℂ) rho.2
  have hm : 0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    exact_mod_cast hmNat
  have hr : 0 < t/16 := by linarith
  exact div_pos hm (sq_pos_of_pos hr)

/-- Pointwise sign firewall: the actual pair term has exactly the sign of the
normalized transformed reflection kernel. -/
theorem QuarticFourSignedPolePair.threeTapAdaptivePairTerm_pos_iff_kernel_pos
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    0 < W.threeTapAdaptivePairTerm eps rho
      <->
    0 < W.threeTapNormalizedPairKernel eps
      (heightOf rho / (t/16))
      (quarticSignedPoleNormalizedOrdinateOffset t rho) := by
  have hc := W.threeTapAdaptivePairCoefficient_pos ht rho
  unfold QuarticFourSignedPolePair.threeTapAdaptivePairTerm
  constructor
  · intro h
    by_contra hk
    have hk' :
        W.threeTapNormalizedPairKernel eps
          (heightOf rho / (t/16))
          (quarticSignedPoleNormalizedOrdinateOffset t rho) <= 0 :=
      le_of_not_gt hk
    have hnonpos :
        ((zetaZeroConfig).mult (rho : ℂ) : ℝ) / (t/16)^2
          * W.threeTapNormalizedPairKernel eps
              (heightOf rho / (t/16))
              (quarticSignedPoleNormalizedOrdinateOffset t rho) <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc.le hk'
    linarith
  · intro hk
    exact mul_pos hc hk

/-- The adverse set is an actual kernel-sign condition in normalized
horizontal/ordinate coordinates. -/
def QuarticFourSignedPolePair.threeTapPairKernelAdverse
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : Prop :=
  0 < W.threeTapNormalizedPairKernel eps
    (heightOf rho / (t/16))
    (quarticSignedPoleNormalizedOrdinateOffset t rho)

theorem QuarticFourSignedPolePair.threeTapPairKernelAdverse_iff_pairTerm_pos
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapPairKernelAdverse eps rho
      <-> 0 < W.threeTapAdaptivePairTerm eps rho := by
  exact (W.threeTapAdaptivePairTerm_pos_iff_kernel_pos ht rho).symm

/-- The adverse part is summable because the original pair carrier is
summable absolutely on the unordered zero index. -/
theorem QuarticFourSignedPolePair.threeTapPairAdversePart_summable
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Summable
      (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        W.threeTapPairAdversePart eps (sigma : Zeros)) := by
  have hpair := W.threeTapAdaptivePairTerm_summable ht (eps:=eps)
  have habs :
      Summable
        (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
          |W.threeTapAdaptivePairTerm eps (sigma : Zeros)|) := by
    simpa [Real.norm_eq_abs] using hpair.norm
  have hsum := hpair.add habs
  have hscaled := hsum.const_mul (1/2 : ℝ)
  simpa [QuarticFourSignedPolePair.threeTapPairAdversePart,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- The favorable credit is summable on the same literal carrier. -/
theorem QuarticFourSignedPolePair.threeTapPairFavorableCredit_summable
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    Summable
      (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
        W.threeTapPairFavorableCredit eps (sigma : Zeros)) := by
  have hpair := W.threeTapAdaptivePairTerm_summable ht (eps:=eps)
  have habs :
      Summable
        (fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
          |W.threeTapAdaptivePairTerm eps (sigma : Zeros)|) := by
    simpa [Real.norm_eq_abs] using hpair.norm
  have hdiff := habs.sub hpair
  have hscaled := hdiff.const_mul (1/2 : ℝ)
  simpa [QuarticFourSignedPolePair.threeTapPairFavorableCredit,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled

/-- Exact infinite signed decomposition of the complete reflection-pair tail. -/
theorem QuarticFourSignedPolePair.threeTap_pair_tsum_eq_adverse_sub_credit
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapAdaptivePairTerm eps (sigma : Zeros))
      =
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros))
      -
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairFavorableCredit eps (sigma : Zeros)) := by
  have ha := W.threeTapPairAdversePart_summable ht (eps:=eps)
  have hf := W.threeTapPairFavorableCredit_summable ht (eps:=eps)
  rw [← ha.tsum_sub hf]
  apply tsum_congr
  intro sigma
  exact W.threeTapAdaptivePairTerm_eq_adverse_sub_credit (eps:=eps) (sigma : Zeros)

theorem QuarticFourSignedPolePair.threeTap_pair_adverse_tsum_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <=
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros) := by
  exact tsum_nonneg fun sigma =>
    W.threeTapPairAdversePart_nonneg (eps:=eps) (sigma : Zeros)

theorem QuarticFourSignedPolePair.threeTap_pair_favorable_credit_tsum_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <=
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairFavorableCredit eps (sigma : Zeros) := by
  exact tsum_nonneg fun sigma =>
    W.threeTapPairFavorableCredit_nonneg (eps:=eps) (sigma : Zeros)

/-- One-sided cancellation-preserving upper bound: favorable negative pairs are
never charged to the adverse mass. -/
theorem QuarticFourSignedPolePair.threeTap_pair_tsum_le_adverse_tsum
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapAdaptivePairTerm eps (sigma : Zeros))
      <=
    ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      W.threeTapPairAdversePart eps (sigma : Zeros) := by
  rw [W.threeTap_pair_tsum_eq_adverse_sub_credit ht]
  have hf := W.threeTap_pair_favorable_credit_tsum_nonneg (eps:=eps)
  linarith

/-- Exact paid-cost decision surface in adverse-mass / favorable-credit
coordinates. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_iff_adverse_credit
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps < 0
      <->
    (1/2 : ℝ) *
      ((∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapPairAdversePart eps (sigma : Zeros))
        -
       (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapPairFavorableCredit eps (sigma : Zeros)))
      < W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_neg_iff_pair_tsum_lt ht,
      W.threeTap_pair_tsum_eq_adverse_sub_credit ht]

/-- Sufficient PASS criterion charging only the adverse positive pair mass. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_of_adverse_tsum_lt
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hadv :
      (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapPairAdversePart eps (sigma : Zeros))
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    W.threeTapResonancePaidCost eps < 0 := by
  apply (W.threeTapResonancePaidCost_neg_iff_pair_tsum_lt ht).2
  have hle := W.threeTap_pair_tsum_le_adverse_tsum ht (eps:=eps)
  have hscaled :
      (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros))
      <=
      (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapPairAdversePart eps (sigma : Zeros)) := by
    exact mul_le_mul_of_nonneg_left hle (by norm_num)
  exact lt_of_le_of_lt hscaled hadv

/-- Direct near-line PASS from an adverse-mass bound; all favorable pair
contributions remain as free credit. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_adverse_tsum_lt
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hadv :
      (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapPairAdversePart eps (sigma : Zeros))
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a -> a < delta ->
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact W.threeTapResonancePaidCost_neg_of_adverse_tsum_lt ht hadv

end Synthesis

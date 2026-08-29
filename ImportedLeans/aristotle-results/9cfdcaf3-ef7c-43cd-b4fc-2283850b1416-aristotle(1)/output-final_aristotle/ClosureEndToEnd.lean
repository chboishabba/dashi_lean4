import Mathlib
import YangMillsClosure
import NavierStokesClosure

/-!
# End-to-end conditional reduction chains for the YM / NS closure receipts

This file assembles the per-step analytic lemmas of `YangMillsClosure` and
`NavierStokesClosure` into *single* end-to-end conditional theorems.  These do
**not** prove the open Millennium-Prize statements; they make the reduction
structure explicit and fully machine-checked: given the named (still-open)
physical inputs, the analytic chain delivers the stated conclusion with no
`sorry` and no extra axioms.

* `ns_end_to_end` : from the enstrophy-depletion differential inequality
  `Y' ≤ -2αY`, a Gagliardo–Nirenberg/Sobolev interpolation bound
  `‖ω‖_∞ ≤ K·√(H¹ enstrophy)`, and the Beale–Kato–Majda criterion (as a named
  hypothesis), global regularity follows.  This wires NS-2 → NS-3 → NS-4.

* `ym_uniform_kp_end_to_end` : from the corrected coupling threshold
  `c_K ≥ (4/3)·log(24e)` (giving the rooted KP sum `≤ 1/2` at the base scale,
  YM-1) and RG improvement factors `q k ≤ 1` (YM-3), the rooted KP sum stays
  `≤ 1/2` uniformly in the RG step `k`, hence uniformly in the volume.
-/

open MeasureTheory
open scoped BigOperators

namespace ClosureEndToEnd

/-
**Navier–Stokes end-to-end conditional regularity.**

Inputs (the genuinely physical ones are the named hypotheses):
* `Y` is the (squared) `H¹` enstrophy, nonnegative and differentiable, obeying
  the A8/A9 enstrophy-depletion inequality `Y'(t) ≤ -2α·Y(t)` for `t ≥ 0` with
  `α > 0`;
* `w t = ‖ω(t)‖_∞` is a nonnegative measurable sup-norm bounded by the
  Gagliardo–Nirenberg/Sobolev interpolation `w t ≤ K·√(Y t)` (`K ≥ 0`);
* `bkm` is the Beale–Kato–Majda criterion: integrability of `w` on `(0,∞)`
  yields `GlobalRegular`.

Conclusion: `GlobalRegular`.  The chain is NS-2 (exponential `H¹` decay) →
NS-3 (`L∞` integrability) → NS-4 (BKM).
-/
theorem ns_end_to_end
    (Y Y' w : ℝ → ℝ) (α K : ℝ)
    (hα : 0 < α) (hK : 0 ≤ K)
    (hYnn : ∀ t, 0 ≤ Y t)
    (hderiv : ∀ t, HasDerivAt Y (Y' t) t)
    (hineq : ∀ t, 0 ≤ t → Y' t ≤ -2 * α * Y t)
    (hwmeas : Measurable w)
    (hwnn : ∀ t, 0 ≤ w t)
    (hsob : ∀ t, 0 ≤ t → w t ≤ K * Real.sqrt (Y t))
    (GlobalRegular : Prop)
    (bkm : IntegrableOn w (Set.Ioi 0) volume → GlobalRegular) :
    GlobalRegular := by
  apply bkm;
  have h_integrable : ∀ t, 0 ≤ t → w t ≤ K * Real.sqrt (Y 0) * Real.exp (-α * t) := by
    intro t ht;
    refine le_trans ( hsob t ht ) ?_;
    convert mul_le_mul_of_nonneg_left ( NavierStokesClosure.ns2_vorticity_control Y Y' α hYnn hderiv hineq t ht ) hK using 1 ; ring;
  refine' MeasureTheory.Integrable.mono' _ _ _;
  refine' fun t => K * Real.sqrt ( Y 0 ) * Real.exp ( -α * t );
  · exact MeasureTheory.Integrable.const_mul ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact ( by exact by simpa [ mul_comm ] using ( exp_neg_integrableOn_Ioi 0 hα ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) _;
  · exact hwmeas.aestronglyMeasurable;
  · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioi ] with t ht using by rw [ Real.norm_of_nonneg ( hwnn t ) ] ; exact h_integrable t ht.out.le;

/-
**Yang–Mills uniform-volume KP bound, end-to-end.**

From the corrected coupling threshold `c_K ≥ (4/3)·log(24e)` and the YM-1
per-size activity bound, the rooted Kotecký–Preiss sum at the base scale is
`≤ 1/2` (YM-1).  Given RG improvement factors `q k ≤ 1` with
`δ(k+1) ≤ q k · δ k` and `δ 0` equal to that base KP sum, the rooted KP sum
stays `≤ 1/2` uniformly in the RG step `k` (YM-3), hence uniformly in the
volume.
-/
theorem ym_uniform_kp_end_to_end
    (cK a : ℝ) (ha : a = cK / 4)
    (hcK : (4 / 3) * Real.log (24 * Real.exp 1) ≤ cK)
    (A : ℕ → ℝ) (hA0 : A 0 = 0) (hAnn : ∀ n, 0 ≤ A n)
    (hAbound : ∀ n, 1 ≤ n →
      A n ≤ (8 * Real.exp 1) ^ n * Real.exp (-cK * n) * Real.exp (a * n))
    (δ q : ℕ → ℝ)
    (hδnn : ∀ k, 0 ≤ δ k)
    (hq1 : ∀ k, q k ≤ 1)
    (hrec : ∀ k, δ (k + 1) ≤ q k * δ k)
    (hδ0 : δ 0 = ∑' n, A n) :
    ∀ k, δ k ≤ 1 / 2 := by
  exact YangMillsClosure.ym3_uniform_volume_kp δ q hδnn hq1 hrec ( by linarith [ YangMillsClosure.ym1_local_kp_sum_below_one cK a ha hcK A hA0 hAnn hAbound ] )

end ClosureEndToEnd
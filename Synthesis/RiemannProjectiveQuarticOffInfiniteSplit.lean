import Synthesis.RiemannProjectiveQuarticOffPairNormalization
import Zeta23Bridge.ProjectedZeroTailSummability
import Zeta23Bridge.NearFarCarrierSplit
import Zeta23Bridge.OscillatoryKernelDecay

/-!
# Infinite base/horizontal split for the quartic off-ordinate carrier

For the fixed normalized quartic witness G and physical radius r=t/16 define

  B_sigma^Q(t)
    = (m_sigma/r^2) Phi_Q((Im sigma-t)/r).

The compact C² profile P_Q gives

  |Phi_Q(q)| <= C_Q/q².

Consequently, outside |Im sigma-t|<1,

  |B_sigma^Q(t)|
    <= C_Q * m_sigma/(Im sigma-t)².

The r^-2 normalization cancels exactly against the r² obtained from q^-2
decay. Thus the literal theorem-bearing tail weight is already the correct
majorant and the full quartic base family is summable (the remaining local band
is finite).

The horizontal source is then defined exactly as

  H_sigma^Q = D_pair^Q - B_sigma^Q

and is summable because both families on the right are summable. This passes
the exact base/horizontal split through the actual infinite off-ordinate tsum.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Real Topology

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.ProjectedZeroTailSummability
open Zeta23Bridge.NearFarCarrierSplit
open Zeta23Bridge.OscillatoryKernelDecay

def genericProjectiveBaseCurvature (G : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ,
    |deriv (deriv (genericProjectivePhysicalProfile G 1)) x|

theorem genericProjectivePhysicalProfile_contDiff_two
    {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G) :
    ContDiff ℝ 2 (genericProjectivePhysicalProfile G 1) := by
  unfold genericProjectivePhysicalProfile
  exact (contDiff_const.mul hG).mul
    (Zeta23Bridge.LiteralWeilProjectiveTaper.twoRadiusBracket_contDiff G 1)

theorem genericProjectiveBaseCurvature_nonneg
    (G : ℝ → ℝ) :
    0 ≤ genericProjectiveBaseCurvature G := by
  unfold genericProjectiveBaseCurvature
  positivity

theorem genericProjectiveBaseKernel_abs_le_invSq
    {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G)
    {q : ℝ} (hq : q ≠ 0) :
    |genericProjectiveBaseKernel G 1 q|
      ≤ genericProjectiveBaseCurvature G / q^2 := by
  unfold genericProjectiveBaseKernel compactCosineTransform
  exact abs_integral_mul_cos_le
    (genericProjectivePhysicalProfile_contDiff_two hG)
    (genericProjectivePhysicalProfile_compact hGc 1)
    hq

def quarticBaseSourceTerm
    (W : QuarticHighWitness) (t : ℝ) (sigma : Zeros) : ℝ :=
  let r := t/16
  ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / r^2
    * genericProjectiveBaseKernel
        (quarticThreeWindowProfile W.R W.lam)
        1
        (((sigma : ℂ).im-t)/r)

def quarticHorizontalSourceTerm
    (W : QuarticHighWitness) (t : ℝ) (sigma : Zeros) : ℝ :=
  literalPairProjectiveDefect
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16) sigma
    - quarticBaseSourceTerm W t sigma

theorem quarticBaseSourceTerm_eq_zero_of_sameOrd
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    {sigma : Zeros}
    (him : (sigma : ℂ).im = t) :
    quarticBaseSourceTerm W t sigma = 0 := by
  unfold quarticBaseSourceTerm
  have hr : t/16 ≠ 0 := by positivity
  have hq : (((sigma : ℂ).im-t)/(t/16)) = 0 := by
    rw [him]
    simp
  rw [hq,
    genericProjectiveBaseKernel_zero
      (quarticThreeWindowProfile_continuous (lam:=W.lam) W.Rpos)
      (quarticThreeWindowProfile_compact (lam:=W.lam) W.Rpos)
      1]
  ring

theorem quarticBaseSourceTerm_abs_le_tailTerm_of_far
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (sigma : Zeros)
    (hfar : 1 ≤ |(sigma : ℂ).im-t|) :
    |quarticBaseSourceTerm W t sigma|
      ≤
    genericProjectiveBaseCurvature
        (quarticThreeWindowProfile W.R W.lam)
      * tailTerm t sigma := by
  let G := quarticThreeWindowProfile W.R W.lam
  let r := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdelta : (sigma : ℂ).im-t ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hfar
    linarith
  have hq : (((sigma : ℂ).im-t)/r) ≠ 0 :=
    div_ne_zero hdelta hr.ne'
  have hdec :=
    genericProjectiveBaseKernel_abs_le_invSq
      (G:=G)
      (quarticThreeWindowProfile_contDiff (lam:=W.lam) W.Rpos)
      (quarticThreeWindowProfile_compact (lam:=W.lam) W.Rpos)
      hq
  have hm :
      0 ≤ ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) := by positivity
  have hC :
      0 ≤ genericProjectiveBaseCurvature G :=
    genericProjectiveBaseCurvature_nonneg G
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  unfold quarticBaseSourceTerm
  dsimp [G,r] at hdec ⊢
  rw [abs_mul,
      abs_of_nonneg (div_nonneg hm hr2.le)]
  have hscaled :
      ((zetaZeroConfig).mult (sigma : ℂ) : ℝ) / (t/16)^2
          *
        (genericProjectiveBaseCurvature G
          / (((sigma : ℂ).im-t)/(t/16))^2)
        =
      genericProjectiveBaseCurvature G
        * (((zetaZeroConfig).mult (sigma : ℂ) : ℝ)
          / ((sigma : ℂ).im-t)^2) := by
    field_simp [hdelta, (by linarith : t ≠ 0)]
    ring
  have hmul :=
    mul_le_mul_of_nonneg_left hdec
      (div_nonneg hm (sq_nonneg (t/16)))
  rw [hscaled] at hmul
  unfold tailTerm
  rw [if_pos hfar]
  exact hmul

theorem quarticBaseSourceTerm_summable_full
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Summable (quarticBaseSourceTerm W t) := by
  classical
  let C :=
    genericProjectiveBaseCurvature
      (quarticThreeWindowProfile W.R W.lam)
  have hC0 : 0 ≤ C := genericProjectiveBaseCurvature_nonneg _
  have hmajor : Summable (fun sigma : Zeros => C * tailTerm t sigma) :=
    (summable_tailTerm t).mul_left C
  let S : Set Zeros := nearSet t 1
  have hSfin : S.Finite := nearSet_finite t 1
  have hev :
      ∀ᶠ sigma : Zeros in Filter.cofinite,
        ‖quarticBaseSourceTerm W t sigma‖
          ≤ C * tailTerm t sigma := by
    filter_upwards [hSfin.compl_mem_cofinite] with sigma hsigma
    have hfar : 1 ≤ |(sigma : ℂ).im-t| := by
      by_contra hlt
      apply hsigma
      exact not_le.1 hlt
    rw [Real.norm_eq_abs]
    exact quarticBaseSourceTerm_abs_le_tailTerm_of_far
      W ht sigma hfar
  exact Summable.of_norm_bounded_eventually hmajor hev

theorem quarticBaseSourceTerm_summable_offOrd
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      quarticBaseSourceTerm W t (sigma : Zeros) :=
  (quarticBaseSourceTerm_summable_full W ht).subtype _

theorem quarticPairDefect_summable_offOrd
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      literalPairProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16) (sigma : Zeros) := by
  exact literalPairProjectiveDefect_summable_offOrd
    (quarticPhysicalDetector_contDiff W.Rpos)
    (quarticPhysicalDetector_compact W.Rpos ht)
    (quarticPhysicalDetector_even W.R W.lam t)
    t (t/16)

theorem quarticHorizontalSourceTerm_summable_offOrd
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Summable fun sigma : ((SameOrd t)ᶜ : Set Zeros) =>
      quarticHorizontalSourceTerm W t (sigma : Zeros) := by
  exact
    (quarticPairDefect_summable_offOrd W ht).sub
      (quarticBaseSourceTerm_summable_offOrd W ht)

theorem quarticPairDefect_eq_base_add_horizontal
    (W : QuarticHighWitness)
    (t : ℝ) (sigma : Zeros) :
    literalPairProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16) sigma
      =
    quarticBaseSourceTerm W t sigma
      + quarticHorizontalSourceTerm W t sigma := by
  unfold quarticHorizontalSourceTerm
  ring

theorem tsum_offOrd_quarticPair_eq_base_add_horizontal
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      literalPairProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16) (sigma : Zeros))
      =
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      quarticBaseSourceTerm W t (sigma : Zeros))
      +
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      quarticHorizontalSourceTerm W t (sigma : Zeros)) := by
  have hb := quarticBaseSourceTerm_summable_offOrd W ht
  have hh := quarticHorizontalSourceTerm_summable_offOrd W ht
  rw [← hb.tsum_add hh]
  apply tsum_congr
  intro sigma
  exact quarticPairDefect_eq_base_add_horizontal
    W t (sigma : Zeros)

theorem quartic_offOrdProjectiveDefect_eq_base_add_horizontal
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      =
    (1/2 : ℝ) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        quarticBaseSourceTerm W t (sigma : Zeros))
      +
    (1/2 : ℝ) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        quarticHorizontalSourceTerm W t (sigma : Zeros)) := by
  rw [offOrdProjectiveDefect_eq_half_literalPair_tsum
      (quarticPhysicalDetector_contDiff W.Rpos)
      (quarticPhysicalDetector_compact W.Rpos ht)
      (quarticPhysicalDetector_even W.R W.lam t)
      t (t/16),
    tsum_offOrd_quarticPair_eq_base_add_horizontal W ht]
  ring

theorem tsum_full_quarticBase_eq_offOrd
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
      =
    (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
      quarticBaseSourceTerm W t (sigma : Zeros)) := by
  have hfull := quarticBaseSourceTerm_summable_full W ht
  have hsame := hfull.subtype (SameOrd t)
  have hoff := hfull.subtype ((SameOrd t)ᶜ)
  have hsame0 :
      (∑' sigma : SameOrd t,
        quarticBaseSourceTerm W t (sigma : Zeros)) = 0 := by
    apply tsum_eq_zero
    intro sigma
    exact quarticBaseSourceTerm_eq_zero_of_sameOrd
      W ht sigma.property
  have hsplit := (Summable.tsum_add_tsum_compl hsame hoff).symm
  rw [hsame0, zero_add] at hsplit
  exact hsplit

end Synthesis

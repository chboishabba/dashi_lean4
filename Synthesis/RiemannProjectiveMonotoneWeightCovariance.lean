import Synthesis.RiemannNormalizedProjectiveHorizontalZeroAnchor

/-!
# Monotone-weight projective covariance compiler

The strict alpha=0 anchor is one instance of a more general radial-order
principle.

Let

  B_r(u) = A_0(r) cos(2ru) - A_0(2r) cos(ru).

If a continuous weight w is strictly increasing with |u| on the support of a
nonnegative radially-admissible taper g, then

  integral g(u) w(u) B_r(u) du < 0.

Indeed, antisymmetrisation gives the negative of

  g(u)g(v)(w(u)-w(v))
    [cos(ru)cos(2rv)-cos(2ru)cos(rv)],

and the two factors in the last line have the same radial ordering sign.

This is the reusable consumer needed for the nonzero-ordinate horizontal
kernel, where w(u)=H_alpha(u) cos(delta u).
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def weightedRadialIntegrand
    (g : ℝ → ℝ) (r : ℝ) (w : ℝ → ℝ) : ℝ × ℝ → ℝ := fun z =>
  g z.1 * g z.2 *
    ((w z.1 - w z.2) *
      (Real.cos (r*z.1) * Real.cos (2*r*z.2)
        - Real.cos (2*r*z.1) * Real.cos (r*z.2)))

theorem weightedRadialIntegrand_nonneg
    {g w : ℝ → ℝ}
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2*r*|u| < Real.pi/2)
    (hmono :
      ∀ u v, g u ≠ 0 → g v ≠ 0 →
        |u| ≤ |v| → w u ≤ w v)
    (z : ℝ × ℝ) :
    0 ≤ weightedRadialIntegrand g r w z := by
  unfold weightedRadialIntegrand
  by_cases h1 : g z.1 = 0
  · simp [h1]
  by_cases h2 : g z.2 = 0
  · simp [h2]
  have hK :=
    squareRadialKernel_nonneg hr (hrad _ h1) (hrad _ h2)
  rcases le_total |z.1| |z.2| with huv | hvu
  · have hw : w z.1 - w z.2 ≤ 0 := by
      linarith [hmono z.1 z.2 h1 h2 huv]
    have hsq : z.1^2-z.2^2 ≤ 0 := by
      nlinarith [sq_abs z.1, sq_abs z.2]
    have hradK :
        Real.cos (r*z.1) * Real.cos (2*r*z.2)
          - Real.cos (2*r*z.1) * Real.cos (r*z.2) ≤ 0 := by
      by_cases heq : |z.1| = |z.2|
      · have hc : Real.cos (r*z.1) = Real.cos (r*z.2) := by
          rw [cos_mul_abs hr (u:=z.1), cos_mul_abs hr (u:=z.2), heq]
        have hc2 : Real.cos (2*r*z.1) = Real.cos (2*r*z.2) := by
          have hr2 : 0 < 2*r := by positivity
          rw [cos_mul_abs hr2 (u:=z.1), cos_mul_abs hr2 (u:=z.2), heq]
        rw [hc, hc2]
        ring_nf
      · have hlt : |z.1| < |z.2| := lt_of_le_of_ne huv heq
        have hcu : 0 < Real.cos (r*z.1) := cos_pos_of_radial hr (hrad _ h1)
        have hcv : 0 < Real.cos (r*z.2) := cos_pos_of_radial hr (hrad _ h2)
        have hfac : 0 < 2*Real.cos (r*z.1)*Real.cos (r*z.2)+1 := by positivity
        rw [radialKernel_factor]
        have hc : Real.cos (r*z.2) < Real.cos (r*z.1) := by
          rw [cos_mul_abs hr (u:=z.1), cos_mul_abs hr (u:=z.2)]
          refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
            (mul_lt_mul_of_pos_left hlt hr)
          linarith
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hfac.le
    exact mul_nonneg (mul_nonneg (hnn _) (hnn _))
      (mul_nonneg_of_nonpos_of_nonpos hw hradK)
  · have hw : 0 ≤ w z.1 - w z.2 := by
      linarith [hmono z.2 z.1 h2 h1 hvu]
    have hsq : 0 ≤ z.1^2-z.2^2 := by
      nlinarith [sq_abs z.1, sq_abs z.2]
    have hradK :
        0 ≤
          Real.cos (r*z.1) * Real.cos (2*r*z.2)
            - Real.cos (2*r*z.1) * Real.cos (r*z.2) := by
      by_cases heq : |z.1| = |z.2|
      · have hc : Real.cos (r*z.1) = Real.cos (r*z.2) := by
          rw [cos_mul_abs hr (u:=z.1), cos_mul_abs hr (u:=z.2), heq]
        have hr2 : 0 < 2*r := by positivity
        have hc2 : Real.cos (2*r*z.1) = Real.cos (2*r*z.2) := by
          rw [cos_mul_abs hr2 (u:=z.1), cos_mul_abs hr2 (u:=z.2), heq]
        rw [hc, hc2]
        ring_nf
      · have hlt : |z.2| < |z.1| := lt_of_le_of_ne hvu (Ne.symm heq)
        have hcu : 0 < Real.cos (r*z.1) := cos_pos_of_radial hr (hrad _ h1)
        have hcv : 0 < Real.cos (r*z.2) := cos_pos_of_radial hr (hrad _ h2)
        have hfac : 0 < 2*Real.cos (r*z.1)*Real.cos (r*z.2)+1 := by positivity
        rw [radialKernel_factor]
        have hc : Real.cos (r*z.1) < Real.cos (r*z.2) := by
          rw [cos_mul_abs hr (u:=z.1), cos_mul_abs hr (u:=z.2)]
          refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
            (mul_lt_mul_of_pos_left hlt hr)
          linarith
        exact mul_nonneg (by linarith) hfac.le
    exact mul_nonneg (mul_nonneg (hnn _) (hnn _))
      (mul_nonneg hw hradK)

theorem weightedRadialIntegrand_continuous
    {g w : ℝ → ℝ} (hg : Continuous g) (hw : Continuous w)
    (r : ℝ) :
    Continuous (weightedRadialIntegrand g r w) := by
  unfold weightedRadialIntegrand
  fun_prop

theorem weightedRadialIntegrand_compact
    {g w : ℝ → ℝ} (hgc : HasCompactSupport g)
    (r : ℝ) :
    HasCompactSupport (weightedRadialIntegrand g r w) := by
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  apply HasCompactSupport.intro hK
  intro z hz
  have h : g z.1 = 0 ∨ g z.2 = 0 := by
    by_contra hc
    push_neg at hc
    exact hz ⟨subset_tsupport g hc.1, subset_tsupport g hc.2⟩
  rcases h with h | h <;> simp [weightedRadialIntegrand, h]

theorem weightedRadialIntegrand_integrable
    {g w : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hw : Continuous w) (r : ℝ) :
    Integrable (weightedRadialIntegrand g r w) :=
  (weightedRadialIntegrand_continuous hg hw r)
    .integrable_of_hasCompactSupport
      (weightedRadialIntegrand_compact hgc r)

/--
Generic antisymmetrisation identity.
-/
theorem two_mul_integral_weight_mul_twoRadiusBracket
    {g w : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hw : Continuous w) (r : ℝ) :
    2 * (∫ u : ℝ, g u * w u * twoRadiusBracket g r u)
      =
    - ∫ z : ℝ × ℝ, weightedRadialIntegrand g r w z := by
  classical
  let f1 : ℝ → ℝ := fun u => g u*w u*Real.cos (2*r*u)
  let f2 : ℝ → ℝ := fun u => g u*Real.cos (r*u)
  let f3 : ℝ → ℝ := fun u => g u*w u*Real.cos (r*u)
  let f4 : ℝ → ℝ := fun u => g u*Real.cos (2*r*u)
  have hc1 : Continuous f1 := by dsimp [f1]; fun_prop
  have hc2 : Continuous f2 := by dsimp [f2]; fun_prop
  have hc3 : Continuous f3 := by dsimp [f3]; fun_prop
  have hc4 : Continuous f4 := by dsimp [f4]; fun_prop
  have hs1 : HasCompactSupport f1 := by
    dsimp [f1]; exact (hgc.mul_right.mul_right)
  have hs2 : HasCompactSupport f2 := by
    dsimp [f2]; exact hgc.mul_right
  have hs3 : HasCompactSupport f3 := by
    dsimp [f3]; exact (hgc.mul_right.mul_right)
  have hs4 : HasCompactSupport f4 := by
    dsimp [f4]; exact hgc.mul_right
  have hi1 : Integrable f1 := hc1.integrable_of_hasCompactSupport hs1
  have hi2 : Integrable f2 := hc2.integrable_of_hasCompactSupport hs2
  have hi3 : Integrable f3 := hc3.integrable_of_hasCompactSupport hs3
  have hi4 : Integrable f4 := hc4.integrable_of_hasCompactSupport hs4
  have hA1 : (∫ u : ℝ, f2 u) = evenResp g 0 r := by
    dsimp [f2]
    symm
    exact evenResp_zero_height g r
  have hA2 : (∫ u : ℝ, f4 u) = evenResp g 0 (2*r) := by
    dsimp [f4]
    symm
    exact evenResp_zero_height g (2*r)
  have hI :
      (∫ u : ℝ, g u*w u*twoRadiusBracket g r u)
        =
      (∫ u : ℝ, f1 u)*(∫ v : ℝ, f2 v)
        - (∫ u : ℝ, f3 u)*(∫ v : ℝ, f4 v) := by
    unfold twoRadiusBracket
    rw [hA1,hA2]
    rw [← integral_const_mul, ← integral_const_mul]
    rw [← integral_sub (hi1.const_mul _) (hi3.const_mul _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [f1,f3]
      ring
  let Psi : ℝ × ℝ → ℝ := fun z =>
    f1 z.1*f2 z.2 - f3 z.1*f4 z.2
  have hPsiC : Continuous Psi := by dsimp [Psi]; fun_prop
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  have hPsiSupp : HasCompactSupport Psi := by
    apply HasCompactSupport.intro hK
    intro z hz
    have h : g z.1=0 ∨ g z.2=0 := by
      by_contra hc
      push_neg at hc
      exact hz ⟨subset_tsupport g hc.1,subset_tsupport g hc.2⟩
    rcases h with h | h <;> simp [Psi,f1,f2,f3,f4,h]
  have hPsiI : Integrable Psi :=
    hPsiC.integrable_of_hasCompactSupport hPsiSupp
  have hSwapI : Integrable (fun z : ℝ × ℝ => Psi z.swap) := hPsiI.swap
  have hprod1 :
      ∫ z : ℝ × ℝ, f1 z.1*f2 z.2
        = (∫ u,f1 u)*(∫ v,f2 v) := by
    have h := MeasureTheory.integral_prod_mul
      (μ:=(volume:Measure ℝ)) (ν:=(volume:Measure ℝ)) f1 f2
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h
  have hprod2 :
      ∫ z : ℝ × ℝ, f3 z.1*f4 z.2
        = (∫ u,f3 u)*(∫ v,f4 v) := by
    have h := MeasureTheory.integral_prod_mul
      (μ:=(volume:Measure ℝ)) (ν:=(volume:Measure ℝ)) f3 f4
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h
  have hPsi :
      ∫ z : ℝ × ℝ, Psi z
        =
      (∫ u,f1 u)*(∫ v,f2 v)
        - (∫ u,f3 u)*(∫ v,f4 v) := by
    have h12 : Integrable (fun z : ℝ × ℝ => f1 z.1*f2 z.2) :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop) hPsiSupp
    have h34 : Integrable (fun z : ℝ × ℝ => f3 z.1*f4 z.2) :=
      Continuous.integrable_of_hasCompactSupport (by fun_prop) hPsiSupp
    rw [show Psi=fun z => f1 z.1*f2 z.2-f3 z.1*f4 z.2 by rfl,
      integral_sub h12 h34,hprod1,hprod2]
  have hswap :
      (∫ z : ℝ × ℝ, Psi z.swap)=∫ z : ℝ × ℝ, Psi z := by
    have h := MeasureTheory.integral_prod_swap
      (μ:=(volume:Measure ℝ)) (ν:=(volume:Measure ℝ)) Psi
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h
  have hpoint :
      (fun z : ℝ × ℝ => Psi z+Psi z.swap)
        = fun z => -weightedRadialIntegrand g r w z := by
    funext z
    dsimp [Psi,f1,f2,f3,f4,weightedRadialIntegrand]
    ring
  calc
    2*(∫ u : ℝ,g u*w u*twoRadiusBracket g r u)
      =2*∫ z : ℝ × ℝ,Psi z := by rw [hI,hPsi]
    _=∫ z : ℝ × ℝ,(Psi z+Psi z.swap) := by
      rw [integral_add hPsiI hSwapI,hswap]
      ring
    _=∫ z : ℝ × ℝ,-weightedRadialIntegrand g r w z := by rw [hpoint]
    _=-∫ z : ℝ × ℝ,weightedRadialIntegrand g r w z := by rw [integral_neg]

/--
Strict monotone-weight covariance theorem.
-/
theorem integral_weight_mul_twoRadiusBracket_neg
    {g w : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u)
    (hw : Continuous w)
    {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2*r*|u| < Real.pi/2)
    (hmono :
      ∀ u v, g u ≠ 0 → g v ≠ 0 →
        |u| ≤ |v| → w u ≤ w v)
    {u0 v0 : ℝ}
    (hu0 : 0 < g u0) (hv0 : 0 < g v0)
    (hne : |u0| ≠ |v0|)
    (hstrict :
      |u0| < |v0| → w u0 < w v0)
    (hstrict' :
      |v0| < |u0| → w v0 < w u0) :
    (∫ u : ℝ, g u*w u*twoRadiusBracket g r u) < 0 := by
  have hrep :=
    two_mul_integral_weight_mul_twoRadiusBracket hg hgc hw r
  have hnnI : ∀ z : ℝ × ℝ, 0 ≤ weightedRadialIntegrand g r w z :=
    weightedRadialIntegrand_nonneg hnn hr hrad hmono
  let W : Set (ℝ × ℝ) :=
    {z | 0 < g z.1 ∧ 0 < g z.2 ∧ |z.1|-|z.2| ≠ 0
      ∧ ((|z.1|<|z.2| ∧ w z.1<w z.2)
          ∨ (|z.2|<|z.1| ∧ w z.2<w z.1))}
  have hWopen : IsOpen W := by
    dsimp [W]
    fun_prop
  have hWne : (u0,v0) ∈ W := by
    dsimp [W]
    refine ⟨hu0,hv0,sub_ne_zero.mpr hne,?_⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inl ⟨h,hstrict h⟩
    · exact Or.inr ⟨h,hstrict' h⟩
  have hWsub : W ⊆ Function.support (weightedRadialIntegrand g r w) := by
    rintro z ⟨h1,h2,hne',hord⟩
    have hKpos := squareRadialKernel_pos hr
      (hrad _ (ne_of_gt h1)) (hrad _ (ne_of_gt h2))
      (sub_ne_zero.mp hne')
    have hwK :
        0 < (w z.1-w z.2) *
          (Real.cos (r*z.1)*Real.cos (2*r*z.2)
            - Real.cos (2*r*z.1)*Real.cos (r*z.2)) := by
      rcases hord with ⟨hlt,hwlt⟩ | ⟨hlt,hwlt⟩
      · have hradneg :
            Real.cos (r*z.1)*Real.cos (2*r*z.2)
              - Real.cos (2*r*z.1)*Real.cos (r*z.2) < 0 := by
          have hs : z.1^2-z.2^2 < 0 := by
            nlinarith [sq_abs z.1,sq_abs z.2,abs_nonneg z.1,abs_nonneg z.2]
          nlinarith [hKpos]
        exact mul_pos_of_neg_of_neg (by linarith) hradneg
      · have hradpos :
            0 <
            Real.cos (r*z.1)*Real.cos (2*r*z.2)
              - Real.cos (2*r*z.1)*Real.cos (r*z.2) := by
          have hs : 0 < z.1^2-z.2^2 := by
            nlinarith [sq_abs z.1,sq_abs z.2,abs_nonneg z.1,abs_nonneg z.2]
          nlinarith [hKpos]
        exact mul_pos (by linarith) hradpos
    have hz : 0 < weightedRadialIntegrand g r w z := by
      unfold weightedRadialIntegrand
      exact mul_pos (mul_pos h1 h2) hwK
    exact ne_of_gt hz
  have hpos : 0 < ∫ z : ℝ × ℝ, weightedRadialIntegrand g r w z := by
    rw [integral_pos_iff_support_of_nonneg hnnI
      (weightedRadialIntegrand_integrable hg hgc hw r)]
    exact lt_of_lt_of_le
      (hWopen.measure_pos volume ⟨(u0,v0),hWne⟩)
      (measure_mono hWsub)
  linarith

end Synthesis

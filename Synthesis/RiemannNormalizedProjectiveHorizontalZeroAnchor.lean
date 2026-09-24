import Synthesis.RiemannNormalizedProjectiveHorizontalUniformSign
import Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-!
# Strict alpha=0 anchor for the normalized projective horizontal kernel

The divided-square horizontal kernel already has a genuine value at alpha=0,

  coshMinusOneDivSq 0 v = v^2/2.

The existing synthetic-height sign theorem proves Q(t,alpha,0)<0 for every
alpha != 0, but its proof factors through alpha^2 and therefore does not by
itself give the value at the continuous-extension point alpha=0.

This file proves that missing anchor directly.

For a nonnegative radially-admissible taper g, the projective bracket

  B_r(u) = A_0(r) cos(2ru) - A_0(2r) cos(ru)

has strictly negative u^2 covariance whenever g is positive at two different
moduli:

  integral g(u) u^2 B_r(u) du < 0.

The proof is the square-weight analogue of the literal two-radius height
detector.  Antisymmetrisation gives

  2 integral g(u)u^2 B_r(u)du
    = - integral integral
        g(u)g(v)(u^2-v^2)
        [cos(ru)cos(2rv)-cos(2ru)cos(rv)] du dv.

The integrand on the right is nonnegative, and strictly positive on an open
set around the two witness support points.  Hence the bracket moment is
strictly negative.

After v=t*u this is exactly Q_proj(t,0,0)<0 for the canonical taper.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-- Square-weight radial detector kernel. -/
def squareRadialIntegrand (g : ℝ → ℝ) (r : ℝ) : ℝ × ℝ → ℝ := fun z =>
  g z.1 * g z.2 *
    ((z.1^2 - z.2^2) *
      (Real.cos (r*z.1) * Real.cos (2*r*z.2)
        - Real.cos (2*r*z.1) * Real.cos (r*z.2)))

theorem squareRadialKernel_nonneg
    {r u v : ℝ} (hr : 0 < r)
    (hu : 2*r*|u| < Real.pi/2)
    (hv : 2*r*|v| < Real.pi/2) :
    0 ≤ (u^2-v^2) *
      (Real.cos (r*u) * Real.cos (2*r*v)
        - Real.cos (2*r*u) * Real.cos (r*v)) := by
  have hcu : 0 < Real.cos (r*u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r*v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r*u) * Real.cos (r*v) + 1 := by
    positivity
  rw [radialKernel_factor]
  rcases lt_trichotomy |u| |v| with h | h | h
  · have hsquare : u^2-v^2 < 0 := by
      nlinarith [sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]
    have hcos : Real.cos (r*v) < Real.cos (r*u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos hsquare.le
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) hfac.le)
  · have hsquare : u^2 = v^2 := by
      nlinarith [sq_abs u, sq_abs v]
    rw [hsquare]
    simp
  · have hsquare : 0 < u^2-v^2 := by
      nlinarith [sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]
    have hcos : Real.cos (r*u) < Real.cos (r*v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      linarith
    exact mul_nonneg hsquare.le
      (mul_nonneg (by linarith) hfac.le)

theorem squareRadialKernel_pos
    {r u v : ℝ} (hr : 0 < r)
    (hu : 2*r*|u| < Real.pi/2)
    (hv : 2*r*|v| < Real.pi/2)
    (hne : |u| ≠ |v|) :
    0 < (u^2-v^2) *
      (Real.cos (r*u) * Real.cos (2*r*v)
        - Real.cos (2*r*u) * Real.cos (r*v)) := by
  have hcu : 0 < Real.cos (r*u) := cos_pos_of_radial hr hu
  have hcv : 0 < Real.cos (r*v) := cos_pos_of_radial hr hv
  have hfac : 0 < 2 * Real.cos (r*u) * Real.cos (r*v) + 1 := by
    positivity
  rw [radialKernel_factor]
  rcases lt_or_gt_of_ne hne with h | h
  · have hsquare : u^2-v^2 < 0 := by
      nlinarith [sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]
    have hcos : Real.cos (r*v) < Real.cos (r*u) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      linarith
    exact mul_pos_of_neg_of_neg hsquare
      (mul_neg_of_neg_of_pos (by linarith) hfac)
  · have hsquare : 0 < u^2-v^2 := by
      nlinarith [sq_abs u, sq_abs v, abs_nonneg u, abs_nonneg v]
    have hcos : Real.cos (r*u) < Real.cos (r*v) := by
      rw [cos_mul_abs hr (u := u), cos_mul_abs hr (u := v)]
      refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_
        (mul_lt_mul_of_pos_left h hr)
      linarith
    exact mul_pos hsquare
      (mul_pos (by linarith) hfac)

theorem squareRadialIntegrand_nonneg
    {g : ℝ → ℝ}
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2*r*|u| < Real.pi/2)
    (z : ℝ × ℝ) :
    0 ≤ squareRadialIntegrand g r z := by
  unfold squareRadialIntegrand
  by_cases h1 : g z.1 = 0
  · simp [h1]
  by_cases h2 : g z.2 = 0
  · simp [h2]
  exact mul_nonneg (mul_nonneg (hnn _) (hnn _))
    (squareRadialKernel_nonneg hr (hrad _ h1) (hrad _ h2))

theorem squareRadialIntegrand_continuous
    {g : ℝ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous (squareRadialIntegrand g r) := by
  unfold squareRadialIntegrand
  fun_prop

theorem squareRadialIntegrand_compact
    {g : ℝ → ℝ} (hgc : HasCompactSupport g) (r : ℝ) :
    HasCompactSupport (squareRadialIntegrand g r) := by
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  apply HasCompactSupport.intro hK
  intro z hz
  have h : g z.1 = 0 ∨ g z.2 = 0 := by
    by_contra hc
    push_neg at hc
    exact hz ⟨subset_tsupport g hc.1, subset_tsupport g hc.2⟩
  rcases h with h | h <;> simp [squareRadialIntegrand, h]

theorem squareRadialIntegrand_integrable
    {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (r : ℝ) :
    Integrable (squareRadialIntegrand g r) :=
  (squareRadialIntegrand_continuous hg r).integrable_of_hasCompactSupport
    (squareRadialIntegrand_compact hgc r)

/--
Antisymmetrisation identity for the square-weight projective bracket.
-/
theorem two_mul_integral_sq_mul_twoRadiusBracket
    {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (r : ℝ) :
    2 * (∫ u : ℝ, g u * u^2 * twoRadiusBracket g r u)
      =
    - ∫ z : ℝ × ℝ, squareRadialIntegrand g r z := by
  classical
  let f1 : ℝ → ℝ := fun u =>
    g u * u^2 * Real.cos (2*r*u)
  let f2 : ℝ → ℝ := fun u =>
    g u * Real.cos (r*u)
  let f3 : ℝ → ℝ := fun u =>
    g u * u^2 * Real.cos (r*u)
  let f4 : ℝ → ℝ := fun u =>
    g u * Real.cos (2*r*u)
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
      (∫ u : ℝ, g u * u^2 * twoRadiusBracket g r u)
        =
      (∫ u : ℝ, f1 u) * (∫ v : ℝ, f2 v)
        - (∫ u : ℝ, f3 u) * (∫ v : ℝ, f4 v) := by
    unfold twoRadiusBracket
    rw [hA1, hA2]
    rw [← integral_const_mul, ← integral_const_mul]
    rw [← integral_sub (hi1.const_mul _) (hi3.const_mul _)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [f1, f3]
      ring

  let Psi : ℝ × ℝ → ℝ := fun z =>
    f1 z.1 * f2 z.2 - f3 z.1 * f4 z.2
  have hPsiC : Continuous Psi := by
    dsimp [Psi]
    fun_prop
  have hK : IsCompact ((tsupport g) ×ˢ (tsupport g)) := hgc.prod hgc
  have hPsiSupp : HasCompactSupport Psi := by
    apply HasCompactSupport.intro hK
    intro z hz
    have h : g z.1 = 0 ∨ g z.2 = 0 := by
      by_contra hc
      push_neg at hc
      exact hz ⟨subset_tsupport g hc.1, subset_tsupport g hc.2⟩
    rcases h with h | h <;> simp [Psi, f1, f2, f3, f4, h]
  have hPsiI : Integrable Psi :=
    hPsiC.integrable_of_hasCompactSupport hPsiSupp
  have hSwapI : Integrable (fun z : ℝ × ℝ => Psi z.swap) := by
    exact hPsiI.swap

  have hprod1 :
      ∫ z : ℝ × ℝ, f1 z.1 * f2 z.2
        = (∫ u, f1 u) * ∫ v, f2 v := by
    have h := MeasureTheory.integral_prod_mul
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) f1 f2
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h
  have hprod2 :
      ∫ z : ℝ × ℝ, f3 z.1 * f4 z.2
        = (∫ u, f3 u) * ∫ v, f4 v := by
    have h := MeasureTheory.integral_prod_mul
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) f3 f4
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h
  have hPsi :
      ∫ z : ℝ × ℝ, Psi z
        =
      (∫ u, f1 u) * (∫ v, f2 v)
        - (∫ u, f3 u) * (∫ v, f4 v) := by
    have h12 : Integrable (fun z : ℝ × ℝ => f1 z.1 * f2 z.2) := by
      exact Continuous.integrable_of_hasCompactSupport
        (by fun_prop)
        (HasCompactSupport.mul
          (hs1.comp_tendsto continuous_fst.tendsto)
          (hs2.comp_tendsto continuous_snd.tendsto))
    have h34 : Integrable (fun z : ℝ × ℝ => f3 z.1 * f4 z.2) := by
      exact Continuous.integrable_of_hasCompactSupport
        (by fun_prop)
        (HasCompactSupport.mul
          (hs3.comp_tendsto continuous_fst.tendsto)
          (hs4.comp_tendsto continuous_snd.tendsto))
    rw [show Psi = fun z => f1 z.1*f2 z.2 - f3 z.1*f4 z.2 by rfl,
      integral_sub h12 h34, hprod1, hprod2]

  have hswap :
      (∫ z : ℝ × ℝ, Psi z.swap) = ∫ z : ℝ × ℝ, Psi z := by
    have h := MeasureTheory.integral_prod_swap
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ)) Psi
    rwa [← MeasureTheory.Measure.volume_eq_prod] at h

  have hpoint :
      (fun z : ℝ × ℝ => Psi z + Psi z.swap)
        =
      fun z => - squareRadialIntegrand g r z := by
    funext z
    dsimp [Psi, f1, f2, f3, f4, squareRadialIntegrand]
    ring

  calc
    2 * (∫ u : ℝ, g u*u^2*twoRadiusBracket g r u)
      = 2 * ∫ z : ℝ × ℝ, Psi z := by rw [hI, hPsi]
    _ = ∫ z : ℝ × ℝ, (Psi z + Psi z.swap) := by
      rw [integral_add hPsiI hSwapI, hswap]
      ring
    _ = ∫ z : ℝ × ℝ, - squareRadialIntegrand g r z := by
      rw [hpoint]
    _ = - ∫ z : ℝ × ℝ, squareRadialIntegrand g r z := by
      rw [integral_neg]

/--
Strict square-covariance sign for the projective bracket.
-/
theorem integral_sq_mul_twoRadiusBracket_neg
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u)
    {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2*r*|u| < Real.pi/2)
    {u0 v0 : ℝ}
    (hu0 : 0 < g u0)
    (hv0 : 0 < g v0)
    (hne : |u0| ≠ |v0|) :
    (∫ u : ℝ, g u*u^2*twoRadiusBracket g r u) < 0 := by
  have hrep :=
    two_mul_integral_sq_mul_twoRadiusBracket hg hgc r
  have hnnI : ∀ z : ℝ × ℝ, 0 ≤ squareRadialIntegrand g r z :=
    squareRadialIntegrand_nonneg hnn hr hrad
  have hWopen :
      IsOpen {z : ℝ × ℝ |
        0 < g z.1 ∧ 0 < g z.2 ∧ |z.1|-|z.2| ≠ 0} := by
    have h1 : IsOpen {z : ℝ × ℝ | 0 < g z.1} :=
      isOpen_lt continuous_const (hg.comp continuous_fst)
    have h2 : IsOpen {z : ℝ × ℝ | 0 < g z.2} :=
      isOpen_lt continuous_const (hg.comp continuous_snd)
    have h3 : IsOpen {z : ℝ × ℝ | |z.1|-|z.2| ≠ 0} :=
      IsOpen.preimage (by fun_prop) isOpen_ne
    exact h1.inter (h2.inter h3)
  have hWne :
      ((u0,v0) : ℝ × ℝ) ∈
        {z : ℝ × ℝ |
          0 < g z.1 ∧ 0 < g z.2 ∧ |z.1|-|z.2| ≠ 0} :=
    ⟨hu0, hv0, sub_ne_zero.mpr hne⟩
  have hWsub :
      {z : ℝ × ℝ |
        0 < g z.1 ∧ 0 < g z.2 ∧ |z.1|-|z.2| ≠ 0}
        ⊆ Function.support (squareRadialIntegrand g r) := by
    rintro z ⟨h1,h2,h3⟩
    have hk := squareRadialKernel_pos hr
      (hrad _ (ne_of_gt h1)) (hrad _ (ne_of_gt h2))
      (sub_ne_zero.mp h3)
    have hz : 0 < squareRadialIntegrand g r z := by
      unfold squareRadialIntegrand
      exact mul_pos (mul_pos h1 h2) hk
    exact ne_of_gt hz
  have hpos :
      0 < ∫ z : ℝ × ℝ, squareRadialIntegrand g r z := by
    rw [integral_pos_iff_support_of_nonneg hnnI
      (squareRadialIntegrand_integrable hg hgc r)]
    exact lt_of_lt_of_le
      (hWopen.measure_pos volume ⟨(u0,v0),hWne⟩)
      (measure_mono hWsub)
  linarith

/--
Canonical normalized anchor: the continuous alpha=0 divided-square horizontal
kernel is strictly negative.
-/
theorem normalizedProjectiveHorizontalQuadratic_zero_zero_neg
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveHorizontalQuadratic t 0 0 < 0 := by
  have ht0 : 0 < t := by linarith
  let hd := quantitativeCanonicalGateData ht
  obtain ⟨u0,v0,hu0,hv0,huv⟩ := hd.twoPoint
  have hbracket :
      (∫ u : ℝ,
        quantitativeCanonicalTaper t u * u^2 *
          twoRadiusBracket
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t) u) < 0 := by
    exact integral_sq_mul_twoRadiusBracket_neg
      hd.smooth.continuous hd.compactSupport hd.nonneg
      hd.radiusPos hd.radial hu0 hv0 huv

  rw [normalizedProjectiveHorizontalQuadratic_eq_physicalCosine]
  simp only [zero_mul, Real.cos_zero, mul_one]
  unfold normalizedProjectiveHorizontalPhysicalProfile
    coshMinusOneDivSq
  simp only [if_pos rfl]

  let F : ℝ → ℝ := fun v =>
    normalizedProjectivePhysicalProfile t v * (v^2/2)
  have hscale := Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1/t := by
    rw [abs_of_pos (inv_pos.mpr ht0)]
    rfl
  have hpoint :
      (fun u : ℝ => F (t*u))
        =
      fun u : ℝ =>
        2 * t^2 *
          (quantitativeCanonicalTaper t u * u^2 *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u) := by
    funext u
    dsimp [F]
    have hp :=
      normalizedProjectivePhysicalProfile_scaled_cosh
        (t := t) (alpha := 0) (u := u) ht0
    simp only [zero_mul, Real.cosh_zero, mul_one] at hp
    unfold reflectionPairWeight projTaper at hp
    rw [hp]
    ring
  have hscaled :
      (∫ u : ℝ, F (t*u))
        = (1/t) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  have hleft :
      (∫ u : ℝ, F (t*u))
        =
      2*t^2 *
        ∫ u : ℝ,
          quantitativeCanonicalTaper t u * u^2 *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u := by
    rw [hpoint, integral_const_mul]
  rw [hleft] at hscaled
  have hfactor : 0 < 2*t^3 := by positivity
  have heq :
      (∫ v : ℝ, F v)
        =
      2*t^3 *
        ∫ u : ℝ,
          quantitativeCanonicalTaper t u * u^2 *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u := by
    field_simp [ne_of_gt ht0] at hscaled ⊢
    nlinarith
  rw [heq]
  exact mul_neg_of_pos_of_neg hfactor hbracket

end Synthesis

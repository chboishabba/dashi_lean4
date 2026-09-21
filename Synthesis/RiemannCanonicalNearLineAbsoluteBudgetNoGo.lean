import Synthesis.RiemannCanonicalDoubledRadiusPoleSign
import Synthesis.RiemannNormalizedHorizontalCorrectionBound
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Near-line no-go for componentwise absolute projective budgets

For a nonnegative taper supported in |u|<=Lambda and a horizontal height a with
|a| Lambda <= 1, centering in height gives the elementary bound

  |A_a(s)-A_0(s)| <= a^2 Lambda^2 ||g||_1.

The two-radius height determinant therefore satisfies

  |D_g(r;a,0)| <= 2 a^2 Lambda^2 ||g||_1^2.

This exposes the near-line scale without a small-r hypothesis.

For the actual canonical taper, the projective pole defect is strictly positive.
Consequently, for every positive multiplicity weight m there exists a positive
height a<1/2 for which

  2 * (2m D_g(r;a,0)) < D_pole^proj.

Thus no proof that separately replaces the N-mu and horizontal channels by
nonnegative upper budgets can establish the reflection-pair strict cut uniformly
over all nonzero horizontal heights.  The remaining proof must use signed
cancellation involving the target-independent channels, or make the test itself
depend on the target height.

This is a proof-search firewall, not an RH conclusion.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

def heightCenteredEvenResp (g : ℝ → ℝ) (a s : ℝ) : ℝ :=
  evenResp g a s - evenResp g 0 s

theorem abs_heightCenteredEvenResp_le
    {g : ℝ → ℝ} {a s Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 ≤ Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ Lambda)
    (hsmall : |a| * Lambda ≤ 1) :
    |heightCenteredEvenResp g a s|
      ≤
    a^2 * Lambda^2 * taperMass g := by
  unfold heightCenteredEvenResp evenResp
  have hia :
      Integrable
        (fun u : ℝ =>
          g u * (Real.cosh (a*u) * Real.cos (s*u))) :=
    taper_integrable hg hgc (by fun_prop)
  have hi0 :
      Integrable
        (fun u : ℝ =>
          g u * (Real.cosh (0*u) * Real.cos (s*u))) :=
    taper_integrable hg hgc (by fun_prop)
  rw [← integral_sub hia hi0]
  have hmajor :
      Integrable
        (fun u : ℝ =>
          a^2 * Lambda^2 * |g u|) :=
    (hg.abs.integrable_of_hasCompactSupport hgc.abs)
      .const_mul (a^2 * Lambda^2)
  calc
    |∫ u : ℝ,
      (g u * (Real.cosh (a*u) * Real.cos (s*u))
        - g u * (Real.cosh (0*u) * Real.cos (s*u)))|
      ≤
    ∫ u : ℝ,
      |g u * (Real.cosh (a*u) * Real.cos (s*u))
        - g u * (Real.cosh (0*u) * Real.cos (s*u))| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ u : ℝ, a^2 * Lambda^2 * |g u| := by
      apply integral_mono (hia.sub hi0).abs hmajor
      intro u
      by_cases hgu : g u = 0
      · simp [hgu]
      · have hu := hsupp u hgu
        have hau : |a*u| ≤ 1 := by
          rw [abs_mul]
          exact le_trans
            (mul_le_mul_of_nonneg_left hu (abs_nonneg a))
            hsmall
        have hch := cosh_sub_one_le_sq hau
        have hch0 := cosh_sub_one_nonneg (a*u)
        have hcos := Real.abs_cos_le_one (s*u)
        have hu2 : u^2 ≤ Lambda^2 := by
          nlinarith [sq_abs u]
        have ha2 : 0 ≤ a^2 := sq_nonneg a
        have hbound :
            Real.cosh (a*u)-1
              ≤ a^2 * Lambda^2 := by
          calc
            Real.cosh (a*u)-1
              ≤ (a*u)^2 := hch
            _ = a^2 * u^2 := by ring
            _ ≤ a^2 * Lambda^2 :=
              mul_le_mul_of_nonneg_left hu2 ha2
        simp only [zero_mul, Real.cosh_zero, one_mul]
        rw [show
          g u * (Real.cosh (a*u) * Real.cos (s*u))
            - g u * Real.cos (s*u)
          =
          g u * (Real.cosh (a*u)-1) * Real.cos (s*u) by ring,
          abs_mul, abs_mul,
          abs_of_nonneg hch0]
        have hgabs : 0 ≤ |g u| := abs_nonneg _
        calc
          |g u| * (Real.cosh (a*u)-1) * |Real.cos (s*u)|
            ≤ |g u| * (Real.cosh (a*u)-1) * 1 := by
              gcongr
          _ ≤ |g u| * (a^2 * Lambda^2) := by
              gcongr
          _ = a^2 * Lambda^2 * |g u| := by ring
    _ = a^2 * Lambda^2 * taperMass g := by
      rw [integral_const_mul]
      rfl

theorem abs_evenResp_zero_le_taperMass
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (s : ℝ) :
    |evenResp g 0 s| ≤ taperMass g := by
  unfold evenResp taperMass
  simp only [zero_mul, Real.cosh_zero, one_mul]
  have hi :
      Integrable (fun u : ℝ => g u * Real.cos (s*u)) :=
    taper_integrable hg hgc (by fun_prop)
  calc
    |∫ u : ℝ, g u * Real.cos (s*u)|
      ≤ ∫ u : ℝ, |g u * Real.cos (s*u)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ u : ℝ, |g u| := by
      exact integral_mono hi.abs
        (hg.abs.integrable_of_hasCompactSupport hgc.abs)
        (fun u => by
          rw [abs_mul]
          exact mul_le_of_le_one_right
            (abs_nonneg (g u)) (Real.abs_cos_le_one _))

theorem abs_heightDefect_le_heightSq
    {g : ℝ → ℝ} {a r Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 ≤ Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ Lambda)
    (hsmall : |a| * Lambda ≤ 1) :
    |heightDefect g r a 0|
      ≤
    2 * a^2 * Lambda^2 * taperMass g^2 := by
  have h1 :=
    abs_heightCenteredEvenResp_le
      hg hgc hLambda hsupp hsmall (s := r)
  have h2 :=
    abs_heightCenteredEvenResp_le
      hg hgc hLambda hsupp hsmall (s := 2*r)
  have hA1 := abs_evenResp_zero_le_taperMass hg hgc r
  have hA2 := abs_evenResp_zero_le_taperMass hg hgc (2*r)
  have hM : 0 ≤ taperMass g := taperMass_nonneg g
  have hC : 0 ≤ a^2 * Lambda^2 := by positivity
  have hre :
      heightDefect g r a 0
        =
      heightCenteredEvenResp g a r * evenResp g 0 (2*r)
        -
      heightCenteredEvenResp g a (2*r) * evenResp g 0 r := by
    unfold heightDefect heightCenteredEvenResp
    ring
  rw [hre]
  calc
    |heightCenteredEvenResp g a r * evenResp g 0 (2*r)
        -
      heightCenteredEvenResp g a (2*r) * evenResp g 0 r|
      ≤
    |heightCenteredEvenResp g a r| * |evenResp g 0 (2*r)|
      +
    |heightCenteredEvenResp g a (2*r)| * |evenResp g 0 r| := by
      rw [abs_sub]
      exact add_le_add le_rfl le_rfl
    _ ≤
    (a^2 * Lambda^2 * taperMass g) * taperMass g
      +
    (a^2 * Lambda^2 * taperMass g) * taperMass g := by
      exact add_le_add
        (mul_le_mul h1 hA2 (abs_nonneg _) hC)
        (mul_le_mul h2 hA1 (abs_nonneg _) hC)
    _ = 2 * a^2 * Lambda^2 * taperMass g^2 := by ring

def canonicalNearLineHeightBoundCoeff (t m : ℝ) : ℝ :=
  8 * m
    * (canonicalProjectiveLambda t)^2
    * taperMass (quantitativeCanonicalTaper t)^2

theorem canonical_doubledTarget_abs_le_heightSq
    {t a m : ℝ}
    (ht : 18 ≤ t)
    (hm : 0 ≤ m)
    (ha : |a| ≤ 1/2) :
    |2 * (2*m *
      heightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) a 0)|
      ≤
    canonicalNearLineHeightBoundCoeff t m * a^2 := by
  have ht0 : 0 < t := by linarith
  have hLambda0 : 0 ≤ canonicalProjectiveLambda t := by
    unfold canonicalProjectiveLambda
    positivity
  have hLambdaHalf : canonicalProjectiveLambda t < 1/2 := by
    unfold canonicalProjectiveLambda
    have hpi := Real.pi_lt_four
    rw [div_lt_iff₀ (by positivity : 0 < 4*t)]
    nlinarith
  have hsmall :
      |a| * canonicalProjectiveLambda t ≤ 1 := by
    have hprod :
        |a| * canonicalProjectiveLambda t < (1/2)*(1/2) :=
      mul_lt_mul_of_nonneg_of_pos ha hLambdaHalf
        (by positivity) (by norm_num)
    linarith
  have hD :=
    abs_heightDefect_le_heightSq
      (quantitativeCanonicalTaper_contDiff ht).continuous
      (quantitativeCanonicalTaper_compact ht)
      hLambda0
      (by
        intro u hu
        unfold canonicalProjectiveLambda
        exact (quantitativeCanonicalTaper_support_abs_lt ht hu).le)
      hsmall
      (r := quantitativeSampleRadius t)
  have hscale :
      |2 * (2*m *
        heightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) a 0)|
        =
      4*m *
        |heightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) a 0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2),
      abs_of_nonneg (mul_nonneg (by norm_num) hm)]
    ring
  rw [hscale]
  unfold canonicalNearLineHeightBoundCoeff
  have hmul :=
    mul_le_mul_of_nonneg_left hD
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hm)
  nlinarith

/--
For every positive multiplicity weight, some positive near-line height has a
doubled target defect smaller than the canonical projective pole alone.
-/
theorem exists_nearLine_height_pole_exceeds_doubledTarget
    {t m : ℝ}
    (ht : 18 ≤ t)
    (hm : 0 < m) :
    ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧
      2 * (2*m *
        heightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) a 0)
        <
      poleProjectiveDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t) := by
  let P : ℝ :=
    poleProjectiveDefect
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
  let C : ℝ := canonicalNearLineHeightBoundCoeff t m
  have hP : 0 < P := by
    dsimp [P]
    exact quantitativeCanonical_projectivePoleDefect_pos ht
  have hC : 0 ≤ C := by
    dsimp [C, canonicalNearLineHeightBoundCoeff]
    positivity
  let a : ℝ := P / (2 * (C + P + 1))
  have hden : 0 < 2 * (C + P + 1) := by positivity
  have ha0 : 0 < a := div_pos hP hden
  have haha : a < 1/2 := by
    dsimp [a]
    rw [div_lt_iff₀ hden]
    nlinarith
  have haAbs : |a| ≤ 1/2 := by
    rw [abs_of_pos ha0]
    exact haha.le
  have htarget :=
    canonical_doubledTarget_abs_le_heightSq
      ht hm.le haAbs
  have hCP :
      C * a^2 < P := by
    dsimp [a]
    have hsq : 0 ≤ (C-P)^2 := sq_nonneg (C-P)
    have hS : 0 < C+P+1 := by positivity
    field_simp [ne_of_gt hS, ne_of_gt hP]
    nlinarith [hsq]
  have hleabs :
      2 * (2*m *
        heightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) a 0)
      ≤
      |2 * (2*m *
        heightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) a 0)| :=
    le_abs_self _
  refine ⟨a, ha0, haha, ?_⟩
  dsimp [C, P] at htarget hCP ⊢
  exact lt_of_le_of_lt (hleabs.trans htarget) hCP

end Synthesis

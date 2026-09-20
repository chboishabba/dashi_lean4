import Synthesis.RiemannNormalizedProjectiveHorizontalSameOrdSign
import Synthesis.RiemannNormalizedProjectiveBaseProfile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Single-profile representation and q-variation of the horizontal quadratic

The projective horizontal divided-square consumer is not intrinsically a
three-channel object.  The same algebra that collapsed the q-only base mode to
one physical profile also collapses the horizontal quadratic:

  Q_proj(t,alpha,q)
    = integral P_t(v) H2(alpha,v) cos(qv) dv,

where

  H2(alpha,v) = (cosh(alpha v)-1)/alpha^2

with its alpha=0 continuous-extension value v^2/2.

This representation keeps the exact alpha^2 factor outside the zero sum while
exposing all ordinate dependence through one cosine transform.  It also gives a
direct q-Lipschitz estimate with the first absolute moment of the weighted
physical profile.  Together with the strict q=0 sign on an actual off-line
same-ordinate zero, this yields a signed neighborhood criterion rather than an
absolute far-shell budget.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

/-- Physical profile for the divided-square horizontal projective consumer. -/
def normalizedProjectiveHorizontalPhysicalProfile
    (t alpha v : ℝ) : ℝ :=
  normalizedProjectivePhysicalProfile t v
    * coshMinusOneDivSq alpha v

theorem coshMinusOneDivSq_continuous_in_v
    (alpha : ℝ) :
    Continuous (coshMinusOneDivSq alpha) := by
  by_cases ha : alpha = 0
  · subst alpha
    simp only [coshMinusOneDivSq, if_pos rfl]
    fun_prop
  · simp only [coshMinusOneDivSq, if_neg ha]
    fun_prop

theorem normalizedProjectiveHorizontalPhysicalProfile_continuous
    (t alpha : ℝ) :
    Continuous (normalizedProjectiveHorizontalPhysicalProfile t alpha) := by
  unfold normalizedProjectiveHorizontalPhysicalProfile
  exact (normalizedProjectivePhysicalProfile_continuous t).mul
    (coshMinusOneDivSq_continuous_in_v alpha)

theorem normalizedProjectiveHorizontalPhysicalProfile_compact
    (t alpha : ℝ) :
    HasCompactSupport (normalizedProjectiveHorizontalPhysicalProfile t alpha) := by
  unfold normalizedProjectiveHorizontalPhysicalProfile
  exact (normalizedProjectivePhysicalProfile_compact t).mul_right

theorem normalizedProjectiveHorizontalPhysicalProfile_integrable
    (t alpha : ℝ) :
    Integrable (normalizedProjectiveHorizontalPhysicalProfile t alpha) :=
  (normalizedProjectiveHorizontalPhysicalProfile_continuous t alpha)
    .integrable_of_hasCompactSupport
      (normalizedProjectiveHorizontalPhysicalProfile_compact t alpha)

/-- Pointwise collapse of the three divided-square projective channels to the
single physical profile. -/
theorem normalizedProjective_horizontalQuadratic_integrand_collapse
    (t alpha q v : ℝ) :
    (4 * normalizedCenteredFixedProfileAtScale t 2 v
        * coshMinusOneDivSq alpha v
        * Real.cos (q*v))
        * onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
      -
    (4 * normalizedCenteredFixedProfileAtScale t 1 v
        * coshMinusOneDivSq alpha v
        * Real.cos (q*v))
        * onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t)
      +
    (4 * normalizedCanonicalFixedProfile t v
        * coshMinusOneDivSq alpha v
        * Real.cos (q*v))
        * (onLineRadiusProfile (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t)
            -
           onLineRadiusProfile (quantitativeCanonicalTaper t)
              (2 * quantitativeSampleRadius t))
      =
    normalizedProjectiveHorizontalPhysicalProfile t alpha v
      * Real.cos (q*v) := by
  unfold normalizedCenteredFixedProfileAtScale
    normalizedProjectiveHorizontalPhysicalProfile
    normalizedProjectivePhysicalProfile
  ring

/-- Exact one-profile cosine-transform representation of Q_proj. -/
theorem normalizedProjectiveHorizontalQuadratic_eq_physicalCosine
    (t alpha q : ℝ) :
    normalizedProjectiveHorizontalQuadratic t alpha q
      =
    ∫ v : ℝ,
      normalizedProjectiveHorizontalPhysicalProfile t alpha v
        * Real.cos (q*v) := by
  let A : ℝ :=
    onLineRadiusProfile (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
  let B : ℝ :=
    onLineRadiusProfile (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t)

  let f2 : ℝ → ℝ := fun v =>
    4 * normalizedCenteredFixedProfileAtScale t 2 v
      * coshMinusOneDivSq alpha v
      * Real.cos (q*v)
  let f1 : ℝ → ℝ := fun v =>
    4 * normalizedCenteredFixedProfileAtScale t 1 v
      * coshMinusOneDivSq alpha v
      * Real.cos (q*v)
  let f0 : ℝ → ℝ := fun v =>
    4 * normalizedCanonicalFixedProfile t v
      * coshMinusOneDivSq alpha v
      * Real.cos (q*v)

  have hf2 : Integrable f2 := by
    dsimp [f2]
    exact Continuous.integrable_of_hasCompactSupport
      (by
        unfold normalizedCenteredFixedProfileAtScale
        fun_prop)
      ((((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left)
        .mul_right).mul_right)
  have hf1 : Integrable f1 := by
    dsimp [f1]
    exact Continuous.integrable_of_hasCompactSupport
      (by
        unfold normalizedCenteredFixedProfileAtScale
        fun_prop)
      ((((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left)
        .mul_right).mul_right)
  have hf0 : Integrable f0 := by
    dsimp [f0]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedCanonicalFixedProfile_compact t).mul_left.mul_right).mul_right)

  unfold normalizedProjectiveHorizontalQuadratic
    normalizedCenteredHorizontalQuadraticAtScale
    normalizedRadiusZeroHorizontalQuadratic
  rw [← integral_const_mul A f2, ← integral_const_mul B f1,
      ← integral_const_mul (A-B) f0]
  rw [← integral_sub (hf2.const_mul A) (hf1.const_mul B)]
  rw [← integral_add ((hf2.const_mul A).sub (hf1.const_mul B))
      (hf0.const_mul (A-B))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp [A, B, f2, f1, f0]
    rw [normalizedProjective_horizontalQuadratic_integrand_collapse
      t alpha q v]
    ring

/-- First absolute moment controlling q-variation of Q_proj. -/
def normalizedProjectiveHorizontalFirstMoment
    (t alpha : ℝ) : ℝ :=
  ∫ v : ℝ,
    |normalizedProjectiveHorizontalPhysicalProfile t alpha v| * |v|

theorem normalizedProjectiveHorizontalFirstMoment_nonneg
    (t alpha : ℝ) :
    0 ≤ normalizedProjectiveHorizontalFirstMoment t alpha := by
  unfold normalizedProjectiveHorizontalFirstMoment
  positivity

theorem normalizedProjectiveHorizontalFirstMoment_integrable
    (t alpha : ℝ) :
    Integrable fun v : ℝ =>
      |normalizedProjectiveHorizontalPhysicalProfile t alpha v| * |v| := by
  exact
    ((normalizedProjectiveHorizontalPhysicalProfile_continuous t alpha).abs.mul
      continuous_abs)
      .integrable_of_hasCompactSupport
        ((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).abs.mul_right)

/-- Exact q-Lipschitz bound for the horizontal divided-square consumer. -/
theorem normalizedProjectiveHorizontalQuadratic_lipschitz
    (t alpha p q : ℝ) :
    |normalizedProjectiveHorizontalQuadratic t alpha q
      - normalizedProjectiveHorizontalQuadratic t alpha p|
      ≤
    normalizedProjectiveHorizontalFirstMoment t alpha * |q-p| := by
  rw [normalizedProjectiveHorizontalQuadratic_eq_physicalCosine,
      normalizedProjectiveHorizontalQuadratic_eq_physicalCosine]
  have hiq : Integrable
      (fun v : ℝ =>
        normalizedProjectiveHorizontalPhysicalProfile t alpha v
          * Real.cos (q*v)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).mul_right)
  have hip : Integrable
      (fun v : ℝ =>
        normalizedProjectiveHorizontalPhysicalProfile t alpha v
          * Real.cos (p*v)) :=
    Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectiveHorizontalPhysicalProfile_compact t alpha).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun v : ℝ =>
          |q-p| *
            (|normalizedProjectiveHorizontalPhysicalProfile t alpha v| * |v|)) :=
    (normalizedProjectiveHorizontalFirstMoment_integrable t alpha).const_mul |q-p|
  calc
    |∫ v : ℝ,
      (normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (q*v)
        - normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (p*v))|
      ≤
    ∫ v : ℝ,
      |normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (q*v)
        - normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (p*v)| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ v : ℝ,
      |q-p| *
        (|normalizedProjectiveHorizontalPhysicalProfile t alpha v| * |v|) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro v
      have hc := Real.abs_cos_sub_cos_le (q*v) (p*v)
      have hfactor : |q*v-p*v| = |q-p| * |v| := by
        rw [← sub_mul, abs_mul]
      calc
        |normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (q*v)
          - normalizedProjectiveHorizontalPhysicalProfile t alpha v * Real.cos (p*v)|
          =
        |normalizedProjectiveHorizontalPhysicalProfile t alpha v|
          * |Real.cos (q*v)-Real.cos (p*v)| := by
            rw [← mul_sub, abs_mul]
        _ ≤
        |normalizedProjectiveHorizontalPhysicalProfile t alpha v|
          * |q*v-p*v| := by gcongr
        _ =
        |q-p| *
          (|normalizedProjectiveHorizontalPhysicalProfile t alpha v| * |v|) := by
            rw [hfactor]
            ring
    _ =
    |q-p| * normalizedProjectiveHorizontalFirstMoment t alpha := by
      rw [integral_const_mul]
      rfl
    _ =
    normalizedProjectiveHorizontalFirstMoment t alpha * |q-p| := by ring

/-- Signed near-q compiler: a negative q=0 margin persists while its Lipschitz
variation is smaller than that margin. -/
theorem normalizedProjectiveHorizontalQuadratic_neg_of_near_zero
    {t alpha q : ℝ}
    (hzero : normalizedProjectiveHorizontalQuadratic t alpha 0 < 0)
    (hnear :
      normalizedProjectiveHorizontalFirstMoment t alpha * |q|
        < - normalizedProjectiveHorizontalQuadratic t alpha 0) :
    normalizedProjectiveHorizontalQuadratic t alpha q < 0 := by
  have hlip :=
    normalizedProjectiveHorizontalQuadratic_lipschitz t alpha 0 q
  rw [sub_zero, abs_sub_comm q 0, sub_zero] at hlip
  have hupper :
      normalizedProjectiveHorizontalQuadratic t alpha q
        ≤ normalizedProjectiveHorizontalQuadratic t alpha 0
          + normalizedProjectiveHorizontalFirstMoment t alpha * |q| := by
    exact (le_abs_self
      (normalizedProjectiveHorizontalQuadratic t alpha q
        - normalizedProjectiveHorizontalQuadratic t alpha 0)).trans hlip
      |> fun h => by linarith
  linarith

/-- Actual-zero specialization of the signed near-q criterion. -/
theorem normalizedProjectiveHorizontalQuadratic_actualZero_neg_of_near
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeta23Bridge.LiteralWeilParityBalance.Zeros}
    (him : ((rho :
      Zeta23Bridge.LiteralWeilParityBalance.Zeros) : ℂ).im = t)
    (hoff :
      Zeta23Bridge.LiteralWeilSameOrdinateEvenCone.heightOf rho ≠ 0)
    {q : ℝ}
    (hnear :
      normalizedProjectiveHorizontalFirstMoment t
          (normalizedHorizontalHeight t rho) * |q|
        <
      - normalizedProjectiveHorizontalQuadratic t
          (normalizedHorizontalHeight t rho) 0) :
    normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t rho) q < 0 := by
  exact normalizedProjectiveHorizontalQuadratic_neg_of_near_zero
    (normalizedProjectiveHorizontalQuadratic_sameOrd_neg ht him hoff)
    hnear

end Synthesis

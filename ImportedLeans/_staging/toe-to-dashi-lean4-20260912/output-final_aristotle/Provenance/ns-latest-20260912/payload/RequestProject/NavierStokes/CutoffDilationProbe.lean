/-
# The cut-off scale-neutral weight, in three dimensions, against a general field

`GeneralDilationProbe.lean` proves, for *any* `C¹` field `U` on `ℝ³` and any
compactly supported `C¹` weight `Φ`,

  `∫ Φ·⟪x, ΛU⟫ = − ∫ (DΦ(x)x + 3Φ(x))·⟪x, U⟫`.

This file instantiates the weight.  For a radial weight `Φ(x) = f(‖x‖)` the
scale residual is the one-dimensional expression

  `DΦ(x)x + 3Φ(x) = r f'(r) + 3 f(r)`,          (`scaleResidual_radWeight`)

which vanishes identically for `f = c/r³` — the scale-invariant weight, which is
not `C¹` at the origin.  Cutting it off, `f = χ(r)/r³`, the residual is

  `r f'(r) + 3 f(r) = χ'(r)/r²`,                (`scaleResidual_cutProfile`)

supported exactly where the cut-off varies.  Hence, for every `C¹` field `U`,

  `∫ (χ(‖x‖)/‖x‖³)·⟪x, ΛU⟫ = − ∫ (χ'(‖x‖)/‖x‖²)·⟪x, U⟫`,
                                            (`cutoff_dilation_probe_adjoint`)

with `ΛU = U + (DU)x` the honest spatial dilation generator.  This is the
non-radial analogue of `ClayNS.radial_cutoff_probe_residual`, and it is what the
dyadic pigeonhole is applied to.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GeneralDilationProbe

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## Radial weights -/

/-- The radial scalar weight attached to a profile `f`. -/
def radWeight (f : ℝ → ℝ) : E3 → ℝ := fun x => f ‖x‖

@[simp] lemma radWeight_apply (f : ℝ → ℝ) (x : E3) : radWeight f x = f ‖x‖ := rfl

/-- A radial weight whose profile is `C¹` and vanishes near the origin is `C¹`
on all of `ℝ³`, the origin included. -/
lemma contDiff_radWeight {f f' : ℝ → ℝ} (hf : ∀ r, HasDerivAt f (f' r) r)
    (hf'c : Continuous f') {r1 : ℝ} (hr1 : 0 < r1) (hz : ∀ r, r ≤ r1 → f r = 0) :
    ContDiff ℝ (1 : ℕ) (radWeight f) := by
  have hfC : ContDiff ℝ (1 : ℕ) f := by
    have hd : deriv f = f' := funext fun r => (hf r).deriv
    have : ContDiff ℝ 1 f := contDiff_one_iff_deriv.2
      ⟨fun r => (hf r).differentiableAt, by rw [hd]; exact hf'c⟩
    exact_mod_cast this
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · -- near the origin the weight vanishes identically
    have hball : Metric.ball (0 : E3) r1 ∈ nhds (0 : E3) := Metric.ball_mem_nhds _ hr1
    have hev : radWeight f =ᶠ[nhds (0 : E3)] fun _ => (0 : ℝ) := by
      filter_upwards [hball] with y hy
      have : ‖y‖ < r1 := by simpa [Metric.mem_ball, dist_eq_norm] using hy
      exact hz _ this.le
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · exact hfC.contDiffAt.comp x (contDiffAt_norm (𝕜 := ℝ) hx)

/-- The dilation derivative of a radial weight is `r f'(r)`. -/
lemma fderiv_radWeight_self {f f' : ℝ → ℝ} (hf : ∀ r, HasDerivAt f (f' r) r) {x : E3}
    (hx : x ≠ 0) : fderiv ℝ (radWeight f) x x = ‖x‖ * f' ‖x‖ := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hcomp : HasFDerivAt (radWeight f)
      ((f' ‖x‖) • ((‖x‖⁻¹ : ℝ) • (innerSL ℝ x))) x :=
    (hf ‖x‖).comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)
  rw [hcomp.fderiv]
  have hinner : (innerSL ℝ x) x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  simp only [ContinuousLinearMap.smul_apply, hinner, smul_eq_mul]
  field_simp

/-- **The scale residual of a radial weight.**  It is the one-dimensional
expression `r f'(r) + 3f(r)`, which vanishes identically exactly for the
scale-invariant profile `f = c/r³`. -/
lemma scaleResidual_radWeight {f f' : ℝ → ℝ} (hf : ∀ r, HasDerivAt f (f' r) r) {x : E3}
    (hx : x ≠ 0) : scaleResidual (radWeight f) x = ‖x‖ * f' ‖x‖ + 3 * f ‖x‖ := by
  rw [scaleResidual, fderiv_radWeight_self hf hx]
  rfl

/-! ## The cut-off scale-invariant profile -/

/-- The cut-off scale-invariant radial profile `χ(r)/r³`. -/
def cutProfile (chi : ℝ → ℝ) : ℝ → ℝ := fun r => chi r / r ^ 3

/-- Its derivative. -/
def cutProfile' (chi chi' : ℝ → ℝ) : ℝ → ℝ := fun r => chi' r / r ^ 3 - 3 * chi r / r ^ 4

lemma hasDerivAt_cutProfile_of_ne {chi chi' : ℝ → ℝ} (hchi : ∀ r, HasDerivAt chi (chi' r) r)
    {r : ℝ} (hr : r ≠ 0) : HasDerivAt (cutProfile chi) (cutProfile' chi chi' r) r := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ 3) (3 * r ^ 2) r := by
    simpa using (hasDerivAt_pow 3 r)
  have hne : (r : ℝ) ^ 3 ≠ 0 := pow_ne_zero _ hr
  have h := (hchi r).div hpow hne
  refine h.congr_deriv ?_
  simp only [cutProfile']
  field_simp

/-- The profile and its derivative vanish where the cut-off does. -/
lemma cutProfile_eq_zero {chi : ℝ → ℝ} {r : ℝ} (h : chi r = 0) : cutProfile chi r = 0 := by
  simp [cutProfile, h]

lemma cutProfile'_eq_zero {chi chi' : ℝ → ℝ} {r : ℝ} (h : chi r = 0) (h' : chi' r = 0) :
    cutProfile' chi chi' r = 0 := by
  simp [cutProfile', h, h']

/-- Off the origin the cut-off profile is differentiable; at the origin it
vanishes identically nearby, so it is differentiable there too. -/
lemma hasDerivAt_cutProfile {chi chi' : ℝ → ℝ} (hchi : ∀ r, HasDerivAt chi (chi' r) r)
    {a1 : ℝ} (ha1 : 0 < a1) (hz : ∀ r, r ≤ a1 → chi r = 0) (hz' : ∀ r, r ≤ a1 → chi' r = 0)
    (r : ℝ) : HasDerivAt (cutProfile chi) (cutProfile' chi chi' r) r := by
  rcases eq_or_ne r 0 with rfl | hr
  · have hev : cutProfile chi =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with s hs
      have : |s| < a1 := by simpa [Real.dist_eq] using hs
      exact cutProfile_eq_zero (hz s ((le_abs_self s).trans this.le))
    have h0 : cutProfile' chi chi' 0 = 0 :=
      cutProfile'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
    rw [h0]
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  · exact hasDerivAt_cutProfile_of_ne hchi hr

/-- **The residual of the cut-off scale-invariant weight**: `χ'(r)/r²`. -/
lemma scaleResidual_cutProfile {chi chi' : ℝ → ℝ} {r : ℝ} (hr : r ≠ 0) :
    r * cutProfile' chi chi' r + 3 * cutProfile chi r = chi' r / r ^ 2 := by
  simp only [cutProfile, cutProfile']
  field_simp
  ring

/-! ## The adjoint identity for the cut-off weight -/

/-- **The cut-off dilation probe against an arbitrary field.**  For every `C¹`
field `U` on `ℝ³` and every `C¹` cut-off `χ` supported in `[a₁,b₂] ⊂ (0,∞)`,

  `∫ (χ(‖x‖)/‖x‖³)·⟪x, ΛU(x)⟫ dx = − ∫ (χ'(‖x‖)/‖x‖²)·⟪x, U(x)⟫ dx`,

where `ΛU = U + (DU)x`.  The left-hand side is the probe of the scaling
direction; the right-hand side is supported where the cut-off varies. -/
theorem cutoff_dilation_probe_adjoint {chi chi' : ℝ → ℝ} {U : E3 → E3}
    (hchi : ∀ r, HasDerivAt chi (chi' r) r) (hchi'c : Continuous chi')
    {a1 b2 : ℝ} (ha1 : 0 < a1) (hb2 : a1 < b2)
    (hz : ∀ r, r ≤ a1 → chi r = 0) (hz' : ∀ r, r ≤ a1 → chi' r = 0)
    (hzb : ∀ r, b2 ≤ r → chi r = 0)
    (hU : ContDiff ℝ (1 : ℕ) U) :
    (∫ x : E3, dilProbe (radWeight (cutProfile chi)) (dilGen U) x)
      = - ∫ x : E3, (chi' ‖x‖ / ‖x‖ ^ 2) * radPair U x := by
  have hderiv := hasDerivAt_cutProfile hchi ha1 hz hz'
  have hcont' : Continuous (cutProfile' chi chi') := by
    have hchic : Continuous chi := continuous_iff_continuousAt.2 fun r =>
      (hchi r).continuousAt
    -- continuity away from the origin, and local vanishing at the origin
    rw [continuous_iff_continuousAt]
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · have hev : cutProfile' chi chi' =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with s hs
        have habs : |s| < a1 := by simpa [Real.dist_eq] using hs
        exact cutProfile'_eq_zero (hz s ((le_abs_self s).trans habs.le))
          (hz' s ((le_abs_self s).trans habs.le))
      have h0 : cutProfile' chi chi' 0 = 0 :=
        cutProfile'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
      rw [ContinuousAt, h0]
      exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
    · exact ContinuousAt.sub
        (ContinuousAt.div hchi'c.continuousAt (continuousAt_pow r 3) (pow_ne_zero _ hr))
        (ContinuousAt.div (continuousAt_const.mul hchic.continuousAt)
          (continuousAt_pow r 4) (pow_ne_zero _ hr))
  have hPhiC : ContDiff ℝ (1 : ℕ) (radWeight (cutProfile chi)) :=
    contDiff_radWeight hderiv hcont' (r1 := a1 / 2) (by positivity)
      (fun r hr => cutProfile_eq_zero (hz r (by linarith)))
  have hsupp : ∀ x : E3, b2 ≤ ‖x‖ → radWeight (cutProfile chi) x = 0 := by
    intro x hx
    exact cutProfile_eq_zero (hzb _ hx)
  have hadj := dilation_probe_adjoint hPhiC hU (L := b2) (by linarith) hsupp
  rw [hadj]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show scaleResidual (radWeight (cutProfile chi)) x * radPair U x
      = chi' ‖x‖ / ‖x‖ ^ 2 * radPair U x
  rcases eq_or_ne x 0 with rfl | hx
  · have h1 : scaleResidual (radWeight (cutProfile chi)) (0 : E3) = 0 := by
      simp only [scaleResidual, radWeight_apply, norm_zero]
      rw [cutProfile_eq_zero (hz 0 ha1.le)]
      simp
    have h2 : chi' ‖(0 : E3)‖ / ‖(0 : E3)‖ ^ 2 = 0 := by
      simp [hz' 0 ha1.le]
    rw [h1, h2]
  · rw [scaleResidual_radWeight hderiv hx,
      scaleResidual_cutProfile (chi := chi) (chi' := chi') (norm_ne_zero_iff.2 hx)]

end ClayNS

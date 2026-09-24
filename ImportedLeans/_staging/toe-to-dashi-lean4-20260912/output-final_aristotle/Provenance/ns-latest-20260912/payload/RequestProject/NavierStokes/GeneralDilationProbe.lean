/-
# The dilation-probe adjoint identity for an arbitrary field

`ScaleProbeRadial.lean` computes the adjoint of the dilation generator against a
*radial* weight paired with a *radial* profile, by a one-dimensional integration
by parts in the radius.  The blow-up profile of Navier–Stokes is not radial, so
that identity, as it stands, does not apply to it.

This file removes the radiality assumption completely.  The mechanism is that
the cancellation lives entirely in the *weight*: for a scalar weight `Φ` and the
radial-pairing observable

  `p(x) = ⟪x, U x⟫`

the vector field `F(x) = Φ(x)·p(x)·x` has divergence

  `div F = Φ·⟪x, ΛU⟫ + (DΦ(x)x + 3Φ(x))·p`,               (`dilation_flux_div`)

where `ΛU = U + (DU)x` is the spatial dilation generator.  No structure of `U`
is used: the identity is a pointwise consequence of the product rule.
Integrating it against the compactly supported divergence theorem of
`CompactDivergence.lean` gives

  `∫ Φ·⟪x, ΛU⟫ = − ∫ (DΦ(x)x + 3Φ(x))·⟪x, U⟫`,        (`dilation_probe_adjoint`)

the exact analogue of `ClayNS.radial_probe_adjoint` for a general `C¹` field.
The coefficient `DΦ(x)x + 3Φ(x)` is the **scale residual** of the weight: it
vanishes identically precisely when `Φ` is homogeneous of degree `−3`, i.e. for
the scale-invariant weight, which is exactly the no-go of
`ClayNS.scaleNeutral_no_go` in the three-dimensional carrier — such a `Φ` cannot
be `C¹` at the origin, so it has to be cut off, and the residual is supported
where the cut-off varies.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.CompactDivergence
import RequestProject.NavierStokes.SpatialScaleGen

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The objects -/

/-- The **radial pairing observable** `p(x) = ⟪x, U x⟫`.  This is the scalar
observable the probe measures; no radiality of `U` is assumed. -/
def radPair (U : E3 → E3) (x : E3) : ℝ := ∑ a, x a * U x a

/-- The **spatial dilation generator** `ΛU = U + (DU)x`. -/
def dilGen (U : E3 → E3) (x : E3) : E3 := U x + fderiv ℝ U x x

/-- The **scale residual of a weight**: `DΦ(x)x + 3Φ(x)`.  It vanishes
identically exactly for weights homogeneous of degree `−3`. -/
def scaleResidual (Phi : E3 → ℝ) (x : E3) : ℝ := fderiv ℝ Phi x x + 3 * Phi x

/-- The probe of a field by the weight `Φ`: the pairing of `Φ(x)·x` with the
field. -/
def dilProbe (Phi : E3 → ℝ) (W : E3 → E3) (x : E3) : ℝ := Phi x * ∑ a, x a * W x a

lemma dilProbe_eq (Phi : E3 → ℝ) (W : E3 → E3) (x : E3) :
    dilProbe Phi W x = ∑ a, (Phi x * x a) * W x a := by
  simp [dilProbe, Finset.mul_sum, mul_assoc]

/-! ## Coordinate calculus -/

lemma contDiff_coordFun (a : Fin 3) : ContDiff ℝ (1 : ℕ) (fun x : E3 => x a) :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff

lemma fderiv_coordFun (a : Fin 3) (x h : E3) : fderiv ℝ (fun x : E3 => x a) x h = h a :=
  congrFun (congrArg _ ((EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.fderiv)) h

lemma hasFDerivAt_coordFun (a : Fin 3) (x : E3) :
    HasFDerivAt (fun x : E3 => x a) (EuclideanSpace.proj (𝕜 := ℝ) a) x :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt

/-- Reassembling a directional derivative along `x` from its coordinates. -/
lemma fderiv_apply_self {f : E3 → ℝ} {x : E3} :
    ∑ i, x i * fderiv ℝ f x (ee i) = fderiv ℝ f x x := by
  rw [← sum_smul_ee x, map_sum]
  simp [sum_smul_ee]

/-! ## The pointwise divergence identity -/

lemma hasFDerivAt_radPair {U : E3 → E3} {x : E3} (hU : DifferentiableAt ℝ U x) :
    HasFDerivAt (radPair U)
      (∑ a, ((x a) • ((EuclideanSpace.proj (𝕜 := ℝ) a).comp (fderiv ℝ U x))
        + (U x a) • (EuclideanSpace.proj (𝕜 := ℝ) a))) x := by
  refine HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    (A := fun a (y : E3) => y a * U y a) (fun a _ => ?_)
  exact (hasFDerivAt_coordFun a x).fun_mul
    ((EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.comp x hU.hasFDerivAt)

lemma differentiableAt_radPair {U : E3 → E3} {x : E3} (hU : DifferentiableAt ℝ U x) :
    DifferentiableAt ℝ (radPair U) x :=
  (hasFDerivAt_radPair hU).differentiableAt

lemma fderiv_radPair_apply {U : E3 → E3} {x : E3} (hU : DifferentiableAt ℝ U x) (h : E3) :
    fderiv ℝ (radPair U) x h = ∑ a, (h a * U x a + x a * (fderiv ℝ U x h) a) := by
  rw [(hasFDerivAt_radPair hU).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show x a * ((fderiv ℝ U x) h) a + (U x) a * h a = h a * (U x) a + x a * ((fderiv ℝ U x) h) a
  ring

/-- **The pointwise divergence identity.**  For any `C¹` field `U` and any `C¹`
weight `Φ`, the flux `F(x) = Φ(x)·⟪x,U x⟫·x` satisfies

  `div F = Φ·⟪x, ΛU⟫ + (DΦ(x)x + 3Φ(x))·⟪x, U x⟫`. -/
theorem dilation_flux_div {Phi : E3 → ℝ} {U : E3 → E3} {x : E3}
    (hPhi : DifferentiableAt ℝ Phi x) (hU : DifferentiableAt ℝ U x) :
    ∑ i, fderiv ℝ (fun y : E3 => Phi y * radPair U y * y i) x (ee i)
      = dilProbe Phi (dilGen U) x + scaleResidual Phi x * radPair U x := by
  have hf : DifferentiableAt ℝ (fun y : E3 => Phi y * radPair U y) x :=
    hPhi.mul (differentiableAt_radPair hU)
  have hterm : ∀ i : Fin 3,
      fderiv ℝ (fun y : E3 => Phi y * radPair U y * y i) x (ee i)
        = x i * fderiv ℝ (fun y : E3 => Phi y * radPair U y) x (ee i)
          + (Phi x * radPair U x) := by
    intro i
    have hg : DifferentiableAt ℝ (fun y : E3 => y i) x := (contDiff_coordFun i).differentiable
      (by simp) x
    rw [fderiv_fun_mul hf hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_coordFun i x (ee i)]
    have : (ee i) i = 1 := by simp [ee, EuclideanSpace.single_apply]
    rw [this]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib, fderiv_apply_self]
  have hdf : fderiv ℝ (fun y : E3 => Phi y * radPair U y) x x
      = radPair U x * fderiv ℝ Phi x x + Phi x * fderiv ℝ (radPair U) x x := by
    rw [fderiv_fun_mul hPhi (differentiableAt_radPair hU)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hdf]
  have hdp : fderiv ℝ (radPair U) x x = ∑ a, (x a * U x a + x a * (fderiv ℝ U x x) a) :=
    fderiv_radPair_apply hU x
  have hgen : ∑ a, x a * dilGen U x a = radPair U x + ∑ a, x a * (fderiv ℝ U x x) a := by
    simp only [dilGen, radPair]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun a _ => by simp [mul_add])
  have hsplit : (∑ a, (x a * U x a + x a * (fderiv ℝ U x x) a))
      = radPair U x + ∑ a, x a * (fderiv ℝ U x x) a := by
    rw [Finset.sum_add_distrib]; rfl
  rw [hdp, hsplit]
  simp only [dilProbe, scaleResidual, hgen, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## The adjoint identity -/

/-- **The dilation-probe adjoint identity, for an arbitrary `C¹` field.**  If the
weight `Φ` is `C¹` and vanishes outside a bounded set, then

  `∫ Φ(x)·⟪x, ΛU(x)⟫ dx = − ∫ (DΦ(x)x + 3Φ(x))·⟪x, U(x)⟫ dx`.

No radiality, no self-similarity and no time-independence of `U` is used. -/
theorem dilation_probe_adjoint {Phi : E3 → ℝ} {U : E3 → E3}
    (hPhi : ContDiff ℝ (1 : ℕ) Phi) (hU : ContDiff ℝ (1 : ℕ) U) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ x : E3, L ≤ ‖x‖ → Phi x = 0) :
    (∫ x : E3, dilProbe Phi (dilGen U) x)
      = - ∫ x : E3, scaleResidual Phi x * radPair U x := by
  classical
  set F : Fin 3 → E3 → ℝ := fun i y => Phi y * radPair U y * y i with hF
  have hradC : ContDiff ℝ (1 : ℕ) (radPair U) := by
    refine ContDiff.sum (fun a _ => ?_)
    exact (contDiff_coordFun a).mul ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp hU)
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (F i) := fun i =>
    (hPhi.mul hradC).mul (contDiff_coordFun i)
  have hFsupp : ∀ (i : Fin 3) (x : E3), L ≤ ‖x‖ → F i x = 0 := by
    intro i x hx
    simp [hF, hsupp x hx]
  have hzero := integral_divergence_eq_zero_of_vanishing_outside F hFC hL hFsupp
  have hpt : ∀ x : E3, (∑ i, fderiv ℝ (F i) x (ee i))
      = dilProbe Phi (dilGen U) x + scaleResidual Phi x * radPair U x := by
    intro x
    exact dilation_flux_div (hPhi.differentiable (by simp) x) (hU.differentiable (by simp) x)
  rw [funext hpt] at hzero
  -- integrability: both summands are continuous and supported in the ball of radius `L`
  have hfdPhi : Continuous (fun x : E3 => fderiv ℝ Phi x) := hPhi.continuous_fderiv (by simp)
  have hfdU : Continuous (fun x : E3 => fderiv ℝ U x) := hU.continuous_fderiv (by simp)
  have hcontRad : Continuous (radPair U) := hradC.continuous
  have hcontA : Continuous (fun x : E3 => dilProbe Phi (dilGen U) x) := by
    have hgen : Continuous (fun x : E3 => dilGen U x) :=
      hU.continuous.add (hfdU.clm_apply continuous_id)
    refine hPhi.continuous.mul (continuous_finset_sum (Finset.univ : Finset (Fin 3))
      fun a _ => ?_)
    exact (EuclideanSpace.proj (𝕜 := ℝ) a).continuous.mul
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hgen)
  have hcontB : Continuous (fun x : E3 => scaleResidual Phi x * radPair U x) :=
    ((hfdPhi.clm_apply continuous_id).add (continuous_const.mul hPhi.continuous)).mul hcontRad
  have hfdPhi_zero : ∀ x : E3, L < ‖x‖ → fderiv ℝ Phi x = 0 := by
    intro x hx
    have hnb : {y : E3 | L < ‖y‖} ∈ nhds x :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds hx
    have hev : Phi =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with y hy using hsupp y (le_of_lt hy)
    rw [hev.fderiv_eq]
    simp
  have hsuppA : ∀ x : E3, L < ‖x‖ → dilProbe Phi (dilGen U) x = 0 := by
    intro x hx
    simp [dilProbe, hsupp x hx.le]
  have hsuppB : ∀ x : E3, L < ‖x‖ → scaleResidual Phi x * radPair U x = 0 := by
    intro x hx
    simp [scaleResidual, hsupp x hx.le, hfdPhi_zero x hx]
  have hintA : Integrable (fun x : E3 => dilProbe Phi (dilGen U) x) :=
    hcontA.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : E3) L)
        (fun x hx => hsuppA x (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)))
  have hintB : Integrable (fun x : E3 => scaleResidual Phi x * radPair U x) :=
    hcontB.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_closedBall (0 : E3) L)
        (fun x hx => hsuppB x (by simpa [Metric.mem_closedBall, dist_eq_norm] using hx)))
  rw [integral_add hintA hintB] at hzero
  linarith [hzero]

end ClayNS

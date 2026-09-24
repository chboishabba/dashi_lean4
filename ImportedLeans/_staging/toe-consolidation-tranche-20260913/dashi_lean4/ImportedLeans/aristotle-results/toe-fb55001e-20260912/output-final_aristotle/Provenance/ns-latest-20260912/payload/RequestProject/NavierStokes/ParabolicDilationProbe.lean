/-
# The parabolic dilation-probe adjoint identity on spacetime

`GeneralDilationProbe.lean` removed the radiality assumption from the scale
probe, but it worked with the *spatial* dilation generator `ΛU = U + (DU)x` on
`ℝ³`.  The generator that actually appears in the Navier–Stokes blow-up analysis
is the **parabolic** one,

  `Λu = u + (x − x₀)·∇u + 2(t − t₀)∂_t u`,   (`ClayNS.scaleGen`)

acting on genuinely spacetime-dependent fields `U(t,x)`.  This file proves the
adjoint identity for that generator, with no radiality, no self-similarity and
no time-independence of `U`.

The mechanism is again that all the cancellation lives in the weight.  Write
`X(z) = (2t, x)` for the parabolic dilation vector field on spacetime and

  `p(z) = ⟪x, U z⟫`

for the radial-pairing observable.  Two facts drive everything:

* `⟪x, Λu(z)⟫ = X·∇p(z)` — pairing the parabolic generator against `x` is the
  same as differentiating the observable along the parabolic orbit
  (`ClayNS.parRadPair_parGen`);
* `div X = 5` in spacetime, so the flux `F(z) = Φ(z)·p(z)·X(z)` has

    `div F = Φ·⟪x, Λu⟫ + (X·∇Φ + 5Φ)·p`.        (`ClayNS.parabolic_flux_div`)

Integrating against the spacetime divergence theorem of
`SpacetimeDivergence.lean` gives

  `∫ Φ·⟪x, Λu⟫ = − ∫ (X·∇Φ + 5Φ)·⟪x, U⟫`.   (`parabolic_dilation_probe_adjoint`)

The coefficient `X·∇Φ + 5Φ` is the **parabolic scale residual** of the weight.
It vanishes identically exactly for weights that are parabolically homogeneous
of degree `−5`, e.g. `Φ = s^{-5/4}` with `s = ‖x‖⁴ + t²`, since `X·∇s = 4s`.
Such a weight is not `C¹` at the origin, so it has to be cut off; the residual
is then supported precisely where the cut-off varies.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SpacetimeDivergence
import RequestProject.NavierStokes.GeneralDilationProbe
import RequestProject.NavierStokes.GaussianScaleGram

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The objects -/

/-- The **parabolic dilation vector field** `X(t,x) = (2t, x)` on spacetime. -/
def parVec (z : STime) : STime := ((2 * z.1 : ℝ), z.2)

/-- The **radial pairing observable** on spacetime, `p(z) = ⟪x, U z⟫`. -/
def parRadPair (U : STime → E3) (z : STime) : ℝ := ∑ a, z.2 a * U z a

/-- The **parabolic dilation generator** `ΛU = U + (DU)X`, written with the
spacetime derivative along the parabolic vector field. -/
def parGen (U : STime → E3) (z : STime) : E3 := U z + fderiv ℝ U z (parVec z)

/-- The **parabolic scale residual of a weight**: `X·∇Φ + 5Φ`. -/
def parScaleResidual (Phi : STime → ℝ) (z : STime) : ℝ :=
  fderiv ℝ Phi z (parVec z) + 5 * Phi z

/-- The probe of a spacetime field by the weight `Φ`: the pairing of the
spacetime weight `Φ(z)·x` against the field. -/
def parProbe (Phi : STime → ℝ) (W : STime → E3) (z : STime) : ℝ :=
  Phi z * ∑ a, z.2 a * W z a

/-! ## Identification with `scaleGen` -/

/-- Decomposition of the parabolic vector field in the spacetime basis. -/
lemma parVec_decomp (z : STime) :
    parVec z = (2 * z.1) • ((1 : ℝ), (0 : E3)) + ∑ i, (z.2 i) • ((0 : ℝ), ee i) := by
  have hsnd : (∑ i, (z.2 i) • ((0 : ℝ), ee i)) = ((0 : ℝ), z.2) := by
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, sum_smul_ee]
  rw [hsnd]
  simp [parVec]

/-- The parabolic generator, written along the spacetime basis, is exactly
`ClayNS.scaleGen` based at the spacetime origin. -/
theorem parGen_eq_scaleGen {U : STime → E3} {z : STime} :
    parGen U z = scaleGen ((0 : ℝ), (0 : E3)) U z := by
  have hlin : fderiv ℝ U z (parVec z)
      = (2 * z.1) • fderiv ℝ U z (1, 0) + ∑ i, (z.2 i) • fderiv ℝ U z (0, ee i) := by
    rw [parVec_decomp z, map_add, map_smul, map_sum]
    simp only [map_smul]
  simp only [parGen, scaleGen, dvec, hlin]
  simp [add_comm, add_left_comm]

/-! ## Spacetime coordinate calculus -/

/-- The `a`-th spatial coordinate as a continuous linear functional on spacetime. -/
def stProj (a : Fin 3) : STime →L[ℝ] ℝ :=
  (EuclideanSpace.proj (𝕜 := ℝ) a).comp (ContinuousLinearMap.snd ℝ ℝ E3)

lemma stProj_apply (a : Fin 3) (v : STime) : stProj a v = v.2 a := rfl

lemma contDiff_stCoord (a : Fin 3) : ContDiff ℝ (1 : ℕ) (fun z : STime => z.2 a) :=
  (stProj a).contDiff

lemma hasFDerivAt_stCoord (a : Fin 3) (z : STime) :
    HasFDerivAt (fun w : STime => w.2 a) (stProj a) z := (stProj a).hasFDerivAt

lemma fderiv_stCoord (a : Fin 3) (z v : STime) :
    fderiv ℝ (fun w : STime => w.2 a) z v = v.2 a := by
  rw [(hasFDerivAt_stCoord a z).fderiv]; rfl

lemma contDiff_stTime2 : ContDiff ℝ (1 : ℕ) (fun z : STime => 2 * z.1) :=
  (contDiff_const.mul (ContinuousLinearMap.fst ℝ ℝ E3).contDiff)

lemma fderiv_stTime2 (z v : STime) :
    fderiv ℝ (fun w : STime => 2 * w.1) z v = 2 * v.1 := by
  have h : HasFDerivAt (fun w : STime => 2 * w.1)
      ((2 : ℝ) • (ContinuousLinearMap.fst ℝ ℝ E3)) z := by
    simpa using ((ContinuousLinearMap.fst ℝ ℝ E3).hasFDerivAt).const_mul (2 : ℝ)
  rw [h.fderiv]
  rfl

/-! ## Derivative of the observable -/

lemma hasFDerivAt_parRadPair {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z) :
    HasFDerivAt (parRadPair U)
      (∑ a, ((z.2 a) • ((EuclideanSpace.proj (𝕜 := ℝ) a).comp (fderiv ℝ U z))
        + (U z a) • stProj a)) z := by
  refine HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
    (A := fun a (w : STime) => w.2 a * U w a) (fun a _ => ?_)
  exact (hasFDerivAt_stCoord a z).fun_mul
    ((EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.comp z hU.hasFDerivAt)

lemma differentiableAt_parRadPair {U : STime → E3} {z : STime}
    (hU : DifferentiableAt ℝ U z) : DifferentiableAt ℝ (parRadPair U) z :=
  (hasFDerivAt_parRadPair hU).differentiableAt

lemma fderiv_parRadPair_apply {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z)
    (v : STime) :
    fderiv ℝ (parRadPair U) z v = ∑ a, (v.2 a * U z a + z.2 a * (fderiv ℝ U z v) a) := by
  rw [(hasFDerivAt_parRadPair hU).fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    smul_eq_mul, stProj_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show z.2 a * ((fderiv ℝ U z) v) a + (U z) a * v.2 a
      = v.2 a * (U z) a + z.2 a * ((fderiv ℝ U z) v) a
  ring

/-- **Pairing the parabolic generator against `x` differentiates the observable
along the parabolic orbit.** -/
theorem parRadPair_parGen {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z) :
    (∑ a, z.2 a * parGen U z a) = fderiv ℝ (parRadPair U) z (parVec z) := by
  rw [fderiv_parRadPair_apply hU]
  have hv : (parVec z).2 = z.2 := rfl
  simp only [hv, parGen]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  show z.2 a * (U z a + (fderiv ℝ U z (parVec z)) a)
      = z.2 a * U z a + z.2 a * (fderiv ℝ U z (parVec z)) a
  ring

/-! ## The pointwise divergence identity -/

/-- **The pointwise spacetime divergence identity.**  For any `C¹` field `U` and
any `C¹` weight `Φ`, the spacetime flux `F(z) = Φ(z)·⟪x, U z⟫·X(z)` with
`X(z) = (2t, x)` satisfies

  `div F = Φ·⟪x, ΛU⟫ + (X·∇Φ + 5Φ)·⟪x, U z⟫`. -/
theorem parabolic_flux_div {Phi : STime → ℝ} {U : STime → E3} {z : STime}
    (hPhi : DifferentiableAt ℝ Phi z) (hU : DifferentiableAt ℝ U z) :
    fderiv ℝ (fun w : STime => Phi w * parRadPair U w * (2 * w.1)) z (1, 0)
      + ∑ i, fderiv ℝ (fun w : STime => Phi w * parRadPair U w * (w.2 i)) z (0, ee i)
      = parProbe Phi (parGen U) z + parScaleResidual Phi z * parRadPair U z := by
  classical
  set h : STime → ℝ := fun w => Phi w * parRadPair U w with hh
  have hdh : DifferentiableAt ℝ h z := hPhi.mul (differentiableAt_parRadPair hU)
  -- the time term
  have hterm0 : fderiv ℝ (fun w : STime => h w * (2 * w.1)) z (1, 0)
      = (2 * z.1) * fderiv ℝ h z (1, 0) + 2 * h z := by
    have hg : DifferentiableAt ℝ (fun w : STime => 2 * w.1) z :=
      contDiff_stTime2.differentiable (by simp) z
    rw [fderiv_fun_mul hdh hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_stTime2 z (1, 0)]
    ring
  -- the space terms
  have htermi : ∀ i : Fin 3,
      fderiv ℝ (fun w : STime => Phi w * parRadPair U w * (w.2 i)) z (0, ee i)
      = (z.2 i) * fderiv ℝ h z (0, ee i) + h z := by
    intro i
    rw [show (fun w : STime => Phi w * parRadPair U w * (w.2 i))
        = fun w : STime => h w * (w.2 i) from rfl]
    have hg : DifferentiableAt ℝ (fun w : STime => w.2 i) z :=
      (contDiff_stCoord i).differentiable (by simp) z
    rw [fderiv_fun_mul hdh hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_stCoord i z (0, ee i)]
    have hee : ((0 : ℝ), ee i).2 i = 1 := by simp [ee, EuclideanSpace.single_apply]
    rw [hee]
    ring
  rw [hterm0, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => htermi i),
    Finset.sum_add_distrib]
  -- reassemble the directional derivative along `X`
  have hdir : fderiv ℝ h z (parVec z)
      = (2 * z.1) * fderiv ℝ h z (1, 0) + ∑ i, (z.2 i) * fderiv ℝ h z (0, ee i) := by
    rw [parVec_decomp z, map_add, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : (∑ _i : Fin 3, h z) = 3 * h z := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum]
  -- expand the product rule for `h = Φ·p`
  have hexp : fderiv ℝ h z (parVec z)
      = parRadPair U z * fderiv ℝ Phi z (parVec z)
        + Phi z * fderiv ℝ (parRadPair U) z (parVec z) := by
    rw [hh, fderiv_fun_mul hPhi (differentiableAt_parRadPair hU)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hgen : Phi z * fderiv ℝ (parRadPair U) z (parVec z) = parProbe Phi (parGen U) z := by
    rw [← parRadPair_parGen hU]
    rfl
  have hkey : (2 * z.1) * fderiv ℝ h z (1, 0) + ∑ i, (z.2 i) * fderiv ℝ h z (0, ee i)
      = parRadPair U z * fderiv ℝ Phi z (parVec z) + parProbe Phi (parGen U) z := by
    rw [← hdir, hexp, hgen]
  have hval : h z = Phi z * parRadPair U z := rfl
  simp only [parScaleResidual]
  linear_combination hkey + 5 * hval

/-! ## The adjoint identity -/

/-- **The parabolic dilation-probe adjoint identity.**  If the weight `Φ` is
`C¹` on spacetime and vanishes outside a bounded set, then for every `C¹` field
`U` on spacetime

  `∫ Φ(z)·⟪x, ΛU(z)⟫ dz = − ∫ (X·∇Φ(z) + 5Φ(z))·⟪x, U(z)⟫ dz`,

where `Λ` is the parabolic scaling generator based at the spacetime origin and
`X(z) = (2t, x)`.  No radiality, no self-similarity and no time-independence of
`U` is used. -/
theorem parabolic_dilation_probe_adjoint {Phi : STime → ℝ} {U : STime → E3}
    (hPhi : ContDiff ℝ (1 : ℕ) Phi) (hU : ContDiff ℝ (1 : ℕ) U) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ z : STime, L ≤ ‖z‖ → Phi z = 0) :
    (∫ z : STime, parProbe Phi (parGen U) z)
      = - ∫ z : STime, parScaleResidual Phi z * parRadPair U z := by
  classical
  have hpC : ContDiff ℝ (1 : ℕ) (parRadPair U) := by
    refine ContDiff.sum (fun a _ => ?_)
    exact (contDiff_stCoord a).mul ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp hU)
  have hhC : ContDiff ℝ (1 : ℕ) (fun w : STime => Phi w * parRadPair U w) := hPhi.mul hpC
  set F0 : STime → ℝ := fun w => Phi w * parRadPair U w * (2 * w.1) with hF0def
  set F : Fin 3 → STime → ℝ := fun i w => Phi w * parRadPair U w * (w.2 i) with hFdef
  have hF0C : ContDiff ℝ (1 : ℕ) F0 := hhC.mul contDiff_stTime2
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (F i) := fun i => hhC.mul (contDiff_stCoord i)
  have hF0supp : ∀ z : STime, L ≤ ‖z‖ → F0 z = 0 := by
    intro z hz; simp [hF0def, hsupp z hz]
  have hFsupp : ∀ (i : Fin 3) (z : STime), L ≤ ‖z‖ → F i z = 0 := by
    intro i z hz; simp [hFdef, hsupp z hz]
  have hzero := integral_spacetime_divergence_eq_zero F0 F hF0C hFC hL hF0supp hFsupp
  have hpt : ∀ z : STime, fderiv ℝ F0 z (1, 0) + ∑ i, fderiv ℝ (F i) z (0, ee i)
      = parProbe Phi (parGen U) z + parScaleResidual Phi z * parRadPair U z := by
    intro z
    exact parabolic_flux_div (hPhi.differentiable (by simp) z) (hU.differentiable (by simp) z)
  rw [funext hpt] at hzero
  -- integrability of the two pieces
  have hfdPhi : Continuous (fun z : STime => fderiv ℝ Phi z) := hPhi.continuous_fderiv (by simp)
  have hfdU : Continuous (fun z : STime => fderiv ℝ U z) := hU.continuous_fderiv (by simp)
  have hcontX : Continuous parVec := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_const.mul continuous_fst
  have hcontGen : Continuous (parGen U) := hU.continuous.add (hfdU.clm_apply hcontX)
  have hcontA : Continuous (fun z : STime => parProbe Phi (parGen U) z) := by
    refine hPhi.continuous.mul (continuous_finset_sum (Finset.univ : Finset (Fin 3))
      fun a _ => ?_)
    exact ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp continuous_snd).mul
      ((EuclideanSpace.proj (𝕜 := ℝ) a).continuous.comp hcontGen)
  have hcontB : Continuous (fun z : STime => parScaleResidual Phi z * parRadPair U z) :=
    ((hfdPhi.clm_apply hcontX).add (continuous_const.mul hPhi.continuous)).mul hpC.continuous
  have hfdPhi_zero : ∀ z : STime, L < ‖z‖ → fderiv ℝ Phi z = 0 :=
    fun z hz => fderiv_eq_zero_of_vanishing_outside hsupp hz
  have hsuppA : ∀ z : STime, L < ‖z‖ → parProbe Phi (parGen U) z = 0 := by
    intro z hz; simp [parProbe, hsupp z hz.le]
  have hsuppB : ∀ z : STime, L < ‖z‖ → parScaleResidual Phi z * parRadPair U z = 0 := by
    intro z hz
    simp [parScaleResidual, hsupp z hz.le, hfdPhi_zero z hz]
  have hintA : Integrable (fun z : STime => parProbe Phi (parGen U) z) :=
    integrable_of_continuous_of_vanishing hcontA hsuppA
  have hintB : Integrable (fun z : STime => parScaleResidual Phi z * parRadPair U z) :=
    integrable_of_continuous_of_vanishing hcontB hsuppB
  rw [integral_add hintA hintB] at hzero
  linarith [hzero]

end ClayNS

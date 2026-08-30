/-
# The quadratic (energy) parabolic scale probe

`ParabolicCutoffProbe.lean` builds the *linear* parabolic scale probe: it pairs
the parabolic scaling generator `Λ` against the weight `Φ(z)·x` and produces

  `∫ (χ(s)/s^{5/4})·⟪x, ΛU⟫ = − ∫ 4χ'(s)·s^{-1/4}·⟪x, U⟫`.

Its anchor is the **signed** dilation mass `m = ∫ ⟪x,U⟫/s^{5/4}`, which can
vanish by cancellation even for a nonzero profile.  This file builds the
quadratic analogue, whose anchor is manifestly positive.

The mechanism.  With `X(z) = (2t, x)` the parabolic dilation field and
`q = ½|U|²` the energy density,

  `X·∇q = ⟪U, (DU)X⟫`,   hence   `⟪U, ΛU⟫ = |U|² + X·∇q = 2q + X·∇q`,

(`ClayNS.parEnergyPair_eq`).  Since `div X = 5`, the scalar flux `F = Φ q X`
has `div F = Φ·(X·∇q) + (X·∇Φ + 5Φ)·q`, so compact support gives the exact
adjoint identity

  `∫ Φ·⟪U, ΛU⟫ = − ∫ q·(X·∇Φ + 3Φ)`,   (`quadratic_parabolic_probe_adjoint`)

the `5` having become a `3` because two units of `Φ q` were spent turning
`X·∇q` into `⟪U, ΛU⟫`.  In the parabolic gauge `s = ‖x‖⁴+t²` (`X·∇s = 4s`) the
residual of `Φ = χ(s)·s^{-3/4}` is `4χ'(s)·s^{1/4}`, so

  `∫ (χ(s)/s^{3/4})·⟪U, ΛU⟫ = − 4∫ χ'(s)·s^{1/4}·q`.
                              (`quadratic_parabolic_cutoff_probe_adjoint`)

The anchor of this probe is `∫ (χ(s)/s^{3/4})·|U|²`, a integral of a
**nonnegative** density: there is no cancellation, and it is positive as soon
as `U` is nonzero somewhere.

Contents:
* `ClayNS.parabolic_scalar_flux_div`, `ClayNS.parabolic_transport_adjoint` — the
  adjoint identity for the parabolic transport operator `g ↦ X·∇g` acting on an
  arbitrary `C¹` scalar observable (the linear probe is the case
  `g = ⟪x, U⟫`);
* `ClayNS.parEnergy`, `ClayNS.parEnergyPair`, `ClayNS.parEnergyPair_eq`;
* `ClayNS.quadratic_parabolic_probe_adjoint`;
* `ClayNS.parCutProfile3`, `ClayNS.parScaleResidual3_parCut3`,
  `ClayNS.quadratic_parabolic_cutoff_probe_adjoint`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ParabolicCutoffProbe

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The adjoint identity for parabolic transport of a scalar observable -/

/-- **The pointwise spacetime divergence identity for a scalar observable.**
For any `C¹` scalar `g` and any `C¹` weight `Φ`, the spacetime flux
`F(z) = Φ(z)·g(z)·X(z)` with `X(z) = (2t, x)` satisfies

  `div F = Φ·(X·∇g) + (X·∇Φ + 5Φ)·g`. -/
theorem parabolic_scalar_flux_div {Phi g : STime → ℝ} {z : STime}
    (hPhi : DifferentiableAt ℝ Phi z) (hg : DifferentiableAt ℝ g z) :
    fderiv ℝ (fun w : STime => Phi w * g w * (2 * w.1)) z (1, 0)
      + ∑ i, fderiv ℝ (fun w : STime => Phi w * g w * (w.2 i)) z (0, ee i)
      = Phi z * fderiv ℝ g z (parVec z) + parScaleResidual Phi z * g z := by
  classical
  set h : STime → ℝ := fun w => Phi w * g w with hh
  have hdh : DifferentiableAt ℝ h z := hPhi.mul hg
  have hterm0 : fderiv ℝ (fun w : STime => h w * (2 * w.1)) z (1, 0)
      = (2 * z.1) * fderiv ℝ h z (1, 0) + 2 * h z := by
    have hgd : DifferentiableAt ℝ (fun w : STime => 2 * w.1) z :=
      contDiff_stTime2.differentiable (by simp) z
    rw [fderiv_fun_mul hdh hgd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_stTime2 z (1, 0)]
    ring
  have htermi : ∀ i : Fin 3,
      fderiv ℝ (fun w : STime => Phi w * g w * (w.2 i)) z (0, ee i)
      = (z.2 i) * fderiv ℝ h z (0, ee i) + h z := by
    intro i
    rw [show (fun w : STime => Phi w * g w * (w.2 i)) = fun w : STime => h w * (w.2 i) from rfl]
    have hgd : DifferentiableAt ℝ (fun w : STime => w.2 i) z :=
      (contDiff_stCoord i).differentiable (by simp) z
    rw [fderiv_fun_mul hdh hgd]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [fderiv_stCoord i z (0, ee i)]
    have hee : ((0 : ℝ), ee i).2 i = 1 := by simp [ee, EuclideanSpace.single_apply]
    rw [hee]
    ring
  rw [hterm0, Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => htermi i),
    Finset.sum_add_distrib]
  have hdir : fderiv ℝ h z (parVec z)
      = (2 * z.1) * fderiv ℝ h z (1, 0) + ∑ i, (z.2 i) * fderiv ℝ h z (0, ee i) := by
    rw [parVec_decomp z, map_add, map_smul, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hsum : (∑ _i : Fin 3, h z) = 3 * h z := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [hsum]
  have hexp : fderiv ℝ h z (parVec z)
      = g z * fderiv ℝ Phi z (parVec z) + Phi z * fderiv ℝ g z (parVec z) := by
    rw [hh, fderiv_fun_mul hPhi hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hkey : (2 * z.1) * fderiv ℝ h z (1, 0) + ∑ i, (z.2 i) * fderiv ℝ h z (0, ee i)
      = g z * fderiv ℝ Phi z (parVec z) + Phi z * fderiv ℝ g z (parVec z) := by
    rw [← hdir, hexp]
  have hval : h z = Phi z * g z := rfl
  simp only [parScaleResidual]
  linear_combination hkey + 5 * hval

/-- **The parabolic transport adjoint identity.**  If the weight `Φ` is `C¹` on
spacetime and vanishes outside a bounded set, then for every `C¹` scalar
observable `g`

  `∫ Φ·(X·∇g) = − ∫ (X·∇Φ + 5Φ)·g`,      `X(z) = (2t, x)`.

The linear scale probe is the case `g(z) = ⟪x, U(z)⟫`; the quadratic probe of
this file is the case `g = ½|U|²`. -/
theorem parabolic_transport_adjoint {Phi g : STime → ℝ}
    (hPhi : ContDiff ℝ (1 : ℕ) Phi) (hg : ContDiff ℝ (1 : ℕ) g) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ z : STime, L ≤ ‖z‖ → Phi z = 0) :
    (∫ z : STime, Phi z * fderiv ℝ g z (parVec z))
      = - ∫ z : STime, parScaleResidual Phi z * g z := by
  classical
  have hhC : ContDiff ℝ (1 : ℕ) (fun w : STime => Phi w * g w) := hPhi.mul hg
  set F0 : STime → ℝ := fun w => Phi w * g w * (2 * w.1) with hF0def
  set F : Fin 3 → STime → ℝ := fun i w => Phi w * g w * (w.2 i) with hFdef
  have hF0C : ContDiff ℝ (1 : ℕ) F0 := hhC.mul contDiff_stTime2
  have hFC : ∀ i, ContDiff ℝ (1 : ℕ) (F i) := fun i => hhC.mul (contDiff_stCoord i)
  have hF0supp : ∀ z : STime, L ≤ ‖z‖ → F0 z = 0 := by
    intro z hz; simp [hF0def, hsupp z hz]
  have hFsupp : ∀ (i : Fin 3) (z : STime), L ≤ ‖z‖ → F i z = 0 := by
    intro i z hz; simp [hFdef, hsupp z hz]
  have hzero := integral_spacetime_divergence_eq_zero F0 F hF0C hFC hL hF0supp hFsupp
  have hpt : ∀ z : STime, fderiv ℝ F0 z (1, 0) + ∑ i, fderiv ℝ (F i) z (0, ee i)
      = Phi z * fderiv ℝ g z (parVec z) + parScaleResidual Phi z * g z := fun z =>
    parabolic_scalar_flux_div (hPhi.differentiable (by simp) z)
      (hg.differentiable (by simp) z)
  rw [funext hpt] at hzero
  have hfdPhi : Continuous (fun z : STime => fderiv ℝ Phi z) := hPhi.continuous_fderiv (by simp)
  have hfdg : Continuous (fun z : STime => fderiv ℝ g z) := hg.continuous_fderiv (by simp)
  have hcontX : Continuous parVec := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_const.mul continuous_fst
  have hcontA : Continuous (fun z : STime => Phi z * fderiv ℝ g z (parVec z)) :=
    hPhi.continuous.mul (hfdg.clm_apply hcontX)
  have hcontB : Continuous (fun z : STime => parScaleResidual Phi z * g z) :=
    ((hfdPhi.clm_apply hcontX).add (continuous_const.mul hPhi.continuous)).mul hg.continuous
  have hfdPhi_zero : ∀ z : STime, L < ‖z‖ → fderiv ℝ Phi z = 0 :=
    fun z hz => fderiv_eq_zero_of_vanishing_outside hsupp hz
  have hsuppA : ∀ z : STime, L < ‖z‖ → Phi z * fderiv ℝ g z (parVec z) = 0 := by
    intro z hz; simp [hsupp z hz.le]
  have hsuppB : ∀ z : STime, L < ‖z‖ → parScaleResidual Phi z * g z = 0 := by
    intro z hz
    simp [parScaleResidual, hsupp z hz.le, hfdPhi_zero z hz]
  have hintA : Integrable (fun z : STime => Phi z * fderiv ℝ g z (parVec z)) :=
    integrable_of_continuous_of_vanishing hcontA hsuppA
  have hintB : Integrable (fun z : STime => parScaleResidual Phi z * g z) :=
    integrable_of_continuous_of_vanishing hcontB hsuppB
  rw [integral_add hintA hintB] at hzero
  linarith [hzero]

/-! ## The energy density and the quadratic pairing -/

/-- The **energy density** `q = ½|U|²` of a spacetime field. -/
def parEnergy (U : STime → E3) (z : STime) : ℝ := (1 / 2 : ℝ) * ∑ a, (U z a) ^ 2

lemma parEnergy_nonneg (U : STime → E3) (z : STime) : 0 ≤ parEnergy U z := by
  have : (0 : ℝ) ≤ ∑ a, (U z a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  simp only [parEnergy]; linarith

/-- The **quadratic scale pairing** `⟪U, ΛU⟫`, with `Λ` the parabolic scaling
generator based at the spacetime origin. -/
def parEnergyPair (U : STime → E3) (z : STime) : ℝ := ∑ a, U z a * parGen U z a

lemma contDiff_parEnergy {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U) :
    ContDiff ℝ (1 : ℕ) (parEnergy U) :=
  contDiff_const.mul (ContDiff.sum fun a _ =>
    (((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp hU)).pow 2)

lemma hasFDerivAt_parEnergy {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z) :
    HasFDerivAt (parEnergy U)
      ((1 / 2 : ℝ) • ∑ a, ((2 * U z a) •
        ((EuclideanSpace.proj (𝕜 := ℝ) a).comp (fderiv ℝ U z)))) z := by
  have hsum : HasFDerivAt (fun w : STime => ∑ a, (U w a) ^ 2)
      (∑ a, ((2 * U z a) • ((EuclideanSpace.proj (𝕜 := ℝ) a).comp (fderiv ℝ U z)))) z := by
    refine HasFDerivAt.fun_sum (u := (Finset.univ : Finset (Fin 3)))
      (A := fun a (w : STime) => (U w a) ^ 2) (fun a _ => ?_)
    have h1 : HasFDerivAt (fun w : STime => U w a)
        ((EuclideanSpace.proj (𝕜 := ℝ) a).comp (fderiv ℝ U z)) z :=
      (EuclideanSpace.proj (𝕜 := ℝ) a).hasFDerivAt.comp z hU.hasFDerivAt
    simpa using h1.pow 2
  exact hsum.const_mul (1 / 2 : ℝ)

lemma fderiv_parEnergy_apply {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z)
    (v : STime) :
    fderiv ℝ (parEnergy U) z v = ∑ a, U z a * (fderiv ℝ U z v) a := by
  rw [(hasFDerivAt_parEnergy hU).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (1 / 2 : ℝ) * (2 * U z a * (fderiv ℝ U z v) a) = U z a * (fderiv ℝ U z v) a
  ring

/-- **The quadratic pairing is two units of energy plus the transport of the
energy density**: `⟪U, ΛU⟫ = 2q + X·∇q`. -/
theorem parEnergyPair_eq {U : STime → E3} {z : STime} (hU : DifferentiableAt ℝ U z) :
    parEnergyPair U z = 2 * parEnergy U z + fderiv ℝ (parEnergy U) z (parVec z) := by
  rw [fderiv_parEnergy_apply hU]
  simp only [parEnergyPair, parGen, parEnergy]
  have hsplit : ∀ a : Fin 3, U z a * (U z + fderiv ℝ U z (parVec z)) a
      = (U z a) ^ 2 + U z a * (fderiv ℝ U z (parVec z)) a := by
    intro a
    show U z a * (U z a + (fderiv ℝ U z (parVec z)) a)
        = (U z a) ^ 2 + U z a * (fderiv ℝ U z (parVec z)) a
    ring
  rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hsplit a), Finset.sum_add_distrib]
  ring

/-! ## The quadratic adjoint identity -/

/-- The **reduced parabolic scale residual** `X·∇Φ + 3Φ`, the coefficient
conjugate to the energy density. -/
def parScaleResidual3 (Phi : STime → ℝ) (z : STime) : ℝ :=
  fderiv ℝ Phi z (parVec z) + 3 * Phi z

/-- **The quadratic parabolic probe adjoint identity.**  For every `C¹`
spacetime field `U` and every compactly supported `C¹` weight `Φ`,

  `∫ Φ·⟪U, ΛU⟫ = − ∫ (X·∇Φ + 3Φ)·½|U|²`,

with `Λ` the parabolic scaling generator based at the spacetime origin.  No
radiality, self-similarity or time-independence of `U` is used. -/
theorem quadratic_parabolic_probe_adjoint {Phi : STime → ℝ} {U : STime → E3}
    (hPhi : ContDiff ℝ (1 : ℕ) Phi) (hU : ContDiff ℝ (1 : ℕ) U) {L : ℝ} (hL : 0 < L)
    (hsupp : ∀ z : STime, L ≤ ‖z‖ → Phi z = 0) :
    (∫ z : STime, Phi z * parEnergyPair U z)
      = - ∫ z : STime, parScaleResidual3 Phi z * parEnergy U z := by
  classical
  have hq : ContDiff ℝ (1 : ℕ) (parEnergy U) := contDiff_parEnergy hU
  have hadj := parabolic_transport_adjoint hPhi hq hL hsupp
  have hpt : ∀ z : STime, Phi z * parEnergyPair U z
      = Phi z * fderiv ℝ (parEnergy U) z (parVec z) + 2 * (Phi z * parEnergy U z) := by
    intro z
    rw [parEnergyPair_eq (hU.differentiable (by simp) z)]
    ring
  have hres : ∀ z : STime, parScaleResidual Phi z * parEnergy U z
      = parScaleResidual3 Phi z * parEnergy U z + 2 * (Phi z * parEnergy U z) := by
    intro z
    simp only [parScaleResidual, parScaleResidual3]
    ring
  -- integrability bookkeeping
  have hfdPhi : Continuous (fun z : STime => fderiv ℝ Phi z) := hPhi.continuous_fderiv (by simp)
  have hfdq : Continuous (fun z : STime => fderiv ℝ (parEnergy U) z) :=
    hq.continuous_fderiv (by simp)
  have hcontX : Continuous parVec := by
    refine Continuous.prodMk ?_ continuous_snd
    exact continuous_const.mul continuous_fst
  have hfdPhi_zero : ∀ z : STime, L < ‖z‖ → fderiv ℝ Phi z = 0 :=
    fun z hz => fderiv_eq_zero_of_vanishing_outside hsupp hz
  have hint1 : Integrable (fun z : STime => Phi z * fderiv ℝ (parEnergy U) z (parVec z)) :=
    integrable_of_continuous_of_vanishing (L := L)
      (hPhi.continuous.mul (hfdq.clm_apply hcontX))
      (fun z (hz : L < ‖z‖) => by simp [hsupp z hz.le])
  have hint2 : Integrable (fun z : STime => 2 * (Phi z * parEnergy U z)) :=
    integrable_of_continuous_of_vanishing (L := L)
      (continuous_const.mul (hPhi.continuous.mul hq.continuous))
      (fun z (hz : L < ‖z‖) => by simp [hsupp z hz.le])
  have hint3 : Integrable (fun z : STime => parScaleResidual3 Phi z * parEnergy U z) :=
    integrable_of_continuous_of_vanishing (L := L)
      (((hfdPhi.clm_apply hcontX).add (continuous_const.mul hPhi.continuous)).mul hq.continuous)
      (fun z (hz : L < ‖z‖) => by simp [parScaleResidual3, hsupp z hz.le, hfdPhi_zero z hz])
  calc (∫ z : STime, Phi z * parEnergyPair U z)
      = ∫ z : STime, (Phi z * fderiv ℝ (parEnergy U) z (parVec z)
          + 2 * (Phi z * parEnergy U z)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = (∫ z : STime, Phi z * fderiv ℝ (parEnergy U) z (parVec z))
          + ∫ z : STime, 2 * (Phi z * parEnergy U z) := integral_add hint1 hint2
    _ = (- ∫ z : STime, parScaleResidual Phi z * parEnergy U z)
          + ∫ z : STime, 2 * (Phi z * parEnergy U z) := by rw [hadj]
    _ = (- ∫ z : STime, (parScaleResidual3 Phi z * parEnergy U z
            + 2 * (Phi z * parEnergy U z)))
          + ∫ z : STime, 2 * (Phi z * parEnergy U z) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hres)]
    _ = - ∫ z : STime, parScaleResidual3 Phi z * parEnergy U z := by
        rw [integral_add hint3 hint2]; ring

/-! ## The cut-off quadratic weight `χ(s)·s^{-3/4}` -/

/-- The cut-off parabolically scale-invariant *quadratic* gauge profile
`χ(s)·s^{-3/4}`: the exponent for which the reduced residual `4sF' + 3F`
vanishes. -/
def parCutProfile3 (chi : ℝ → ℝ) : ℝ → ℝ := fun s => chi s * s ^ (-(3 : ℝ) / 4)

/-- Its derivative. -/
def parCutProfile3' (chi chi' : ℝ → ℝ) : ℝ → ℝ := fun s =>
  chi' s * s ^ (-(3 : ℝ) / 4) + chi s * ((-(3 : ℝ) / 4) * s ^ ((-(3 : ℝ) / 4) - 1))

lemma parCutProfile3_eq_zero {chi : ℝ → ℝ} {s : ℝ} (h : chi s = 0) :
    parCutProfile3 chi s = 0 := by simp [parCutProfile3, h]

lemma parCutProfile3'_eq_zero {chi chi' : ℝ → ℝ} {s : ℝ} (h : chi s = 0) (h' : chi' s = 0) :
    parCutProfile3' chi chi' s = 0 := by simp [parCutProfile3', h, h']

lemma hasDerivAt_parCutProfile3 {chi chi' : ℝ → ℝ} (hchi : ∀ s, HasDerivAt chi (chi' s) s)
    {a1 : ℝ} (ha1 : 0 < a1) (hz : ∀ s, s ≤ a1 → chi s = 0) (hz' : ∀ s, s ≤ a1 → chi' s = 0)
    (s : ℝ) : HasDerivAt (parCutProfile3 chi) (parCutProfile3' chi chi' s) s := by
  rcases eq_or_ne s 0 with rfl | hs
  · have hev : parCutProfile3 chi =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with u hu
      have : |u| < a1 := by simpa [Real.dist_eq] using hu
      exact parCutProfile3_eq_zero (hz u ((le_abs_self u).trans this.le))
    have h0 : parCutProfile3' chi chi' 0 = 0 :=
      parCutProfile3'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
    rw [h0]
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  · exact (hchi s).mul (Real.hasDerivAt_rpow_const (Or.inl hs))

lemma continuous_parCutProfile3' {chi chi' : ℝ → ℝ} (hchi : ∀ s, HasDerivAt chi (chi' s) s)
    (hchi'c : Continuous chi') {a1 : ℝ} (ha1 : 0 < a1) (hz : ∀ s, s ≤ a1 → chi s = 0)
    (hz' : ∀ s, s ≤ a1 → chi' s = 0) : Continuous (parCutProfile3' chi chi') := by
  have hchic : Continuous chi := continuous_iff_continuousAt.2 fun s => (hchi s).continuousAt
  rw [continuous_iff_continuousAt]
  intro s
  rcases eq_or_ne s 0 with rfl | hs
  · have hev : parCutProfile3' chi chi' =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with u hu
      have habs : |u| < a1 := by simpa [Real.dist_eq] using hu
      exact parCutProfile3'_eq_zero (hz u ((le_abs_self u).trans habs.le))
        (hz' u ((le_abs_self u).trans habs.le))
    have h0 : parCutProfile3' chi chi' 0 = 0 :=
      parCutProfile3'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
    rw [ContinuousAt, h0]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  · have hp1 : ContinuousAt (fun u : ℝ => u ^ (-(3 : ℝ) / 4)) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs)
    have hp2 : ContinuousAt (fun u : ℝ => u ^ ((-(3 : ℝ) / 4) - 1)) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs)
    exact (hchi'c.continuousAt.mul hp1).add
      (hchic.continuousAt.mul (continuousAt_const.mul hp2))

/-- **The reduced residual of the cut-off quadratic weight**: `4χ'(s)·s^{1/4}`. -/
theorem parScaleResidual3_parCut3 {chi chi' : ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    4 * s * parCutProfile3' chi chi' s + 3 * parCutProfile3 chi s
      = 4 * chi' s * s ^ ((1 : ℝ) / 4) := by
  have h1 : s * s ^ (-(3 : ℝ) / 4) = s ^ ((1 : ℝ) / 4) := by
    nth_rewrite 1 [show s = s ^ (1 : ℝ) from (Real.rpow_one s).symm]
    rw [← Real.rpow_add hs]
    norm_num
  have h2 : s * s ^ ((-(3 : ℝ) / 4) - 1) = s ^ (-(3 : ℝ) / 4) := by
    nth_rewrite 1 [show s = s ^ (1 : ℝ) from (Real.rpow_one s).symm]
    rw [← Real.rpow_add hs]
    norm_num
  simp only [parCutProfile3, parCutProfile3']
  have hexp : 4 * s * (chi' s * s ^ (-(3 : ℝ) / 4)
      + chi s * ((-(3 : ℝ) / 4) * s ^ ((-(3 : ℝ) / 4) - 1)))
      = 4 * chi' s * (s * s ^ (-(3 : ℝ) / 4))
        - 3 * chi s * (s * s ^ ((-(3 : ℝ) / 4) - 1)) := by ring
  rw [hexp, h1, h2]
  ring

/-- The reduced residual of a gauge weight `Φ = F(s)`: `4sF'(s) + 3F(s)`. -/
theorem parScaleResidual3_parWeightOf {F F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s)
    (z : STime) :
    parScaleResidual3 (parWeightOf F) z
      = 4 * parScale z * F' (parScale z) + 3 * F (parScale z) := by
  have hcomp : HasFDerivAt (parWeightOf F)
      ((F' (parScale z)) • (fderiv ℝ parScale z)) z :=
    (hF (parScale z)).comp_hasFDerivAt z
      (contDiff_parScale.differentiable (by simp) z).hasFDerivAt
  simp only [parScaleResidual3, hcomp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_parScale_parVec, parWeightOf_apply]
  ring

/-- **The cut-off quadratic parabolic probe adjoint identity.**  For every `C¹`
spacetime field `U` and every `C¹` cut-off `χ` supported in `[a₁,b₂] ⊂ (0,∞)` in
the parabolic gauge `s = ‖x‖⁴ + t²`,

  `∫ (χ(s)/s^{3/4})·⟪U, ΛU⟫ = − ∫ 4χ'(s)·s^{1/4}·½|U|²`,

with `Λ` the parabolic scaling generator based at the spacetime origin. -/
theorem quadratic_parabolic_cutoff_probe_adjoint {chi chi' : ℝ → ℝ} {U : STime → E3}
    (hchi : ∀ s, HasDerivAt chi (chi' s) s) (hchi'c : Continuous chi')
    {a1 b2 : ℝ} (ha1 : 0 < a1)
    (hz : ∀ s, s ≤ a1 → chi s = 0) (hz' : ∀ s, s ≤ a1 → chi' s = 0)
    (hzb : ∀ s, b2 ≤ s → chi s = 0)
    (hU : ContDiff ℝ (1 : ℕ) U) :
    (∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergyPair U z)
      = - ∫ z : STime, (4 * chi' (parScale z) * (parScale z) ^ ((1 : ℝ) / 4))
          * parEnergy U z := by
  have hderiv := hasDerivAt_parCutProfile3 hchi ha1 hz hz'
  have hcont' := continuous_parCutProfile3' hchi hchi'c ha1 hz hz'
  have hPhiC : ContDiff ℝ (1 : ℕ) (parWeightOf (parCutProfile3 chi)) :=
    contDiff_parWeightOf hderiv hcont'
  set L : ℝ := max 1 b2 with hLdef
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLb : b2 ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hsupp : ∀ z : STime, L ≤ ‖z‖ → parWeightOf (parCutProfile3 chi) z = 0 := by
    intro z hznorm
    exact parCutProfile3_eq_zero (hzb _ (le_trans hLb (parScale_ge_of_norm_ge hL1 hznorm)))
  have hadj := quadratic_parabolic_probe_adjoint hPhiC hU hL0 hsupp
  rw [hadj]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show parScaleResidual3 (parWeightOf (parCutProfile3 chi)) z * parEnergy U z
      = 4 * chi' (parScale z) * (parScale z) ^ ((1 : ℝ) / 4) * parEnergy U z
  rcases eq_or_ne z 0 with rfl | hzne
  · have hs0 : parScale (0 : STime) = 0 := (parScale_eq_zero_iff _).2 rfl
    have h1 : parScaleResidual3 (parWeightOf (parCutProfile3 chi)) (0 : STime) = 0 := by
      rw [parScaleResidual3_parWeightOf hderiv, hs0,
        parCutProfile3_eq_zero (hz 0 ha1.le),
        parCutProfile3'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)]
      ring
    have h2 : 4 * chi' (parScale (0 : STime)) * (parScale (0 : STime)) ^ ((1 : ℝ) / 4) = 0 := by
      rw [hs0, hz' 0 ha1.le]
      ring
    rw [h1, h2]
  · rw [parScaleResidual3_parWeightOf hderiv,
      parScaleResidual3_parCut3 (chi := chi) (chi' := chi') (parScale_pos_of_ne hzne)]

end ClayNS

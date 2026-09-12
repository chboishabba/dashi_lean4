/-
# The cut-off parabolically scale-invariant weight on spacetime

`ParabolicDilationProbe.lean` proves, for *any* `C¹` spacetime field `U` and any
compactly supported `C¹` weight `Φ`,

  `∫ Φ·⟪x, ΛU⟫ = − ∫ (X·∇Φ + 5Φ)·⟪x, U⟫`,     `X(z) = (2t, x)`.

This file instantiates the weight by the parabolic analogue of `χ(r)/r³`.  The
natural parabolic gauge is

  `s(z) = ‖x‖⁴ + t²`,      `X·∇s = 4s`,        (`ClayNS.fderiv_parScale_parVec`)

so that a weight `Φ = F(s)` has scale residual

  `X·∇Φ + 5Φ = 4 s F'(s) + 5 F(s)`,        (`ClayNS.parScaleResidual_parWeightOf`)

which vanishes identically exactly for `F = c·s^{-5/4}` — the parabolically
scale-invariant weight, which is not `C¹` at the spacetime origin.  Cutting it
off, `F = χ(s)·s^{-5/4}`, the residual is

  `4 s F'(s) + 5F(s) = 4 χ'(s)·s^{-1/4}`,      (`ClayNS.parScaleResidual_parCut`)

supported exactly where the cut-off varies.  Hence, for every `C¹` spacetime
field `U`,

  `∫ (χ(s)/s^{5/4})·⟪x, ΛU⟫ = − ∫ 4χ'(s)·s^{-1/4}·⟪x, U⟫`,
                                          (`parabolic_cutoff_probe_adjoint`)

with `Λ` the genuine parabolic scaling generator `ClayNS.scaleGen` based at the
spacetime origin.  This is the spacetime analogue of
`ClayNS.cutoff_dilation_probe_adjoint`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ParabolicDilationProbe

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The parabolic gauge `s = ‖x‖⁴ + t²` -/

/-- The **parabolic gauge**: the natural degree-`4` homogeneous function of
spacetime for the parabolic scaling `(t,x) ↦ (λ²t, λx)`. -/
def parScale (z : STime) : ℝ := ‖z.2‖ ^ 4 + z.1 ^ 2

lemma parScale_nonneg (z : STime) : 0 ≤ parScale z := by
  have h1 : (0 : ℝ) ≤ ‖z.2‖ ^ 4 := by positivity
  have h2 : (0 : ℝ) ≤ z.1 ^ 2 := by positivity
  simp only [parScale]; linarith

lemma parScale_eq_zero_iff (z : STime) : parScale z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have h1 : (0 : ℝ) ≤ ‖z.2‖ ^ 4 := by positivity
    have h2 : (0 : ℝ) ≤ z.1 ^ 2 := by positivity
    have hx : ‖z.2‖ ^ 4 = 0 := by simp only [parScale] at h; linarith
    have ht : z.1 ^ 2 = 0 := by simp only [parScale] at h; linarith
    have hx0 : z.2 = 0 := by
      have hn : ‖z.2‖ = 0 := by
        exact (pow_eq_zero_iff (n := 4) (by norm_num)).1 hx
      simpa using hn
    have ht0 : z.1 = 0 := by
      exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 ht
    exact Prod.ext ht0 hx0
  · rintro rfl
    simp [parScale]

lemma parScale_pos_of_ne {z : STime} (hz : z ≠ 0) : 0 < parScale z :=
  lt_of_le_of_ne (parScale_nonneg z) (fun h => hz ((parScale_eq_zero_iff z).1 h.symm))

/-- Far away in spacetime the gauge is large. -/
lemma parScale_ge_of_norm_ge {L : ℝ} (hL : 1 ≤ L) {z : STime} (hz : L ≤ ‖z‖) :
    L ≤ parScale z := by
  have hnorm : ‖z‖ = max |z.1| ‖z.2‖ := by
    simp [Prod.norm_def, Real.norm_eq_abs]
  rw [hnorm] at hz
  have h1 : (0 : ℝ) ≤ ‖z.2‖ ^ 4 := by positivity
  have h2 : (0 : ℝ) ≤ z.1 ^ 2 := by positivity
  rcases le_total |z.1| ‖z.2‖ with hc | hc
  · have hx : L ≤ ‖z.2‖ := by
      rwa [max_eq_right hc] at hz
    have hr1 : (1 : ℝ) ≤ ‖z.2‖ := le_trans hL hx
    have hpow : ‖z.2‖ ≤ ‖z.2‖ ^ 4 := by
      calc ‖z.2‖ = ‖z.2‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z.2‖ ^ 4 := pow_le_pow_right₀ hr1 (by norm_num)
    have : L ≤ ‖z.2‖ ^ 4 := le_trans hx hpow
    simp only [parScale]; linarith
  · have ht : L ≤ |z.1| := by
      rwa [max_eq_left hc] at hz
    have hr1 : (1 : ℝ) ≤ |z.1| := le_trans hL ht
    have hsq : |z.1| ^ 2 = z.1 ^ 2 := sq_abs _
    have hpow : |z.1| ≤ |z.1| ^ 2 := by
      calc |z.1| = |z.1| ^ 1 := (pow_one _).symm
        _ ≤ |z.1| ^ 2 := pow_le_pow_right₀ hr1 (by norm_num)
    have : L ≤ z.1 ^ 2 := by rw [← hsq]; linarith
    simp only [parScale]; linarith

lemma contDiff_parScale : ContDiff ℝ (1 : ℕ) parScale := by
  have hfun : parScale = fun z : STime => (‖z.2‖ ^ 2) ^ 2 + z.1 ^ 2 := by
    funext z
    simp only [parScale]
    ring
  rw [hfun]
  exact ((((contDiff_norm_sq ℝ).comp contDiff_snd)).pow 2).add (contDiff_fst.pow 2)

/-- **The parabolic gauge is homogeneous of degree `4`**: `X·∇s = 4s`. -/
theorem fderiv_parScale_parVec (z : STime) :
    fderiv ℝ parScale z (parVec z) = 4 * parScale z := by
  have hfun : parScale = fun w : STime => (‖w.2‖ ^ 2) ^ 2 + w.1 ^ 2 := by
    funext w
    simp only [parScale]
    ring
  have hA : HasFDerivAt (fun w : STime => ‖w.2‖ ^ 2)
      (((2 : ℕ) • (innerSL ℝ z.2)).comp (ContinuousLinearMap.snd ℝ ℝ E3)) z :=
    (hasStrictFDerivAt_norm_sq z.2).hasFDerivAt.comp z
      (ContinuousLinearMap.snd ℝ ℝ E3).hasFDerivAt
  have hT : HasFDerivAt (fun w : STime => w.1) (ContinuousLinearMap.fst ℝ ℝ E3) z :=
    (ContinuousLinearMap.fst ℝ ℝ E3).hasFDerivAt
  have hsum : HasFDerivAt (fun w : STime => (‖w.2‖ ^ 2) ^ 2 + w.1 ^ 2) _ z :=
    (hA.pow 2).add (hT.pow 2)
  rw [hfun, hsum.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_fst', innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul,
    real_inner_self_eq_norm_sq, parVec]
  push_cast
  ring

/-! ## Weights built from the gauge -/

/-- The spacetime weight attached to a gauge profile `F`. -/
def parWeightOf (F : ℝ → ℝ) : STime → ℝ := fun z => F (parScale z)

@[simp] lemma parWeightOf_apply (F : ℝ → ℝ) (z : STime) :
    parWeightOf F z = F (parScale z) := rfl

lemma contDiff_parWeightOf {F F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s)
    (hF'c : Continuous F') : ContDiff ℝ (1 : ℕ) (parWeightOf F) := by
  have hFC : ContDiff ℝ (1 : ℕ) F := by
    have hd : deriv F = F' := funext fun s => (hF s).deriv
    have h1 : ContDiff ℝ 1 F := contDiff_one_iff_deriv.2
      ⟨fun s => (hF s).differentiableAt, by rw [hd]; exact hF'c⟩
    exact_mod_cast h1
  exact hFC.comp contDiff_parScale

/-- **The parabolic scale residual of a gauge weight**: `4 s F'(s) + 5 F(s)`. -/
theorem parScaleResidual_parWeightOf {F F' : ℝ → ℝ} (hF : ∀ s, HasDerivAt F (F' s) s)
    (z : STime) :
    parScaleResidual (parWeightOf F) z
      = 4 * parScale z * F' (parScale z) + 5 * F (parScale z) := by
  have hcomp : HasFDerivAt (parWeightOf F)
      ((F' (parScale z)) • (fderiv ℝ parScale z)) z :=
    (hF (parScale z)).comp_hasFDerivAt z
      (contDiff_parScale.differentiable (by simp) z).hasFDerivAt
  simp only [parScaleResidual, hcomp.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_parScale_parVec, parWeightOf_apply]
  ring

/-! ## The cut-off parabolically scale-invariant profile -/

/-- The cut-off parabolically scale-invariant gauge profile `χ(s)·s^{-5/4}`. -/
def parCutProfile (chi : ℝ → ℝ) : ℝ → ℝ := fun s => chi s * s ^ (-(5 : ℝ) / 4)

/-- Its derivative. -/
def parCutProfile' (chi chi' : ℝ → ℝ) : ℝ → ℝ := fun s =>
  chi' s * s ^ (-(5 : ℝ) / 4) + chi s * ((-(5 : ℝ) / 4) * s ^ ((-(5 : ℝ) / 4) - 1))

lemma parCutProfile_eq_zero {chi : ℝ → ℝ} {s : ℝ} (h : chi s = 0) :
    parCutProfile chi s = 0 := by simp [parCutProfile, h]

lemma parCutProfile'_eq_zero {chi chi' : ℝ → ℝ} {s : ℝ} (h : chi s = 0) (h' : chi' s = 0) :
    parCutProfile' chi chi' s = 0 := by simp [parCutProfile', h, h']

lemma hasDerivAt_parCutProfile_of_ne {chi chi' : ℝ → ℝ}
    (hchi : ∀ s, HasDerivAt chi (chi' s) s) {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (parCutProfile chi) (parCutProfile' chi chi' s) s :=
  (hchi s).mul (Real.hasDerivAt_rpow_const (Or.inl hs))

/-- The cut-off profile is differentiable everywhere: off the origin by the
product rule, at the origin because the cut-off vanishes there identically. -/
lemma hasDerivAt_parCutProfile {chi chi' : ℝ → ℝ} (hchi : ∀ s, HasDerivAt chi (chi' s) s)
    {a1 : ℝ} (ha1 : 0 < a1) (hz : ∀ s, s ≤ a1 → chi s = 0) (hz' : ∀ s, s ≤ a1 → chi' s = 0)
    (s : ℝ) : HasDerivAt (parCutProfile chi) (parCutProfile' chi chi' s) s := by
  rcases eq_or_ne s 0 with rfl | hs
  · have hev : parCutProfile chi =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with u hu
      have : |u| < a1 := by simpa [Real.dist_eq] using hu
      exact parCutProfile_eq_zero (hz u ((le_abs_self u).trans this.le))
    have h0 : parCutProfile' chi chi' 0 = 0 :=
      parCutProfile'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
    rw [h0]
    exact (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev
  · exact hasDerivAt_parCutProfile_of_ne hchi hs

lemma continuous_parCutProfile' {chi chi' : ℝ → ℝ} (hchi : ∀ s, HasDerivAt chi (chi' s) s)
    (hchi'c : Continuous chi') {a1 : ℝ} (ha1 : 0 < a1) (hz : ∀ s, s ≤ a1 → chi s = 0)
    (hz' : ∀ s, s ≤ a1 → chi' s = 0) : Continuous (parCutProfile' chi chi') := by
  have hchic : Continuous chi := continuous_iff_continuousAt.2 fun s => (hchi s).continuousAt
  rw [continuous_iff_continuousAt]
  intro s
  rcases eq_or_ne s 0 with rfl | hs
  · have hev : parCutProfile' chi chi' =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) ha1] with u hu
      have habs : |u| < a1 := by simpa [Real.dist_eq] using hu
      exact parCutProfile'_eq_zero (hz u ((le_abs_self u).trans habs.le))
        (hz' u ((le_abs_self u).trans habs.le))
    have h0 : parCutProfile' chi chi' 0 = 0 :=
      parCutProfile'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)
    rw [ContinuousAt, h0]
    exact Filter.Tendsto.congr' hev.symm tendsto_const_nhds
  · have hp1 : ContinuousAt (fun u : ℝ => u ^ (-(5 : ℝ) / 4)) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs)
    have hp2 : ContinuousAt (fun u : ℝ => u ^ ((-(5 : ℝ) / 4) - 1)) s :=
      Real.continuousAt_rpow_const _ _ (Or.inl hs)
    exact (hchi'c.continuousAt.mul hp1).add
      (hchic.continuousAt.mul (continuousAt_const.mul hp2))

/-- **The residual of the cut-off parabolically scale-invariant weight**:
`4χ'(s)·s^{-1/4}`. -/
theorem parScaleResidual_parCut {chi chi' : ℝ → ℝ} {s : ℝ} (hs : 0 < s) :
    4 * s * parCutProfile' chi chi' s + 5 * parCutProfile chi s
      = 4 * chi' s * s ^ (-(1 : ℝ) / 4) := by
  have hs0 : s ≠ 0 := ne_of_gt hs
  have h1 : s * s ^ (-(5 : ℝ) / 4) = s ^ (-(1 : ℝ) / 4) := by
    nth_rewrite 1 [show s = s ^ (1 : ℝ) from (Real.rpow_one s).symm]
    rw [← Real.rpow_add hs]
    norm_num
  have h2 : s * s ^ ((-(5 : ℝ) / 4) - 1) = s ^ (-(5 : ℝ) / 4) := by
    nth_rewrite 1 [show s = s ^ (1 : ℝ) from (Real.rpow_one s).symm]
    rw [← Real.rpow_add hs]
    norm_num
  simp only [parCutProfile, parCutProfile']
  have hexp : 4 * s * (chi' s * s ^ (-(5 : ℝ) / 4)
      + chi s * ((-(5 : ℝ) / 4) * s ^ ((-(5 : ℝ) / 4) - 1)))
      = 4 * chi' s * (s * s ^ (-(5 : ℝ) / 4))
        - 5 * chi s * (s * s ^ ((-(5 : ℝ) / 4) - 1)) := by ring
  rw [hexp, h1, h2]
  ring

/-! ## The adjoint identity for the cut-off parabolic weight -/

/-- **The cut-off parabolic dilation probe against an arbitrary spacetime
field.**  For every `C¹` field `U` on spacetime and every `C¹` cut-off `χ`
supported in `[a₁,b₂] ⊂ (0,∞)` in the parabolic gauge `s = ‖x‖⁴ + t²`,

  `∫ (χ(s)/s^{5/4})·⟪x, ΛU⟫ dz = − ∫ 4χ'(s)·s^{-1/4}·⟪x, U⟫ dz`,

where `Λ` is the parabolic scaling generator based at the spacetime origin.  No
radiality, no self-similarity and no time-independence of `U` is used. -/
theorem parabolic_cutoff_probe_adjoint {chi chi' : ℝ → ℝ} {U : STime → E3}
    (hchi : ∀ s, HasDerivAt chi (chi' s) s) (hchi'c : Continuous chi')
    {a1 b2 : ℝ} (ha1 : 0 < a1)
    (hz : ∀ s, s ≤ a1 → chi s = 0) (hz' : ∀ s, s ≤ a1 → chi' s = 0)
    (hzb : ∀ s, b2 ≤ s → chi s = 0)
    (hU : ContDiff ℝ (1 : ℕ) U) :
    (∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) (parGen U) z)
      = - ∫ z : STime, (4 * chi' (parScale z) * (parScale z) ^ (-(1 : ℝ) / 4))
          * parRadPair U z := by
  have hderiv := hasDerivAt_parCutProfile hchi ha1 hz hz'
  have hcont' := continuous_parCutProfile' hchi hchi'c ha1 hz hz'
  have hPhiC : ContDiff ℝ (1 : ℕ) (parWeightOf (parCutProfile chi)) :=
    contDiff_parWeightOf hderiv hcont'
  set L : ℝ := max 1 b2 with hLdef
  have hL1 : (1 : ℝ) ≤ L := le_max_left _ _
  have hLb : b2 ≤ L := le_max_right _ _
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL1
  have hsupp : ∀ z : STime, L ≤ ‖z‖ → parWeightOf (parCutProfile chi) z = 0 := by
    intro z hznorm
    exact parCutProfile_eq_zero (hzb _ (le_trans hLb (parScale_ge_of_norm_ge hL1 hznorm)))
  have hadj := parabolic_dilation_probe_adjoint hPhiC hU hL0 hsupp
  rw [hadj]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show parScaleResidual (parWeightOf (parCutProfile chi)) z * parRadPair U z
      = 4 * chi' (parScale z) * (parScale z) ^ (-(1 : ℝ) / 4) * parRadPair U z
  rcases eq_or_ne z 0 with rfl | hzne
  · have hs0 : parScale (0 : STime) = 0 := (parScale_eq_zero_iff _).2 rfl
    have h1 : parScaleResidual (parWeightOf (parCutProfile chi)) (0 : STime) = 0 := by
      rw [parScaleResidual_parWeightOf hderiv, hs0,
        parCutProfile_eq_zero (hz 0 ha1.le),
        parCutProfile'_eq_zero (hz 0 ha1.le) (hz' 0 ha1.le)]
      ring
    have h2 : 4 * chi' (parScale (0 : STime)) * (parScale (0 : STime)) ^ (-(1 : ℝ) / 4) = 0 := by
      rw [hs0, hz' 0 ha1.le]
      ring
    rw [h1, h2]
  · rw [parScaleResidual_parWeightOf hderiv,
      parScaleResidual_parCut (chi := chi) (chi' := chi') (parScale_pos_of_ne hzne)]

end ClayNS

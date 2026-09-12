/-
# Probe coercivity without a normalised weight

`ApproximateScaleAnchor.lean` proves `ClayNS.probe_scale_coercivity`: a probe
weight `w` which is normalised (`∫|w|²/Γ ≤ 1`), nearly blind to the scaling
direction (`|∫⟨w,ΛU⟩| ≤ δ`) and sees the profile (`∫⟨w,U⟩ = a₀`) forces the
quantitative scale cost `(|a₀| − Mc·δ)²·‖ΛU‖²_Γ ≤ Δ_scale`.

The probes actually produced by the cut-off construction of
`ParabolicProbeExistence.lean` are *not* normalised: their weight is
`w(z) = (χ(s)/s^{5/4})·x`, whose Gaussian norm is whatever it is.  This file
removes the normalisation from the hypotheses, at the expected cost of dividing
the conclusion by the norm:

  `∫|w|²/Γ ≤ N`  ⟹  `((|a₀| − Mc·δ)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`.
                                    (`probe_scale_coercivity_unnormalized`)

The proof simply rescales the weight by `N^{-1/2}`, which multiplies `a₀` and
`δ` by the same factor and therefore multiplies the whole bracket by it: the
statement is exactly scaling-covariant, as it must be, since a probe and its
positive multiples carry the same information.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ApproximateScaleAnchor
import RequestProject.NavierStokes.GaussianScaleGram

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

/-- Rescaling a probe weight rescales its pairings. -/
lemma integral_pair_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℝ)
    (w V : α → E3) :
    (∫ x, ∑ a, (c • w x) a * V x a ∂μ) = c * ∫ x, ∑ a, w x a * V x a ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ∑ a, (c • w x) a * V x a = c * ∑ a, w x a * V x a
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show c * w x a * V x a = c * (w x a * V x a)
  ring

/-- Rescaling a probe weight rescales its Gaussian norm quadratically. -/
lemma integral_norm_smul {α : Type*} [MeasurableSpace α] {μ : Measure α} (c : ℝ)
    (Gam : α → ℝ) (w : α → E3) :
    (∫ x, (Gam x)⁻¹ * ∑ a, ((c • w x) a) ^ 2 ∂μ)
      = c ^ 2 * ∫ x, (Gam x)⁻¹ * ∑ a, (w x a) ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Gam x)⁻¹ * ∑ a, ((c • w x) a) ^ 2
      = c ^ 2 * ((Gam x)⁻¹ * ∑ a, (w x a) ^ 2)
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (Gam x)⁻¹ * (c * w x a) ^ 2 = c ^ 2 * ((Gam x)⁻¹ * (w x a) ^ 2)
  ring

/-- The anchor mode of a rescaled weight is the rescaled anchor mode. -/
lemma probeMode_smul {α : Type*} [MeasurableSpace α] (Gam : α → ℝ) (c : ℝ) (w : α → E3)
    (x : α) (a : Fin 3) :
    probeMode Gam (fun y => c • w y) x a = c * probeMode Gam w x a := by
  show (Gam x)⁻¹ * (c * w x a) = c * ((Gam x)⁻¹ * w x a)
  ring

/-- **Probe coercivity for an unnormalised probe.**  A probe weight `w` whose
Gaussian norm is merely *bounded*, `∫|w|²/Γ ≤ N`, still forces a quantitative
scale cost, with the bracket divided by `N`:

  `((|a₀| − Mc·δ)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`.

This is the form in which the cut-off probes of the scale-probe construction —
which come with no normalisation at all — can be fed to the approximate
anchor. -/
theorem probe_scale_coercivity_unnormalized {μ : Measure STime} {Gam : STime → ℝ}
    {z0 : STime} {U w : STime → E3} (hpos : ∀ x, 0 < Gam x)
    (hf : Integrable (fun x => Gam x * ∑ a, (U x a) ^ 2) μ)
    (hg : Integrable (fun x => Gam x * ∑ a, (scaleGen z0 U x a) ^ 2) μ)
    (hfg : Integrable (fun x => Gam x * ∑ a, U x a * scaleGen z0 U x a) μ)
    (he : Integrable (fun x => Gam x * ∑ a, (probeMode Gam w x a) ^ 2) μ)
    (hef : Integrable (fun x => Gam x * ∑ a, probeMode Gam w x a * U x a) μ)
    (heg : Integrable (fun x => Gam x * ∑ a, probeMode Gam w x a * scaleGen z0 U x a) μ)
    {Nb del a0 Mc : ℝ} (hNb : 0 < Nb) (hdel : 0 ≤ del)
    (hnorm : (∫ x, (Gam x)⁻¹ * ∑ a, (w x a) ^ 2 ∂μ) ≤ Nb)
    (hperp : |∫ x, ∑ a, w x a * scaleGen z0 U x a ∂μ| ≤ del)
    (hanchor : (∫ x, ∑ a, w x a * U x a ∂μ) = a0)
    (hcoll : |gramC μ Gam U (scaleGen z0 U)| ≤ Mc * gramA μ Gam (scaleGen z0 U))
    (hbracket : 0 ≤ |a0| - Mc * del) :
    ((|a0| - Mc * del) ^ 2 / Nb) * gramA μ Gam (scaleGen z0 U)
      ≤ scaleGramDefect μ Gam z0 U := by
  classical
  set c : ℝ := (Real.sqrt Nb)⁻¹ with hc
  have hsq : 0 < Real.sqrt Nb := Real.sqrt_pos.2 hNb
  have hc0 : 0 < c := by positivity
  have hcsq : c ^ 2 = 1 / Nb := by
    rw [hc, inv_pow, Real.sq_sqrt hNb.le, one_div]
  set w' : STime → E3 := fun x => c • w x with hw'
  -- integrability of the rescaled mode
  have hmode : ∀ (x : STime) (a : Fin 3), probeMode Gam w' x a = c * probeMode Gam w x a :=
    fun x a => probeMode_smul Gam c w x a
  have he' : Integrable (fun x => Gam x * ∑ a, (probeMode Gam w' x a) ^ 2) μ := by
    have hfun : (fun x => Gam x * ∑ a, (probeMode Gam w' x a) ^ 2)
        = fun x => c ^ 2 * (Gam x * ∑ a, (probeMode Gam w x a) ^ 2) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hmode x a]
      ring
    rw [hfun]
    exact he.const_mul _
  have hef' : Integrable (fun x => Gam x * ∑ a, probeMode Gam w' x a * U x a) μ := by
    have hfun : (fun x => Gam x * ∑ a, probeMode Gam w' x a * U x a)
        = fun x => c * (Gam x * ∑ a, probeMode Gam w x a * U x a) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hmode x a]
      ring
    rw [hfun]
    exact hef.const_mul _
  have heg' : Integrable (fun x => Gam x * ∑ a, probeMode Gam w' x a * scaleGen z0 U x a) μ := by
    have hfun : (fun x => Gam x * ∑ a, probeMode Gam w' x a * scaleGen z0 U x a)
        = fun x => c * (Gam x * ∑ a, probeMode Gam w x a * scaleGen z0 U x a) := by
      funext x
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hmode x a]
      ring
    rw [hfun]
    exact heg.const_mul _
  -- the rescaled probe is normalised
  have hnorm' : (∫ x, (Gam x)⁻¹ * ∑ a, (w' x a) ^ 2 ∂μ) ≤ 1 := by
    rw [hw', integral_norm_smul c Gam w, hcsq]
    rw [div_mul_eq_mul_div, one_mul, div_le_one hNb]
    exact hnorm
  have hperp' : |∫ x, ∑ a, w' x a * scaleGen z0 U x a ∂μ| ≤ c * del := by
    rw [hw', integral_pair_smul c w (scaleGen z0 U), abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left hperp hc0.le
  have hanchor' : (∫ x, ∑ a, w' x a * U x a ∂μ) = c * a0 := by
    rw [hw', integral_pair_smul c w U, hanchor]
  have hbracket' : 0 ≤ |c * a0| - Mc * (c * del) := by
    rw [abs_mul, abs_of_pos hc0]
    nlinarith [hbracket, hc0.le]
  have hmain := probe_scale_coercivity (μ := μ) (Gam := Gam) (z0 := z0) (U := U) (w := w')
    hpos hf hg hfg he' hef' heg' (by positivity) hnorm' hperp' hanchor' hcoll hbracket'
  have hbr : (|c * a0| - Mc * (c * del)) ^ 2 = (1 / Nb) * (|a0| - Mc * del) ^ 2 := by
    rw [abs_mul, abs_of_pos hc0]
    have : (c * |a0| - Mc * (c * del)) = c * (|a0| - Mc * del) := by ring
    rw [this, mul_pow, hcsq]
  rw [hbr] at hmain
  calc ((|a0| - Mc * del) ^ 2 / Nb) * gramA μ Gam (scaleGen z0 U)
      = (1 / Nb) * (|a0| - Mc * del) ^ 2 * gramA μ Gam (scaleGen z0 U) := by ring
    _ ≤ scaleGramDefect μ Gam z0 U := hmain

end ClayNS

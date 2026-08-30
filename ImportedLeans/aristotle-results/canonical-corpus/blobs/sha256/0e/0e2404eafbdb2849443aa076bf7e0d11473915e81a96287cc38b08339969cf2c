/-
# The scale-separating probe for the actual spacetime profile

This file assembles the two halves that have been built separately:

* `ClayNS.exists_small_residual_parabolic_probe` — for an arbitrary `C¹`
  spacetime field `U` with integrable dimensionless parabolic mass, a cut-off
  weight `w(z) = (χ(s)/s^{5/4})·x`, `s = ‖x‖⁴+t²`, whose pairing with the genuine
  parabolic scaling generator is as small as one likes while its pairing with
  `U` retains essentially all of the mass;
* `ClayNS.probe_scale_coercivity_unnormalized` — such a probe, with a merely
  bounded Gaussian norm, forces a quantitative scale-Gram defect.

The result is the **scale-separating probe theorem for the actual profile**:

  `((m/2)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`,        (`actual_scale_separating_probe`)

where `m = ∫ ⟪x,U⟫/s^{5/4}` is the profile's dimensionless parabolic dilation
mass, `N` bounds the Gaussian norm of the admissible probe weights and `Λ` is
the genuine parabolic scaling generator based at the spacetime origin.  Nothing
in the statement assumes that `U` is radial, self-similar or time-independent:
the separation is produced by the *weight*, not by any structure of `U`.

The hypotheses that remain are the weighted integrability side conditions for
the probe family (`hside`), the a priori collinearity bound `Mc` for the pair
`(U, ΛU)`, and the positivity of the mass `m` — the normalised defect that the
blow-up produces.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ParabolicProbeExistence
import RequestProject.NavierStokes.UnnormalizedProbeCoercivity

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The vector probe weight of the cut-off parabolic scale probe:
`w(z) = (χ(s)/s^{5/4})·x`. -/
def parProbeWeight (chi : ℝ → ℝ) : STime → E3 := fun z =>
  (parCutProfile chi (parScale z)) • z.2

lemma parProbeWeight_pair (chi : ℝ → ℝ) (V : STime → E3) (z : STime) :
    (∑ a, parProbeWeight chi z a * V z a)
      = parProbe (parWeightOf (parCutProfile chi)) V z := by
  show (∑ a, (parCutProfile chi (parScale z) * z.2 a) * V z a)
      = parCutProfile chi (parScale z) * ∑ a, z.2 a * V z a
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The scale cost carried by a single cut-off probe.**  If the cut-off probe
`w(z) = (χ(s)/s^{5/4})·x` has Gaussian norm at most `N`, pairs with the
parabolic scaling generator to within `ε`, and captures at least `m − ε` of the
profile's dilation mass, then — provided the margin `(1+Mc)ε ≤ m/2` — the
scale-Gram defect is coercive:

  `((m/2)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`. -/
theorem scale_cost_of_cutoff_probe
    {Gam : STime → ℝ} {U : STime → E3} (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    {chi : ℝ → ℝ}
    (he : Integrable
      (fun z => Gam z * ∑ a, (probeMode Gam (parProbeWeight chi) z a) ^ 2) volume)
    (hef : Integrable
      (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a * U z a) volume)
    (heg : Integrable
      (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a
        * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    {N eps m Mc : ℝ} (hN : 0 < N) (heps0 : 0 ≤ eps) (hmpos : 0 < m)
    (hnorm : (∫ z : STime, (Gam z)⁻¹ * ∑ a, (parProbeWeight chi z a) ^ 2) ≤ N)
    (hsmall : |∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) (parGen U) z| ≤ eps)
    (hcore : m - eps ≤ ∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) U z)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hmargin : (1 + Mc) * eps ≤ m / 2) :
    ((m / 2) ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  classical
  -- the generator used by the probe is the project's parabolic generator
  have hgenpt : ∀ z : STime, parGen U z = scaleGen ((0 : ℝ), (0 : E3)) U z :=
    fun z => parGen_eq_scaleGen
  have hgen : (∫ z : STime, parProbe (parWeightOf (parCutProfile chi))
      (scaleGen ((0 : ℝ), (0 : E3)) U) z)
      = ∫ z : STime, parProbe (parWeightOf (parCutProfile chi)) (parGen U) z := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [parProbe]
    rw [← hgenpt z]
  have hperp : |∫ z : STime, ∑ a, parProbeWeight chi z a
      * scaleGen ((0 : ℝ), (0 : E3)) U z a| ≤ eps := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
      parProbeWeight_pair chi (scaleGen ((0 : ℝ), (0 : E3)) U) z), hgen]
    exact hsmall
  set a0 : ℝ := ∫ z : STime, ∑ a, parProbeWeight chi z a * U z a with ha0def
  have ha0 : m - eps ≤ a0 := by
    rw [ha0def, integral_congr_ae (Filter.Eventually.of_forall fun z =>
      parProbeWeight_pair chi U z)]
    exact hcore
  have hbr : m / 2 ≤ |a0| - Mc * eps := by
    have habs : a0 ≤ |a0| := le_abs_self a0
    nlinarith [ha0, habs, hmargin]
  have hbracket : 0 ≤ |a0| - Mc * eps := le_trans (by positivity) hbr
  have hmain := probe_scale_coercivity_unnormalized (μ := volume) (Gam := Gam)
    (z0 := ((0 : ℝ), (0 : E3))) (U := U) (w := parProbeWeight chi)
    hpos hf hg hfg he hef heg hN heps0 hnorm hperp rfl hcoll hbracket
  have hAnn : 0 ≤ gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U) :=
    gramA_nonneg (fun z => (hpos z).le) _
  have hsq : (m / 2) ^ 2 ≤ (|a0| - Mc * eps) ^ 2 := by
    have h0 : (0 : ℝ) ≤ m / 2 := by positivity
    nlinarith [hbr, h0]
  have hdiv : (m / 2) ^ 2 / N ≤ (|a0| - Mc * eps) ^ 2 / N :=
    div_le_div_of_nonneg_right hsq hN.le
  calc ((m / 2) ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ ((|a0| - Mc * eps) ^ 2 / N)
          * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U) :=
        mul_le_mul_of_nonneg_right hdiv hAnn
    _ ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := hmain

/-- **The scale-separating probe theorem for the actual spacetime profile.**

Let `U` be a `C¹` spacetime field whose dimensionless parabolic mass density
`m(z) = ⟪x,U z⟫/s(z)^{5/4}` is integrable with total mass `m > 0`, let `Γ > 0`
be a weight, let `Mc` bound the collinearity coefficient of the pair `(U, ΛU)`,
and suppose every admissible cut-off probe weight has Gaussian norm at most `N`
(together with the weighted integrability side conditions).  Then

  `((m/2)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`,

where `Λ` is the genuine parabolic scaling generator based at the spacetime
origin.  No radiality, self-similarity or time-independence of `U` is used. -/
theorem actual_scale_separating_probe
    {Gam : STime → ℝ} {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U)
    (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    (hint : Integrable (parMass U))
    {m : ℝ} (hm : (∫ z : STime, parMass U z) = m) (hmpos : 0 < m)
    {Mc N : ℝ} (hMc : 0 ≤ Mc) (hN : 0 < N)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hside : ∀ chi : ℝ → ℝ, (∀ s, 0 ≤ chi s) → (∀ s, chi s ≤ 1) →
      Integrable
        (fun z => Gam z * ∑ a, (probeMode Gam (parProbeWeight chi) z a) ^ 2) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a * U z a) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a
          * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume ∧
      (∫ z : STime, (Gam z)⁻¹ * ∑ a, (parProbeWeight chi z a) ^ 2) ≤ N) :
    ((m / 2) ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  classical
  set eps : ℝ := m / (2 * (1 + Mc)) with heps_def
  have heps : 0 < eps := by
    have : 0 < 2 * (1 + Mc) := by linarith
    positivity
  have hmargin : (1 + Mc) * eps ≤ m / 2 := by
    rw [heps_def]
    field_simp
    exact le_refl 1
  obtain ⟨chi, chi', a1, b2, ha1, ha1b2, hchi, hchiz, hchinn, hchi1, hsmall, hcore⟩ :=
    exists_small_residual_parabolic_probe hU hint heps
  obtain ⟨he, hef, heg, hnorm⟩ := hside chi hchinn hchi1
  rw [hm] at hcore
  exact scale_cost_of_cutoff_probe hpos hf hg hfg he hef heg hN heps.le hmpos
    hnorm hsmall hcore hcoll hmargin

/-- **The scale-separating probe theorem, with the normalisation left implicit.**
Same as `ClayNS.actual_scale_separating_probe`, but without assuming a uniform
bound on the Gaussian norm of the probe family: the norm of the probe that is
actually produced is finite (it is the weighted mass of an integrable mode), so
some positive `N` always works.  The conclusion is then the qualitative
dichotomy: a positive dilation mass forces a positive scale-Gram defect unless
the weighted mass of `ΛU` vanishes. -/
theorem actual_scale_separating_probe_exists
    {Gam : STime → ℝ} {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U)
    (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    (hint : Integrable (parMass U))
    {m : ℝ} (hm : (∫ z : STime, parMass U z) = m) (hmpos : 0 < m)
    {Mc : ℝ} (hMc : 0 ≤ Mc)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hside : ∀ chi : ℝ → ℝ, (∀ s, 0 ≤ chi s) → (∀ s, chi s ≤ 1) →
      Integrable
        (fun z => Gam z * ∑ a, (probeMode Gam (parProbeWeight chi) z a) ^ 2) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a * U z a) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (parProbeWeight chi) z a
          * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume) :
    ∃ N : ℝ, 0 < N ∧
      ((m / 2) ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
        ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  classical
  set eps : ℝ := m / (2 * (1 + Mc)) with heps_def
  have heps : 0 < eps := by
    have : 0 < 2 * (1 + Mc) := by linarith
    positivity
  have hmargin : (1 + Mc) * eps ≤ m / 2 := by
    rw [heps_def]
    field_simp
    exact le_refl 1
  obtain ⟨chi, chi', a1, b2, ha1, ha1b2, hchi, hchiz, hchinn, hchi1, hsmall, hcore⟩ :=
    exists_small_residual_parabolic_probe hU hint heps
  obtain ⟨he, hef, heg⟩ := hside chi hchinn hchi1
  rw [hm] at hcore
  refine ⟨max 1 (∫ z : STime, (Gam z)⁻¹ * ∑ a, (parProbeWeight chi z a) ^ 2),
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  exact scale_cost_of_cutoff_probe hpos hf hg hfg he hef heg
    (lt_of_lt_of_le one_pos (le_max_left _ _)) heps.le hmpos (le_max_right _ _)
    hsmall hcore hcoll hmargin

end ClayNS

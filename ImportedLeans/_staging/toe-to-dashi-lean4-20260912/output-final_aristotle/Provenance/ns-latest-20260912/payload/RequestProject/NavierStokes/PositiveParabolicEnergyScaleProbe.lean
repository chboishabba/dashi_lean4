/-
# The scale-separating probe with a positive, normalisation-derived anchor

`ActualScaleSeparatingProbe.lean` assembles the *linear* parabolic probe into
scale-Gram coercivity,

  `((m/2)²/N)·‖ΛU‖²_Γ ≤ Δ_scale`,

but its anchor is the **signed** dilation mass `m = ∫ ⟪x,U⟫/s^{5/4}`, and the
theorem has to *assume* `m > 0`.  That hypothesis does not follow from the
profile being nonzero: the integrand changes sign.

This file replaces it.  Using the quadratic probe of
`QuadraticParabolicProbe.lean` / `PositiveParabolicEnergyProbe.lean`, the vector
probe weight is

  `w(z) = Φ(z)·U(z)`,   `Φ(z) = χ(s)/s^{3/4}`,   `s = ‖x‖⁴ + t²`,

whose anchor pairing is `⟪w, U⟫ = Φ·|U|²` — an integral of a **nonnegative**
density — and whose scale pairing is `⟪w, ΛU⟫ = Φ·⟪U, ΛU⟫`, controlled by the
exact adjoint identity.  So:

* `ClayNS.scale_cost_of_quadratic_probe` — the coercivity produced by one
  cut-off quadratic probe;
* `ClayNS.positive_parabolic_energy_scale_probe` — the scale-separating probe
  theorem with anchor `mE = ∫ ½|U|²/s^{3/4}`:

    `(mE²/N)·‖ΛU‖²_Γ ≤ Δ_scale`;

* `ClayNS.positive_parabolic_energy_scale_probe_of_nonzero` — **the point of the
  construction**: the positivity hypothesis is discharged from the profile
  being nonzero at a single spacetime point away from the origin.  No signed
  mass, no cancellation hypothesis, no radiality, no self-similarity, no
  time-independence.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.PositiveParabolicEnergyProbe
import RequestProject.NavierStokes.UnnormalizedProbeCoercivity

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ClayNS

/-- The vector probe weight of the cut-off **quadratic** parabolic scale probe:
`w(z) = (χ(s)/s^{3/4})·U(z)`.  Its anchor pairing against `U` is the
nonnegative density `Φ·|U|²`. -/
def energyProbeWeight (chi : ℝ → ℝ) (U : STime → E3) : STime → E3 := fun z =>
  (parWeightOf (parCutProfile3 chi) z) • U z

lemma energyProbeWeight_pair (chi : ℝ → ℝ) (U V : STime → E3) (z : STime) :
    (∑ a, energyProbeWeight chi U z a * V z a)
      = parWeightOf (parCutProfile3 chi) z * ∑ a, U z a * V z a := by
  show (∑ a, (parWeightOf (parCutProfile3 chi) z * U z a) * V z a)
      = parWeightOf (parCutProfile3 chi) z * ∑ a, U z a * V z a
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

lemma energyProbeWeight_pair_self (chi : ℝ → ℝ) (U : STime → E3) (z : STime) :
    (∑ a, energyProbeWeight chi U z a * U z a)
      = 2 * (parWeightOf (parCutProfile3 chi) z * parEnergy U z) := by
  rw [energyProbeWeight_pair chi U U z]
  simp only [parEnergy]
  have : (∑ a, U z a * U z a) = ∑ a, (U z a) ^ 2 :=
    Finset.sum_congr rfl fun a _ => by ring
  rw [this]
  ring

lemma energyProbeWeight_pair_gen (chi : ℝ → ℝ) (U : STime → E3) (z : STime) :
    (∑ a, energyProbeWeight chi U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a)
      = parWeightOf (parCutProfile3 chi) z * parEnergyPair U z := by
  rw [energyProbeWeight_pair chi U (scaleGen ((0 : ℝ), (0 : E3)) U) z]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← parGen_eq_scaleGen (U := U) (z := z)]

/-- **The scale cost carried by a single cut-off quadratic probe.**  If the
probe `w = Φ·U`, `Φ = χ(s)/s^{3/4}`, has Gaussian norm at most `N`, pairs with
the parabolic scaling generator to within `ε`, and captures at least `mE − ε` of
the profile's parabolic energy, then — provided the margin `(2+Mc)ε ≤ mE` — the
scale-Gram defect is coercive:

  `(mE²/N)·‖ΛU‖²_Γ ≤ Δ_scale`. -/
theorem scale_cost_of_quadratic_probe
    {Gam : STime → ℝ} {U : STime → E3} (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    {chi : ℝ → ℝ}
    (he : Integrable
      (fun z => Gam z * ∑ a, (probeMode Gam (energyProbeWeight chi U) z a) ^ 2) volume)
    (hef : Integrable
      (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a * U z a) volume)
    (heg : Integrable
      (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a
        * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    {N eps mE Mc : ℝ} (hN : 0 < N) (heps0 : 0 ≤ eps) (hMc : 0 ≤ Mc)
    (hnorm : (∫ z : STime, (Gam z)⁻¹ * ∑ a, (energyProbeWeight chi U z a) ^ 2) ≤ N)
    (hsmall : |∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergyPair U z| ≤ eps)
    (hcore : mE - eps ≤ ∫ z : STime, parWeightOf (parCutProfile3 chi) z * parEnergy U z)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hmargin : (2 + Mc) * eps ≤ mE) :
    (mE ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  classical
  have hperp : |∫ z : STime, ∑ a, energyProbeWeight chi U z a
      * scaleGen ((0 : ℝ), (0 : E3)) U z a| ≤ eps := by
    rw [integral_congr_ae (Filter.Eventually.of_forall fun z =>
      energyProbeWeight_pair_gen chi U z)]
    exact hsmall
  set a0 : ℝ := ∫ z : STime, ∑ a, energyProbeWeight chi U z a * U z a with ha0def
  have ha0 : 2 * (mE - eps) ≤ a0 := by
    rw [ha0def, integral_congr_ae (Filter.Eventually.of_forall fun z =>
      energyProbeWeight_pair_self chi U z), integral_const_mul]
    linarith [hcore]
  have hbr : mE ≤ |a0| - Mc * eps := by
    have habs : a0 ≤ |a0| := le_abs_self a0
    nlinarith [ha0, habs, hmargin]
  have hmEnn : 0 ≤ mE := by nlinarith [hmargin, heps0, hMc]
  have hbracket : 0 ≤ |a0| - Mc * eps := le_trans hmEnn hbr
  have hmain := probe_scale_coercivity_unnormalized (μ := volume) (Gam := Gam)
    (z0 := ((0 : ℝ), (0 : E3))) (U := U) (w := energyProbeWeight chi U)
    hpos hf hg hfg he hef heg hN heps0 hnorm hperp rfl hcoll hbracket
  have hAnn : 0 ≤ gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U) :=
    gramA_nonneg (fun z => (hpos z).le) _
  have hsq : mE ^ 2 ≤ (|a0| - Mc * eps) ^ 2 := by nlinarith [hbr, hmEnn]
  have hdiv : mE ^ 2 / N ≤ (|a0| - Mc * eps) ^ 2 / N :=
    div_le_div_of_nonneg_right hsq hN.le
  calc (mE ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ ((|a0| - Mc * eps) ^ 2 / N)
          * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U) :=
        mul_le_mul_of_nonneg_right hdiv hAnn
    _ ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := hmain

/-- **The scale-separating probe theorem with a positive anchor.**

Let `U` be a `C¹` spacetime field whose dimensionless parabolic energy density
`½|U|²/(‖x‖⁴+t²)^{3/4}` is integrable with total mass `mE > 0`, let `Γ > 0` be a
weight, let `Mc` bound the collinearity coefficient of the pair `(U, ΛU)`, and
suppose every admissible cut-off quadratic probe weight has Gaussian norm at
most `N` (with the weighted integrability side conditions).  Then

  `(mE²/N)·‖ΛU‖²_Γ ≤ Δ_scale`,

with `Λ` the genuine parabolic scaling generator at the spacetime origin.  No
radiality, self-similarity or time-independence of `U` is used, and — in
contrast with the linear probe — the anchor `mE` is the integral of a
nonnegative density. -/
theorem positive_parabolic_energy_scale_probe
    {Gam : STime → ℝ} {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U)
    (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    (hint : Integrable (parEnergyMass U))
    {mE : ℝ} (hm : (∫ z : STime, parEnergyMass U z) = mE) (hmpos : 0 < mE)
    {Mc N : ℝ} (hMc : 0 ≤ Mc) (hN : 0 < N)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hside : ∀ chi : ℝ → ℝ, (∀ s, 0 ≤ chi s) → (∀ s, chi s ≤ 1) →
      Integrable
        (fun z => Gam z * ∑ a, (probeMode Gam (energyProbeWeight chi U) z a) ^ 2) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a * U z a) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a
          * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume ∧
      (∫ z : STime, (Gam z)⁻¹ * ∑ a, (energyProbeWeight chi U z a) ^ 2) ≤ N) :
    (mE ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
      ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  classical
  set eps : ℝ := mE / (2 + Mc) with heps_def
  have h2Mc : 0 < 2 + Mc := by linarith
  have heps : 0 < eps := by rw [heps_def]; positivity
  have hmargin : (2 + Mc) * eps ≤ mE := by
    rw [heps_def, mul_div_cancel₀ _ (ne_of_gt h2Mc)]
  obtain ⟨chi, chi', a1, b2, ha1, ha1b2, hchi, hchiz, hchinn, hchi1, hsmall, hcore⟩ :=
    exists_small_residual_quadratic_parabolic_probe hU hint heps
  obtain ⟨he, hef, heg, hnorm⟩ := hside chi hchinn hchi1
  rw [hm] at hcore
  exact scale_cost_of_quadratic_probe hpos hf hg hfg he hef heg hN heps.le hMc
    hnorm hsmall hcore hcoll hmargin

/-- **The positivity hypothesis discharged.**  The anchor of the quadratic probe
is positive as soon as the profile is nonzero somewhere away from the spacetime
origin; there is no signed-mass hypothesis left.  This is the exact fix for the
`m > 0` assumption of `ClayNS.actual_scale_separating_probe`. -/
theorem positive_parabolic_energy_scale_probe_of_nonzero
    {Gam : STime → ℝ} {U : STime → E3} (hU : ContDiff ℝ (1 : ℕ) U)
    (hpos : ∀ z, 0 < Gam z)
    (hf : Integrable (fun z => Gam z * ∑ a, (U z a) ^ 2) volume)
    (hg : Integrable
      (fun z => Gam z * ∑ a, (scaleGen ((0 : ℝ), (0 : E3)) U z a) ^ 2) volume)
    (hfg : Integrable
      (fun z => Gam z * ∑ a, U z a * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume)
    (hint : Integrable (parEnergyMass U))
    {z0 : STime} (hz0 : z0 ≠ 0) (hUz0 : U z0 ≠ 0)
    {Mc N : ℝ} (hMc : 0 ≤ Mc) (hN : 0 < N)
    (hcoll : |gramC volume Gam U (scaleGen ((0 : ℝ), (0 : E3)) U)|
      ≤ Mc * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U))
    (hside : ∀ chi : ℝ → ℝ, (∀ s, 0 ≤ chi s) → (∀ s, chi s ≤ 1) →
      Integrable
        (fun z => Gam z * ∑ a, (probeMode Gam (energyProbeWeight chi U) z a) ^ 2) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a * U z a) volume ∧
      Integrable
        (fun z => Gam z * ∑ a, probeMode Gam (energyProbeWeight chi U) z a
          * scaleGen ((0 : ℝ), (0 : E3)) U z a) volume ∧
      (∫ z : STime, (Gam z)⁻¹ * ∑ a, (energyProbeWeight chi U z a) ^ 2) ≤ N) :
    ∃ mE : ℝ, 0 < mE ∧ (∫ z : STime, parEnergyMass U z) = mE ∧
      (mE ^ 2 / N) * gramA volume Gam (scaleGen ((0 : ℝ), (0 : E3)) U)
        ≤ scaleGramDefect volume Gam ((0 : ℝ), (0 : E3)) U := by
  refine ⟨∫ z : STime, parEnergyMass U z,
    parEnergyMass_integral_pos hU.continuous hint hz0 hUz0, rfl, ?_⟩
  exact positive_parabolic_energy_scale_probe hU hpos hf hg hfg hint rfl
    (parEnergyMass_integral_pos hU.continuous hint hz0 hUz0) hMc hN hcoll hside

end ClayNS

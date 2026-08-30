/-
# Optimizing the near/far cutoff: `η_near(Δ) + η_far(Δ) < 1`

`GaussianNearFarSplit.lean` supplies the literal cutoff decomposition of the
physical interaction `N = (V·∇)V + ∇P` in Gaussian similarity variables,
together with

* **(A-far), proved**: the far pairing is at most `e^{−R²/(8ν)}·M`, `M` the
  fixed second-Gaussian moment `∫ρ_{2ν}‖N‖‖W_⊥‖`, and
* **(A-near)** reduced to a *pointwise* domination on the near field.

This file does two things.

1. It replaces the pointwise near hypothesis by the weaker and far more usable
   **weighted `L²` relative hypothesis**: if the near field is `η`-small in
   `L²(ρ_ν)` relative to the transverse velocity, the near pairing is a
   relative contraction, `|⟪N_near,W_⊥⟫_ρ| ≤ η‖W_⊥‖²_ρ`.  Only Young's
   inequality is used, so no Cauchy–Schwarz machinery in `L²(ρ)` is needed.

2. It performs the **cutoff optimization** that the near/far doctrine calls
   for.  Once the far moment is itself *relative* — `M ≤ C_far‖W_⊥‖²_ρ`, which
   is what a scale-invariant blow-up normalization provides — the far
   contribution at cutoff `R` is `e^{−R²/(8ν)}C_far`, which the Gaussian tail
   drives below any threshold.  Hence a near constant `η_near(R) ≤ η_∞ < 1`,
   *uniform in the cutoff*, already yields a genuinely strict relative
   contraction of the whole interaction at a judiciously chosen cutoff:

     `η_near(R) + η_far(R) < 1`.

   That is `ClayNS.gauss_nearfar_strict_relative_contraction`, whose conclusion
   is exactly the input (A-near)+(A-far) of
   `ClayNS.gaussian_similarity_interaction_closure`.

## Results

* `ClayNS.gauss_pairing_young` — the weighted Young inequality for the Gaussian
  pairing;
* `ClayNS.gauss_near_pairing_relative_L2` — (A-near) from an `L²(ρ)` relative
  bound instead of a pointwise one;
* `ClayNS.exists_cutoff_far_small` — the Gaussian tail beats any relative far
  constant;
* `ClayNS.gauss_nearfar_strict_relative_contraction` — the optimization
  `η_near(R) + η_far(R) < 1` and the resulting strict relative contraction of
  the full interaction.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianNearFarSplit

open MeasureTheory Set Filter
open RealInnerProductSpace

noncomputable section

namespace ClayNS

/-! ## Young's inequality for the Gaussian pairing -/

/-- **The weighted Young inequality.**  For every `ε > 0`,

  `|∫ρ⟪N,W⟫| ≤ (1/2ε)∫ρ‖N‖² + (ε/2)∫ρ‖W‖²`. -/
theorem gauss_pairing_young {nu eps : ℝ} (heps : 0 < eps) (N W : E3 → E3)
    (hN : Integrable (fun y : E3 => gaussWeight nu y * ‖N y‖ ^ 2))
    (hW : Integrable (fun y : E3 => gaussWeight nu y * ‖W y‖ ^ 2)) :
    |∫ y : E3, gaussWeight nu y * ⟪N y, W y⟫|
      ≤ (1 / (2 * eps)) * (∫ y : E3, gaussWeight nu y * ‖N y‖ ^ 2)
        + (eps / 2) * ∫ y : E3, gaussWeight nu y * ‖W y‖ ^ 2 := by
  have hg : Integrable (fun y : E3 => (1 / (2 * eps)) * (gaussWeight nu y * ‖N y‖ ^ 2)
      + (eps / 2) * (gaussWeight nu y * ‖W y‖ ^ 2)) :=
    (hN.const_mul _).add (hW.const_mul _)
  have hbound : ∀ y : E3, ‖gaussWeight nu y * ⟪N y, W y⟫‖
      ≤ (1 / (2 * eps)) * (gaussWeight nu y * ‖N y‖ ^ 2)
        + (eps / 2) * (gaussWeight nu y * ‖W y‖ ^ 2) := by
    intro y
    have hwpos := (gaussWeight_pos nu y).le
    have hcs : |(⟪N y, W y⟫ : ℝ)| ≤ ‖N y‖ * ‖W y‖ := abs_real_inner_le_norm _ _
    have hyoung : ‖N y‖ * ‖W y‖
        ≤ (1 / (2 * eps)) * ‖N y‖ ^ 2 + (eps / 2) * ‖W y‖ ^ 2 := by
      have hsq : 0 ≤ (‖N y‖ - eps * ‖W y‖) ^ 2 := sq_nonneg _
      have hepos : 0 < 2 * eps := by linarith
      rw [← sub_nonneg]
      have hkey : (1 / (2 * eps)) * ‖N y‖ ^ 2 + (eps / 2) * ‖W y‖ ^ 2 - ‖N y‖ * ‖W y‖
          = (1 / (2 * eps)) * (‖N y‖ - eps * ‖W y‖) ^ 2 := by
        field_simp
        ring
      rw [hkey]
      positivity
    calc ‖gaussWeight nu y * ⟪N y, W y⟫‖
        = gaussWeight nu y * |(⟪N y, W y⟫ : ℝ)| := by
          simp [Real.norm_eq_abs, abs_of_nonneg hwpos]
      _ ≤ gaussWeight nu y * ((1 / (2 * eps)) * ‖N y‖ ^ 2 + (eps / 2) * ‖W y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hcs.trans hyoung) hwpos
      _ = (1 / (2 * eps)) * (gaussWeight nu y * ‖N y‖ ^ 2)
            + (eps / 2) * (gaussWeight nu y * ‖W y‖ ^ 2) := by ring
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall hbound)
  rw [integral_add (hN.const_mul _) (hW.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  simpa [Real.norm_eq_abs] using hle

/-- **(A-near) from an `L²(ρ)` relative bound.**  If the near field is
`η`-small relative to the transverse velocity in the Gaussian `L²`,

  `∫ρ‖N_near‖² ≤ η²∫ρ‖W_⊥‖²`,

then the near pairing is a relative contraction of the transverse expenditure.
This is strictly weaker than the pointwise domination of
`ClayNS.gauss_near_pairing_relative`. -/
theorem gauss_near_pairing_relative_L2 {nu R eta : ℝ} (heta : 0 < eta)
    (N Wp : E3 → E3)
    (hnearL2 : (∫ y : E3, gaussWeight nu y * ‖gaussNear R N y‖ ^ 2)
      ≤ eta ^ 2 * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hN : Integrable (fun y : E3 => gaussWeight nu y * ‖gaussNear R N y‖ ^ 2))
    (hW : Integrable (fun y : E3 => gaussWeight nu y * ‖Wp y‖ ^ 2)) :
    |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
      ≤ eta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  have hyoung := gauss_pairing_young (nu := nu) heta (gaussNear R N) Wp hN hW
  have hstep : (1 / (2 * eta)) * (∫ y : E3, gaussWeight nu y * ‖gaussNear R N y‖ ^ 2)
      ≤ (1 / (2 * eta)) * (eta ^ 2 * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hnearL2 (by positivity)
  have hcalc : (1 / (2 * eta)) * (eta ^ 2 * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
      = (eta / 2) * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
    field_simp
  linarith [hyoung, hstep, hcalc.le, hcalc.ge]

/-! ## The Gaussian tail beats any relative far constant -/

/-- **The cutoff can always be pushed past the far tail.**  For every relative
far constant `C ≥ 0` and every threshold `δ > 0` there is a cutoff `R ≥ 0` with
`e^{−R²/(8ν)}·C < δ`. -/
theorem exists_cutoff_far_small {nu C delta : ℝ} (hnu : 0 < nu)
    (hdelta : 0 < delta) :
    ∃ R : ℝ, 0 ≤ R ∧ Real.exp (-(R ^ 2) / (8 * nu)) * C < delta := by
  have hlim : Tendsto (fun R : ℝ => Real.exp (-(R ^ 2) / (8 * nu)) * C) atTop (nhds (0 * C)) := by
    refine Tendsto.mul_const C ?_
    refine Real.tendsto_exp_atBot.comp ?_
    have hsq : Tendsto (fun R : ℝ => R ^ 2) atTop atTop :=
      tendsto_pow_atTop (n := 2) (by norm_num)
    have hdiv : Tendsto (fun R : ℝ => R ^ 2 / (8 * nu)) atTop atTop :=
      hsq.atTop_div_const (by linarith)
    have hneg : Tendsto (fun R : ℝ => -(R ^ 2 / (8 * nu))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp hdiv
    refine hneg.congr fun R => ?_
    ring
  rw [zero_mul] at hlim
  have hev : ∀ᶠ R : ℝ in atTop, Real.exp (-(R ^ 2) / (8 * nu)) * C < delta := by
    have := hlim.eventually (eventually_lt_nhds hdelta)
    exact this
  obtain ⟨R, hR⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
  exact ⟨R, hR.2, hR.1⟩

/-! ## The optimization `η_near(Δ) + η_far(Δ) < 1` -/

/-- **The near/far cutoff optimization.**  Assume

* the near pairing obeys a relative bound at *every* cutoff with a constant
  `η_near(R) ≤ η_∞ < 1` (uniformity in the cutoff, not smallness of the
  cutoff), and
* the far moment is itself relative, `∫ρ_{2ν}‖N‖‖W_⊥‖ ≤ C_far·‖W_⊥‖²_ρ`.

Then there is a cutoff `R` and a constant `θ < 1` with

  `|⟪N,W_⊥⟫_ρ| ≤ θ‖W_⊥‖²_ρ`,

i.e. the *whole* interaction is a strict relative contraction of the transverse
expenditure.  The Gaussian tail pays the far channel, and the cutoff is chosen
so that `η_near(R) + η_far(R) < 1`. -/
theorem gauss_nearfar_strict_relative_contraction {nu etaInf Cfar : ℝ} (hnu : 0 < nu)
    (hetaInf : etaInf < 1) (N Wp : E3 → E3)
    (hnear : ∀ R : ℝ, 0 ≤ R →
      |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
        ≤ etaInf * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hfarRel : (∫ y : E3, gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖))
      ≤ Cfar * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2)
    (hintM : Integrable (fun y : E3 => gaussWeight (2 * nu) y * (‖N y‖ * ‖Wp y‖)))
    (hnearInt : ∀ R : ℝ,
      Integrable (fun y : E3 => gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫))
    (hfarInt : ∀ R : ℝ,
      Integrable (fun y : E3 => gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫)) :
    ∃ theta : ℝ, theta < 1 ∧
      |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
        ≤ theta * ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 := by
  obtain ⟨R, hR0, hRsmall⟩ :=
    exists_cutoff_far_small (nu := nu) (C := Cfar) hnu (by linarith : (0 : ℝ) < 1 - etaInf)
  set X : ℝ := ∫ y : E3, gaussWeight nu y * ‖Wp y‖ ^ 2 with hX
  set tail : ℝ := Real.exp (-(R ^ 2) / (8 * nu)) with htail
  have htailpos : 0 < tail := Real.exp_pos _
  refine ⟨etaInf + tail * Cfar, by linarith, ?_⟩
  -- split the interaction at the chosen cutoff
  have hsplit : (∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫)
      = (∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫)
        + ∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫ := by
    rw [← integral_add (hnearInt R) (hfarInt R)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have hy : (⟪N y, Wp y⟫ : ℝ)
        = ⟪gaussNear R N y, Wp y⟫ + ⟪gaussFar R N y, Wp y⟫ := by
      rw [← inner_add_left, gaussNear_add_gaussFar]
    dsimp only
    rw [hy]
    ring
  have hnearR := hnear R hR0
  have hfar := gauss_far_pairing_tail_bound hnu hR0 N Wp hintM
  have hfarX : |∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫| ≤ tail * (Cfar * X) := by
    refine hfar.trans ?_
    exact mul_le_mul_of_nonneg_left hfarRel htailpos.le
  calc |∫ y : E3, gaussWeight nu y * ⟪N y, Wp y⟫|
      = |(∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫)
          + ∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫| := by rw [hsplit]
    _ ≤ |∫ y : E3, gaussWeight nu y * ⟪gaussNear R N y, Wp y⟫|
          + |∫ y : E3, gaussWeight nu y * ⟪gaussFar R N y, Wp y⟫| := abs_add_le _ _
    _ ≤ etaInf * X + tail * (Cfar * X) := by linarith
    _ = (etaInf + tail * Cfar) * X := by ring

end ClayNS

/-
# The space-time form of the weight-aware Caccioppoli budget

`GaussianWeightedAbsorption.lean` proves, for each fixed time, the cell budget
whose sources all carry a positive power of the concentration scale.  The De
Giorgi machinery of `DeGiorgiRecurrence.lean` / `ParabolicGain.lean` consumes a
*space-time* budget: a single constant bounding both the weighted mass at the
end of the window and the total dissipation over it.

This file performs that integration.  The first term of the cell budget is
exactly the time derivative of the weighted mass
(`ClayNS.hasDerivAt_cellInt`), so the fundamental theorem of calculus turns the
family of instantaneous inequalities into

```
  M(t₁) − M(t₀) + ∫_{t₀}^{t₁} [(1−η)ν·J₂ + (ν/2)·J₁]
      ≤ ∫_{t₀}^{t₁} C₁·K₂ + (t₁−t₀)·[ (…)·(π³a)^{3/2}/λ
                                      + (9AB²/2θ)·C_FI√a/λ
                                      + ‖β‖_∞(6π³A·a + νC√a) ],
```

with `M` the weighted mass, `J₂`, `J₁` the two good (coercive) terms and `K₂`
the level-measure term.  Every source is either the coercivity-paired `K₂` or a
quantity that vanishes as the weight concentrates, uniformly over the window.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianWeightedAbsorption

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The four time-dependent quantities -/

/-- The weighted mass `M(t) = ∫_cell Φ_a·β(q)`. -/
def gwMass (a : ℝ) (x0 h : E3) (V : STime → E3) (beta : ℝ → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => torusGauss a x0 (t, x) * beta (incrQuad h V (t, x)))

/-- The first good term `J₂(t) = ∫_cell Φ_a·β″(q)|∇q|²`. -/
def gwJ2 (a : ℝ) (x0 h : E3) (V : STime → E3) (b2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => torusGauss a x0 (t, x) * (b2 (incrQuad h V (t, x))
    * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x) * dvec (0, ee k) (incrQuad h V) (t, x)))

/-- The second good term `J₁(t) = ∫_cell Φ_a·β′(q)|∇δ_hu|²`. -/
def gwJ1 (a : ℝ) (x0 h : E3) (V : STime → E3) (b1 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => torusGauss a x0 (t, x)
    * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))

/-- The level-measure term `K₂(t) = ∫_cell Φ_a·β″(q)`. -/
def gwK2 (a : ℝ) (x0 h : E3) (V : STime → E3) (b2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  cellInt (fun x => torusGauss a x0 (t, x) * b2 (incrQuad h V (t, x)))

section Continuity

variable {a : ℝ} {x0 h : E3} {V : STime → E3} {beta b1 b2 : ℝ → ℝ}

lemma continuous_gwJ2 (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2) :
    Continuous (gwJ2 a x0 h V b2) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have hdq : ∀ k : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (dvec (0, ee k) (incrQuad h V)) :=
    fun k => contDiff_dvec _ hq _
  exact continuous_cellInt _
    ((contDiff_torusGauss a x0).mul ((hb2c.comp hq).mul
      (ContDiff.sum fun k _ => (hdq k).mul (hdq k)))).continuous

lemma continuous_gwJ1 (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) :
    Continuous (gwJ1 a x0 h V b1) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  exact continuous_cellInt _
    ((contDiff_torusGauss a x0).mul ((hb1c.comp hq).mul (contDiff_incrDissip h hV))).continuous

lemma continuous_gwK2 (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2) :
    Continuous (gwK2 a x0 h V b2) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  exact continuous_cellInt _ ((contDiff_torusGauss a x0).mul (hb2c.comp hq)).continuous

/-- The weighted mass is differentiable in time, with the derivative given by
the first term of the cell budget. -/
lemma hasDerivAt_gwMass (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (t : ℝ) :
    HasDerivAt (gwMass a x0 h V beta)
      (cellInt (fun x => dvec (1, 0)
        (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x))) t :=
  hasDerivAt_cellInt _
    ((contDiff_torusGauss a x0).mul (hbeta.comp (contDiff_incrQuad h hV))) t

lemma continuous_gwMassDeriv (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta) :
    Continuous fun t => cellInt (fun x => dvec (1, 0)
      (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x)) :=
  continuous_cellInt _
    (contDiff_dvec _ ((contDiff_torusGauss a x0).mul
      (hbeta.comp (contDiff_incrQuad h hV))) (1, 0)).continuous

end Continuity

/-! ## The space-time budget -/

/-- **The space-time weight-aware Caccioppoli budget.**  The time integral of
`ClayNS.gaussianGradientWeightedAbsorption` over a window `[t₀,t₁]`: the first
term integrates exactly to the increment of the weighted mass, and the constant
sources contribute `(t₁−t₀)` times a quantity that vanishes as the concentration
scale `a` tends to `0`.  This is the shape the De Giorgi recurrence consumes. -/
theorem gaussian_weighted_spacetime_budget {nu eta theta a lam A B Gp Bbeta : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta) (ha : 0 < a) (hlam : 0 < lam)
    {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x) (hb1le : ∀ x, b1 x ≤ 1 / lam)
    (hA : ∀ (z : STime) (c : Fin 3), |V z c| ≤ A)
    (hB : ∀ (z : STime) (c : Fin 3), |incrComp h V c z| ≤ B)
    (hGp : ∀ (z : STime) (c : Fin 3), |dvec (0, ee c) (incrPres h P) z| ≤ Gp)
    (hBbeta : ∀ z : STime, |beta (incrQuad h V z)| ≤ Bbeta)
    {t0 t1 : ℝ} (ht : t0 ≤ t1) :
    gwMass a x0 h V beta t1 - gwMass a x0 h V beta t0
        + ∫ t in t0..t1, ((1 - eta) * nu * gwJ2 a x0 h V b2 t
            + nu / 2 * gwJ1 a x0 h V b1 t)
      ≤ (∫ t in t0..t1, 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t)
        + (t1 - t0) * ((9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
              * (tgY a ^ 3 / lam)
            + 9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt a / lam)
            + Bbeta * (A * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a))) := by
  set Dt : ℝ → ℝ := fun t => cellInt (fun x => dvec (1, 0)
    (fun w => torusGauss a x0 w * beta (incrQuad h V w)) (t, x)) with hDt
  set Cst : ℝ := (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
        * (tgY a ^ 3 / lam)
      + 9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt a / lam)
      + Bbeta * (A * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a)) with hCst
  have hDcont : Continuous Dt := continuous_gwMassDeriv hV hbeta
  have hJ2cont : Continuous (gwJ2 a x0 h V b2) := continuous_gwJ2 hV hb2c
  have hJ1cont : Continuous (gwJ1 a x0 h V b1) := continuous_gwJ1 hV hb1c
  have hK2cont : Continuous (gwK2 a x0 h V b2) := continuous_gwK2 hV hb2c
  -- the pointwise-in-time inequality
  have hpt : ∀ t : ℝ, Dt t + ((1 - eta) * nu * gwJ2 a x0 h V b2 t
      + nu / 2 * gwJ1 a x0 h V b1 t)
      ≤ 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t + Cst := by
    intro t
    have := gaussianGradientWeightedAbsorption (nu := nu) (eta := eta) (theta := theta)
      (a := a) (lam := lam) (A := A) (B := B) (Gp := Gp) (Bbeta := Bbeta)
      hnu heta htheta ha hlam h x0 hV hP hVper hbeta hb1c hb2c hb1 hb2 hdiv hmom hB1 hB2
      hb1le hA hB hGp hBbeta t
    simp only [hDt, hCst, gwJ2, gwJ1, gwK2]
    linarith [this]
  -- integrate
  have hLcont : Continuous fun t => Dt t + ((1 - eta) * nu * gwJ2 a x0 h V b2 t
      + nu / 2 * gwJ1 a x0 h V b1 t) :=
    hDcont.add ((continuous_const.mul hJ2cont).add (continuous_const.mul hJ1cont))
  have hRcont : Continuous fun t =>
      27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t + Cst :=
    (continuous_const.mul hK2cont).add continuous_const
  have hmono := intervalIntegral.integral_mono_on (μ := volume) ht
    (hLcont.intervalIntegrable t0 t1) (hRcont.intervalIntegrable t0 t1)
    (fun t _ => hpt t)
  -- the left-hand side splits, and the derivative term is exact
  have hFTC : (∫ t in t0..t1, Dt t) = gwMass a x0 h V beta t1 - gwMass a x0 h V beta t0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_gwMass hV hbeta t) (hDcont.intervalIntegrable t0 t1)
  have hLsplit : (∫ t in t0..t1, (Dt t + ((1 - eta) * nu * gwJ2 a x0 h V b2 t
        + nu / 2 * gwJ1 a x0 h V b1 t)))
      = (∫ t in t0..t1, Dt t)
        + ∫ t in t0..t1, ((1 - eta) * nu * gwJ2 a x0 h V b2 t
            + nu / 2 * gwJ1 a x0 h V b1 t) :=
    intervalIntegral.integral_add (hDcont.intervalIntegrable t0 t1)
      (show IntervalIntegrable (fun t => (1 - eta) * nu * gwJ2 a x0 h V b2 t
            + nu / 2 * gwJ1 a x0 h V b1 t) volume t0 t1 from
        ((continuous_const.mul hJ2cont).add
          (continuous_const.mul hJ1cont)).intervalIntegrable t0 t1)
  have hRsplit : (∫ t in t0..t1,
        (27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t + Cst))
      = (∫ t in t0..t1, 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t)
        + (t1 - t0) * Cst := by
    have h1 : IntervalIntegrable
        (fun t => 27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 a x0 h V b2 t) volume t0 t1 :=
      (continuous_const.mul hK2cont).intervalIntegrable t0 t1
    have h2 : IntervalIntegrable (fun _ : ℝ => Cst) volume t0 t1 :=
      continuous_const.intervalIntegrable t0 t1
    rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const, smul_eq_mul]
  rw [hLsplit, hFTC, hRsplit] at hmono
  exact hmono

end ClayNS

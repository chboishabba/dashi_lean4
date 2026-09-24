/-
# The scale-invariant choice of the concentration parameter, `a = ηR²`

`GaussianWeightedAbsorption.lean` proves the weight-aware Caccioppoli budget in
which every source carries a positive power of the concentration scale `a`.
Taking `a → 0` at a *fixed* physical cylinder is not the right limit for a De
Giorgi oscillation argument: the estimate has to be usable at every radius `R`
with a constant that does not degenerate.

Under Navier–Stokes parabolic rescaling `(t,x) ↦ (R²t, Rx)` the concentration
parameter has the dimensions of a squared length, so the scale-invariant choice
is

  `a = ηR²`,   `0 < η` fixed,

for which the Gaussian width is `√a = √η·R`: a fixed fraction of the cylinder
radius at *every* scale.  This file records what the weighted source of the
budget becomes under that choice.

* `ClayNS.gwSource` — the source constant of
  `ClayNS.gaussianGradientWeightedAbsorption`, isolated as a function of `a`;
* `ClayNS.gwSource_scaleInvariant_eq` — the **exact** expansion at `a = ηR²`:
  the source is `R·K₁(η) + R²·K₂(η) + R³·K₃(η)`, with all three coefficients
  independent of `R`.  In particular the source is `O(R)` — it carries a
  *positive scaling dimension*, which is exactly what a dyadic tail argument
  needs;
* `ClayNS.gwSource_scaleInvariant_le` — the packaged bound
  `source ≤ R·K(η)` for `0 < R ≤ 1`;
* `ClayNS.gwSource_scaleInvariant_tendsto_zero` — consequently the source tends
  to `0` linearly as `R ↓ 0` along the scale-invariant family, not merely along
  an artificial `a → 0` limit at fixed geometry.

There is no `a⁻¹` anywhere: the `K₀/a` obstruction recorded in
`GaussianLinearBudgetAudit.lean` was an artefact of the unweighted supremum
estimate, and after `C53`/`C54` the whole source is a sum of positive powers of
`a`, hence of `R`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianWeightedAbsorption

open Real

noncomputable section

namespace ClayNS

/-- The source constant of the weight-aware Caccioppoli budget
`ClayNS.gaussianGradientWeightedAbsorption`, as a function of the concentration
scale `a`. -/
def gwSource (nu theta lam A B Gp Bbeta a : ℝ) : ℝ :=
  (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2) * (tgY a ^ 3 / lam)
    + 9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt a / lam)
    + Bbeta * (A * (6 * π ^ 3 * a) + nu * (tgLapC * Real.sqrt a))

/-- The coefficient of `R` in the scale-invariant expansion: the Fisher-information
term and the Gaussian adjoint residual. -/
def gwK1 (nu theta lam A B Bbeta eta : ℝ) : ℝ :=
  9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt eta / lam)
    + Bbeta * nu * (tgLapC * Real.sqrt eta)

/-- The coefficient of `R²`: the pointwise-weighted Young term. -/
def gwK2c (A Bbeta eta : ℝ) : ℝ := Bbeta * A * (6 * π ^ 3 * eta)

/-- The coefficient of `R³`: the weighted mass term. -/
def gwK3 (nu theta lam A B Gp eta : ℝ) : ℝ :=
  (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
    * (Real.sqrt (π ^ 3) ^ 3 * (Real.sqrt eta) ^ 3 / lam)

/-- The packaged scale-invariant constant. -/
def gwScaleConst (nu theta lam A B Gp Bbeta eta : ℝ) : ℝ :=
  gwK1 nu theta lam A B Bbeta eta + gwK2c A Bbeta eta + gwK3 nu theta lam A B Gp eta

lemma sqrt_eta_mul_sq {eta R : ℝ} (heta : 0 ≤ eta) (hR : 0 ≤ R) :
    Real.sqrt (eta * R ^ 2) = Real.sqrt eta * R := by
  rw [Real.sqrt_mul heta, Real.sqrt_sq hR]

/-- **The exact scale-invariant expansion.**  At `a = ηR²` the source of the
weight-aware budget is a polynomial in `R` with no constant term:

  `source = R·K₁(η) + R²·K₂(η) + R³·K₃(η)`.

Every coefficient is independent of `R`, so the estimate has the same
dimensionless size at every scale, and the source carries the positive scaling
dimension `R¹`. -/
theorem gwSource_scaleInvariant_eq (nu theta lam A B Gp Bbeta : ℝ) {eta R : ℝ}
    (heta : 0 ≤ eta) (hR : 0 ≤ R) :
    gwSource nu theta lam A B Gp Bbeta (eta * R ^ 2)
      = R * gwK1 nu theta lam A B Bbeta eta
        + R ^ 2 * gwK2c A Bbeta eta
        + R ^ 3 * gwK3 nu theta lam A B Gp eta := by
  have hs : Real.sqrt (eta * R ^ 2) = Real.sqrt eta * R := sqrt_eta_mul_sq heta hR
  have hY : tgY (eta * R ^ 2) = Real.sqrt (π ^ 3) * (Real.sqrt eta * R) := by
    rw [tgY_eq, hs]
  unfold gwSource gwK1 gwK2c gwK3
  rw [hY, hs]
  ring

/-- **The packaged scale-invariant bound.**  For `0 < R ≤ 1` and nonnegative
data, the source of the weight-aware budget at `a = ηR²` is at most `R` times a
constant depending only on the dimensionless ratio `η` and the data. -/
theorem gwSource_scaleInvariant_le {nu theta lam A B Gp Bbeta eta R : ℝ}
    (hnu : 0 ≤ nu) (htheta : 0 < theta) (hlam : 0 < lam) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hGp : 0 ≤ Gp) (hBbeta : 0 ≤ Bbeta) (heta : 0 ≤ eta) (hR : 0 ≤ R) (hR1 : R ≤ 1) :
    gwSource nu theta lam A B Gp Bbeta (eta * R ^ 2)
      ≤ R * gwScaleConst nu theta lam A B Gp Bbeta eta := by
  have hFI : 0 ≤ tgFisherC := by
    unfold tgFisherC; positivity
  have hLap : 0 ≤ tgLapC := by
    unfold tgLapC; positivity
  have hK1 : 0 ≤ gwK1 nu theta lam A B Bbeta eta := by
    unfold gwK1; positivity
  have hK2 : 0 ≤ gwK2c A Bbeta eta := by unfold gwK2c; positivity
  have hK3 : 0 ≤ gwK3 nu theta lam A B Gp eta := by
    have hc : 0 ≤ 9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2 := by
      have h1 : (0:ℝ) ≤ 9 * A ^ 2 * B ^ 2 / (2 * nu) := by positivity
      have h2 : (0:ℝ) ≤ 3 * B * Gp := by positivity
      have h3 : (0:ℝ) ≤ 9 * A * B ^ 2 * theta / 2 := by positivity
      linarith
    unfold gwK3
    have : (0:ℝ) ≤ Real.sqrt (π ^ 3) ^ 3 * Real.sqrt eta ^ 3 / lam := by positivity
    exact mul_nonneg hc this
  rw [gwSource_scaleInvariant_eq nu theta lam A B Gp Bbeta heta hR]
  have h2 : R ^ 2 * gwK2c A Bbeta eta ≤ R * gwK2c A Bbeta eta := by
    have : R ^ 2 ≤ R := by nlinarith
    exact mul_le_mul_of_nonneg_right this hK2
  have h3 : R ^ 3 * gwK3 nu theta lam A B Gp eta ≤ R * gwK3 nu theta lam A B Gp eta := by
    have : R ^ 3 ≤ R := by nlinarith
    exact mul_le_mul_of_nonneg_right this hK3
  unfold gwScaleConst
  nlinarith [h2, h3]

/-- **Linear decay along the scale-invariant family.**  The source vanishes as
the cylinder radius shrinks, with the Gaussian width locked to `√η·R`. -/
theorem gwSource_scaleInvariant_tendsto_zero (nu theta lam A B Gp Bbeta eta : ℝ)
    (heta : 0 ≤ eta) :
    Filter.Tendsto (fun R : ℝ => gwSource nu theta lam A B Gp Bbeta (eta * R ^ 2))
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
  have hcong : Set.EqOn (fun R : ℝ => gwSource nu theta lam A B Gp Bbeta (eta * R ^ 2))
      (fun R : ℝ => R * gwK1 nu theta lam A B Bbeta eta
        + R ^ 2 * gwK2c A Bbeta eta + R ^ 3 * gwK3 nu theta lam A B Gp eta)
      (Set.Ici 0) := fun R hR =>
    gwSource_scaleInvariant_eq nu theta lam A B Gp Bbeta heta hR
  have hpoly : Filter.Tendsto (fun R : ℝ => R * gwK1 nu theta lam A B Bbeta eta
      + R ^ 2 * gwK2c A Bbeta eta + R ^ 3 * gwK3 nu theta lam A B Gp eta)
      (nhdsWithin 0 (Set.Ici 0)) (nhds 0) := by
    have hc : Continuous fun R : ℝ => R * gwK1 nu theta lam A B Bbeta eta
        + R ^ 2 * gwK2c A Bbeta eta + R ^ 3 * gwK3 nu theta lam A B Gp eta := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  exact hpoly.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hcong).symm

/-! ## The budget at the scale-invariant weight -/

/-- **The weight-aware Caccioppoli budget at the scale-invariant weight**
`a = κR²`.  Apart from the coercivity-paired level-measure term, the whole
right-hand side is bounded by `R` times a constant that depends only on the data
and the fixed dimensionless ratio `κ` — never on `R`.  This is the form the
dyadic/De Giorgi assembly consumes: a source with a strictly positive scaling
dimension. -/
theorem gaussianGradientWeightedAbsorption_scaleInvariant
    {nu eta theta lam A B Gp Bbeta kap R : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta) (hkap : 0 < kap) (hR : 0 < R)
    (hR1 : R ≤ 1) (hlam : 0 < lam)
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
    (t : ℝ) :
    cellInt (fun x => dvec (1, 0)
          (fun w => torusGauss (kap * R ^ 2) x0 w * beta (incrQuad h V w)) (t, x))
        + (1 - eta) * nu * cellInt (fun x => torusGauss (kap * R ^ 2) x0 (t, x)
            * (b2 (incrQuad h V (t, x))
              * ∑ k, dvec (0, ee k) (incrQuad h V) (t, x)
                  * dvec (0, ee k) (incrQuad h V) (t, x)))
        + nu / 2 * cellInt (fun x => torusGauss (kap * R ^ 2) x0 (t, x)
            * (b1 (incrQuad h V (t, x)) * incrDissip h V (t, x)))
      ≤ 27 * A ^ 2 * B ^ 4 / (4 * eta * nu)
            * cellInt (fun x => torusGauss (kap * R ^ 2) x0 (t, x)
                * b2 (incrQuad h V (t, x)))
        + R * gwScaleConst nu theta lam A B Gp Bbeta kap := by
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hA (t, 0) 0)
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB (t, 0) 0)
  have hGp0 : 0 ≤ Gp := le_trans (abs_nonneg _) (hGp (t, 0) 0)
  have hBb0 : 0 ≤ Bbeta := le_trans (abs_nonneg _) (hBbeta (t, 0))
  have ha : 0 < kap * R ^ 2 := by positivity
  have hmain := gaussianGradientWeightedAbsorption (nu := nu) (eta := eta) (theta := theta)
    (a := kap * R ^ 2) (lam := lam) (A := A) (B := B) (Gp := Gp) (Bbeta := Bbeta)
    hnu heta htheta ha hlam h x0 hV hP hVper hbeta hb1c hb2c hb1 hb2 hdiv hmom hB1 hB2
    hb1le hA hB hGp hBbeta t
  have hsrc := gwSource_scaleInvariant_le (nu := nu) (theta := theta) (lam := lam)
    (A := A) (B := B) (Gp := Gp) (Bbeta := Bbeta) (eta := kap) (R := R)
    hnu.le htheta hlam hA0 hB0 hGp0 hBb0 hkap.le hR.le hR1
  unfold gwSource at hsrc
  linarith [hmain, hsrc]

end ClayNS

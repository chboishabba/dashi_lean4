/-
# Instantiating the expenditure ledger on the Navier–Stokes budget

`ExpenditureLedger.lean` proves the post-Caccioppoli algebra abstractly:
`E_total = E_coercive + E_absorbed` together with a potential balance whose
replenishment is paid by the absorbed dissipation plus a remainder gives
`E_coercive ≤ Φ(0) + E_remainder`.

This file *instantiates* it on the actual Navier–Stokes objects: the potential
is the Gaussian-weighted mass `M(t)`, the coercive expenditure is the pair of
good terms `(1−η)νJ₂ + (ν/2)J₁` of the weight-aware budget, the absorbed part is
the coercivity-paired level-measure term `K₂`, and the remainder is the source,
which at the scale-invariant weight `a = κR²` is bounded by
`R·gwScaleConst` — a quantity with a *strictly positive scaling dimension*.

`ClayNS.coercive_expenditure_scaleInvariant`:

  `∫[(1−η)νJ₂ + (ν/2)J₁] ≤ M(t₀) + ∫(27A²B⁴/4ην)K₂ + (t₁−t₀)·R·gwScaleConst`.

So the total coercive expenditure over a window is paid by the initial weighted
mass, the absorbed level-measure term, and a remainder that can be made as small
as one likes by shrinking the concentration scale `R` — the exact shape the
tail/absorption machinery of `ExpenditureLedger.lean` consumes.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianSpacetimeBudget
import RequestProject.NavierStokes.ScaleInvariantWeightChoice
import RequestProject.NavierStokes.ExpenditureLedger

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-- **The coercive expenditure of the Navier–Stokes budget, at the
scale-invariant weight.**  The instantiation of `ClayNS.coercive_expenditure_le`
on the weight-aware space-time budget: the coercive expenditure over the window
is bounded by the initial weighted mass, the absorbed level-measure term, and a
remainder proportional to the concentration scale `R`. -/
theorem coercive_expenditure_scaleInvariant {nu eta theta kap lam A B Gp Bbeta R : ℝ}
    (hnu : 0 < nu) (heta : 0 < eta) (htheta : 0 < theta) (hkap : 0 < kap)
    (hR : 0 < R) (hR1 : R ≤ 1) (hlam : 0 < lam)
    {V : STime → E3} {P : STime → ℝ} (h x0 : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hVper : SpacePeriodic V)
    {beta b1 b2 : ℝ → ℝ} (hbeta : ContDiff ℝ (⊤ : ℕ∞) beta)
    (hb1c : ContDiff ℝ (⊤ : ℕ∞) b1) (hb2c : ContDiff ℝ (⊤ : ℕ∞) b2)
    (hb1 : ∀ x, HasDerivAt beta (b1 x) x) (hb2 : ∀ x, HasDerivAt b1 (b2 x) x)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (hB1 : ∀ x, 0 ≤ b1 x) (hB2 : ∀ x, 0 ≤ b2 x) (hb1le : ∀ x, b1 x ≤ 1 / lam)
    (hA : ∀ (z : STime) (c : Fin 3), |V z c| ≤ A)
    (hBB : ∀ (z : STime) (c : Fin 3), |incrComp h V c z| ≤ B)
    (hGpb : ∀ (z : STime) (c : Fin 3), |dvec (0, ee c) (incrPres h P) z| ≤ Gp)
    (hBbeta : ∀ z : STime, |beta (incrQuad h V z)| ≤ Bbeta)
    (hbeta0 : ∀ s : ℝ, 0 ≤ beta s)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hGp0 : 0 ≤ Gp) (hBbeta0 : 0 ≤ Bbeta)
    {t0 t1 : ℝ} (ht : t0 ≤ t1) :
    (∫ t in t0..t1, ((1 - eta) * nu * gwJ2 (kap * R ^ 2) x0 h V b2 t
        + nu / 2 * gwJ1 (kap * R ^ 2) x0 h V b1 t))
      ≤ gwMass (kap * R ^ 2) x0 h V beta t0
        + ((∫ t in t0..t1,
              27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 (kap * R ^ 2) x0 h V b2 t)
            + (t1 - t0) * (R * gwScaleConst nu theta lam A B Gp Bbeta kap)) := by
  have ha : (0:ℝ) < kap * R ^ 2 := by positivity
  have hbud := gaussian_weighted_spacetime_budget (nu := nu) (eta := eta) (theta := theta)
    (a := kap * R ^ 2) (lam := lam) (A := A) (B := B) (Gp := Gp) (Bbeta := Bbeta)
    hnu heta htheta ha hlam h x0 hV hP hVper hbeta hb1c hb2c hb1 hb2 hdiv hmom hB1 hB2
    hb1le hA hBB hGpb hBbeta ht
  -- the source of the budget is exactly `gwSource` at the scale-invariant weight
  have hsrc : (9 * A ^ 2 * B ^ 2 / (2 * nu) + 3 * B * Gp + 9 * A * B ^ 2 * theta / 2)
        * (tgY (kap * R ^ 2) ^ 3 / lam)
      + 9 * A * B ^ 2 / (2 * theta) * (tgFisherC * Real.sqrt (kap * R ^ 2) / lam)
      + Bbeta * (A * (6 * π ^ 3 * (kap * R ^ 2)) + nu * (tgLapC * Real.sqrt (kap * R ^ 2)))
      = gwSource nu theta lam A B Gp Bbeta (kap * R ^ 2) := by
    unfold gwSource
    ring
  have hsrcle : gwSource nu theta lam A B Gp Bbeta (kap * R ^ 2)
      ≤ R * gwScaleConst nu theta lam A B Gp Bbeta kap :=
    gwSource_scaleInvariant_le hnu.le htheta hlam hA0 hB0 hGp0 hBbeta0 hkap.le hR.le hR1
  have hdt : (0:ℝ) ≤ t1 - t0 := by linarith
  have hsrcmul : (t1 - t0) * gwSource nu theta lam A B Gp Bbeta (kap * R ^ 2)
      ≤ (t1 - t0) * (R * gwScaleConst nu theta lam A B Gp Bbeta kap) :=
    mul_le_mul_of_nonneg_left hsrcle hdt
  rw [hsrc] at hbud
  -- the terminal potential is nonnegative
  have hPhiT : 0 ≤ gwMass (kap * R ^ 2) x0 h V beta t1 := by
    refine cellInt_nonneg fun x => ?_
    exact mul_nonneg (torusGauss_nonneg _ _ _) (hbeta0 _)
  -- instantiate the ledger
  set Ecoer := ∫ t in t0..t1, ((1 - eta) * nu * gwJ2 (kap * R ^ 2) x0 h V b2 t
    + nu / 2 * gwJ1 (kap * R ^ 2) x0 h V b1 t) with hEcoer
  set Eabs := ∫ t in t0..t1,
    27 * A ^ 2 * B ^ 4 / (4 * eta * nu) * gwK2 (kap * R ^ 2) x0 h V b2 t with hEabs
  set Erem := Eabs + (t1 - t0) * (R * gwScaleConst nu theta lam A B Gp Bbeta kap) with hErem
  refine coercive_expenditure_le (Etotal := Ecoer + Eabs) (Eabsorbed := Eabs)
    (Ereplenish := Eabs + Erem) (PhiT := gwMass (kap * R ^ 2) x0 h V beta t1)
    rfl hPhiT ?_ (by linarith)
  have : gwMass (kap * R ^ 2) x0 h V beta t1 + Ecoer
      ≤ gwMass (kap * R ^ 2) x0 h V beta t0 + Eabs
        + (t1 - t0) * (R * gwScaleConst nu theta lam A B Gp Bbeta kap) := by
    linarith [hbud, hsrcmul]
  simp only [hErem]
  linarith [this]

end ClayNS

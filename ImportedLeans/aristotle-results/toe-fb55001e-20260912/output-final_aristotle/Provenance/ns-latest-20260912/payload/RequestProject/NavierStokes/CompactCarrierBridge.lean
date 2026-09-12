/-
# The compact-support carrier bridge

The weight-aware Caccioppoli budget lives on the periodic cell against a
strictly positive Gaussian; the parabolic `L^{10/3}` embedding
(`ClayNS.parabolic_gain_of_caccioppoli`) consumes *compactly supported*
truncations on `ℝ³`.  This file builds the missing bridge: a cut-off carrier
whose two Caccioppoli slots — the supremum in time of the `L²` mass and the
total dissipation — are bounded by the Gaussian-weighted budget with constants
that depend only on the localization data `(κ, R, L)`, never on the level of the
truncation.

* `ClayNS.concBall` — the concentration ball `∑_j(x_j−x₀_j)² ≤ R²`, identified
  with the metric closed ball (`ClayNS.concBall_eq_closedBall`), hence compact
  and measurable.
* `ClayNS.BallCutoff` — the cut-off data: a smooth `[0,1]`-valued function
  vanishing off the concentration ball, with a gradient bound `L`.  Such data
  exists, and can be taken to equal `1` on the half ball
  (`ClayNS.exists_ballCutoff`), so the bridge is not vacuous.
* `ClayNS.cutoff_mass_le_weighted` — the first slot: the *unweighted* `L²` mass
  of the cut-off carrier is at most `exp(1/(4κ))` times the Gaussian-weighted
  mass on the ball.
* `ClayNS.cutoff_dissipation_le_weighted` — the second slot: the unweighted
  dissipation of the cut-off carrier is at most
  `2exp(1/(4κ))·(weighted dissipation + L²·weighted mass)`; the `L²` factor is
  the classical Caccioppoli cut-off loss, and it multiplies the *mass* term only.
* `ClayNS.compactCarrier_parabolic_gain` — the two combined and fed to the
  parabolic embedding: from a sup-in-time weighted mass bound `Mw` and a total
  weighted dissipation bound `Dw`, the carrier obeys

    `∫∫|ψq|^{10/3} ≤ C_S·K^{5/3}`,  `K = 2e^{1/(4κ)}(Mw + Dw + L²(b−a)Mw)`,

  which is exactly the shape of the embedding input `hEmb` of the De Giorgi
  recurrence.  Every constant is independent of the truncation level: only the
  budgets `Mw, Dw` carry the level.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianUnweighting
import RequestProject.NavierStokes.ParabolicGain

open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The concentration ball -/

/-- The concentration ball of radius `R` about `x₀`, in the coordinate form used
by the Gaussian estimates. -/
def concBall (x0 : E3) (R : ℝ) : Set E3 := {x | ∑ j, (x j - x0 j) ^ 2 ≤ R ^ 2}

lemma concBall_eq_closedBall (x0 : E3) {R : ℝ} (hR : 0 ≤ R) :
    concBall x0 R = Metric.closedBall x0 R := by
  ext x
  rw [Metric.mem_closedBall, EuclideanSpace.dist_eq]
  have hrw : (∑ j, dist (x j) (x0 j) ^ 2) = ∑ j, (x j - x0 j) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by rw [Real.dist_eq, sq_abs]
  rw [hrw]
  constructor
  · intro h
    have h1 := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq hR] at h1
  · intro h
    have h0 : (0:ℝ) ≤ ∑ j, (x j - x0 j) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hs : 0 ≤ Real.sqrt (∑ j, (x j - x0 j) ^ 2) := Real.sqrt_nonneg _
    have h2 : Real.sqrt (∑ j, (x j - x0 j) ^ 2) ^ 2 ≤ R ^ 2 := by nlinarith
    rwa [Real.sq_sqrt h0] at h2

lemma isClosed_concBall (x0 : E3) {R : ℝ} (hR : 0 ≤ R) : IsClosed (concBall x0 R) := by
  rw [concBall_eq_closedBall x0 hR]; exact Metric.isClosed_closedBall

lemma isCompact_concBall (x0 : E3) {R : ℝ} (hR : 0 ≤ R) : IsCompact (concBall x0 R) := by
  rw [concBall_eq_closedBall x0 hR]; exact isCompact_closedBall x0 R

lemma measurableSet_concBall (x0 : E3) {R : ℝ} (hR : 0 ≤ R) :
    MeasurableSet (concBall x0 R) := (isClosed_concBall x0 hR).measurableSet

lemma mem_concBall_iff (x0 : E3) (R : ℝ) (x : E3) :
    x ∈ concBall x0 R ↔ ∑ j, (x j - x0 j) ^ 2 ≤ R ^ 2 := Iff.rfl

/-! ## Cut-off data -/

/-- Cut-off data on the concentration ball: a smooth function with values in
`[0,1]`, vanishing off the ball, with a gradient bound. -/
structure BallCutoff (x0 : E3) (R : ℝ) where
  /-- The cut-off function. -/
  fn : E3 → ℝ
  /-- It is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) fn
  /-- It is nonnegative. -/
  nonneg : ∀ x, 0 ≤ fn x
  /-- It is at most one. -/
  le_one : ∀ x, fn x ≤ 1
  /-- It vanishes off the concentration ball. -/
  zero_outside : ∀ x ∉ concBall x0 R, fn x = 0
  /-- A bound for its gradient. -/
  gradBound : ℝ
  /-- The gradient bound holds. -/
  grad_le : ∀ x, ‖fderiv ℝ fn x‖ ≤ gradBound

namespace BallCutoff

variable {x0 : E3} {R : ℝ}

lemma gradBound_nonneg (psi : BallCutoff x0 R) : 0 ≤ psi.gradBound :=
  le_trans (norm_nonneg _) (psi.grad_le x0)

lemma support_subset (psi : BallCutoff x0 R) :
    Function.support psi.fn ⊆ concBall x0 R := by
  intro x hx
  by_contra hmem
  exact hx (psi.zero_outside x hmem)

lemma hasCompactSupport (psi : BallCutoff x0 R) (hR : 0 ≤ R) :
    HasCompactSupport psi.fn := by
  refine IsCompact.of_isClosed_subset (isCompact_concBall x0 hR) isClosed_closure ?_
  exact closure_minimal psi.support_subset (isClosed_concBall x0 hR)

/-- The cut-off carrier: `ψ·q`. -/
def carrier (psi : BallCutoff x0 R) (q : E3 → ℝ) : E3 → ℝ := fun x => psi.fn x * q x

lemma carrier_contDiff (psi : BallCutoff x0 R) {q : E3 → ℝ} (hq : ContDiff ℝ 1 q) :
    ContDiff ℝ 1 (psi.carrier q) :=
  (psi.smooth.of_le (by exact_mod_cast le_top : (1:WithTop ℕ∞) ≤ (⊤:ℕ∞))).mul hq

lemma carrier_hasCompactSupport (psi : BallCutoff x0 R) (hR : 0 ≤ R) (q : E3 → ℝ) :
    HasCompactSupport (psi.carrier q) :=
  HasCompactSupport.mul_right (psi.hasCompactSupport hR)

lemma carrier_zero_outside (psi : BallCutoff x0 R) (q : E3 → ℝ) :
    ∀ x ∉ concBall x0 R, psi.carrier q x = 0 := fun x hx => by
  simp [carrier, psi.zero_outside x hx]

/-- Off the (closed) concentration ball the carrier vanishes identically on a
neighbourhood, so its derivative vanishes there too. -/
lemma carrier_fderiv_zero_outside (psi : BallCutoff x0 R) (hR : 0 ≤ R) (q : E3 → ℝ)
    {x : E3} (hx : x ∉ concBall x0 R) : fderiv ℝ (psi.carrier q) x = 0 := by
  have hopen : IsOpen (concBall x0 R)ᶜ := (isClosed_concBall x0 hR).isOpen_compl
  have hnhds : (concBall x0 R)ᶜ ∈ nhds x := hopen.mem_nhds hx
  have heq : psi.carrier q =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [hnhds] with y hy using psi.carrier_zero_outside q y hy
  rw [heq.fderiv_eq]
  simp

/-- The pointwise Caccioppoli bound for the carrier's gradient. -/
lemma carrier_fderiv_sq_le (psi : BallCutoff x0 R) {q : E3 → ℝ} (hq : ContDiff ℝ 1 q)
    (x : E3) :
    ‖fderiv ℝ (psi.carrier q) x‖ ^ 2
      ≤ 2 * (‖fderiv ℝ q x‖ ^ 2 + psi.gradBound ^ 2 * (q x) ^ 2) := by
  have hpsid : DifferentiableAt ℝ psi.fn x :=
    (psi.smooth.differentiable (by simp)).differentiableAt
  have hqd : DifferentiableAt ℝ q x := (hq.differentiable (by norm_num)).differentiableAt
  have hderiv : fderiv ℝ (psi.carrier q) x
      = psi.fn x • fderiv ℝ q x + q x • fderiv ℝ psi.fn x := by
    have : psi.carrier q = psi.fn * q := rfl
    rw [this, fderiv_mul hpsid hqd]
  have hnorm : ‖fderiv ℝ (psi.carrier q) x‖
      ≤ ‖psi.fn x‖ * ‖fderiv ℝ q x‖ + ‖q x‖ * ‖fderiv ℝ psi.fn x‖ := by
    rw [hderiv]
    refine le_trans (norm_add_le _ _) ?_
    simp [norm_smul]
  have h1 : ‖psi.fn x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (psi.nonneg x)]; exact psi.le_one x
  have h2 : ‖fderiv ℝ psi.fn x‖ ≤ psi.gradBound := psi.grad_le x
  have hq0 : (0:ℝ) ≤ ‖q x‖ := norm_nonneg _
  have hg0 : (0:ℝ) ≤ ‖fderiv ℝ q x‖ := norm_nonneg _
  have hstep : ‖fderiv ℝ (psi.carrier q) x‖
      ≤ ‖fderiv ℝ q x‖ + psi.gradBound * ‖q x‖ := by
    refine hnorm.trans ?_
    have ha : ‖psi.fn x‖ * ‖fderiv ℝ q x‖ ≤ 1 * ‖fderiv ℝ q x‖ :=
      mul_le_mul_of_nonneg_right h1 hg0
    have hb : ‖q x‖ * ‖fderiv ℝ psi.fn x‖ ≤ ‖q x‖ * psi.gradBound :=
      mul_le_mul_of_nonneg_left h2 hq0
    nlinarith [ha, hb]
  have hnn : (0:ℝ) ≤ ‖fderiv ℝ (psi.carrier q) x‖ := norm_nonneg _
  have hsq := mul_self_le_mul_self hnn hstep
  have hqx : ‖q x‖ ^ 2 = (q x) ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  nlinarith [hsq, sq_nonneg (‖fderiv ℝ q x‖ - psi.gradBound * ‖q x‖), hqx,
    psi.gradBound_nonneg, hq0, hg0]

end BallCutoff

/-! ## Existence of cut-off data -/

/-- **Cut-off data exists.**  There is a smooth `[0,1]`-valued cut-off supported
in the concentration ball of radius `R` which equals `1` on the half ball.  So
the bridge below is not vacuous. -/
theorem exists_ballCutoff (x0 : E3) {R : ℝ} (hR : 0 < R) :
    ∃ psi : BallCutoff x0 R, ∀ x ∈ concBall x0 (R / 2), psi.fn x = 1 := by
  set f : ContDiffBump x0 := ⟨R / 2, R, by linarith, by linarith⟩ with hf
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (f : E3 → ℝ) := f.contDiff
  have hcs : HasCompactSupport (f : E3 → ℝ) := f.hasCompactSupport
  have hcsd : HasCompactSupport (fun x => fderiv ℝ (f : E3 → ℝ) x) := hcs.fderiv ℝ
  have hcont : Continuous (fun x => fderiv ℝ (f : E3 → ℝ) x) :=
    hsmooth.continuous_fderiv (by simp)
  obtain ⟨L, hL⟩ := hcsd.exists_bound_of_continuous hcont
  have hzero : ∀ x ∉ concBall x0 R, (f : E3 → ℝ) x = 0 := by
    intro x hx
    have hnotsupp : x ∉ Function.support (f : E3 → ℝ) := by
      rw [f.support_eq]
      intro hmem
      exact hx (by
        rw [concBall_eq_closedBall x0 hR.le]
        exact Metric.ball_subset_closedBall hmem)
    simpa using hnotsupp
  refine ⟨⟨(f : E3 → ℝ), hsmooth, fun x => f.nonneg, fun x => f.le_one, hzero, L, hL⟩, ?_⟩
  intro x hx
  refine f.one_of_mem_closedBall ?_
  have : x ∈ concBall x0 (R / 2) := hx
  rw [concBall_eq_closedBall x0 (by linarith : (0:ℝ) ≤ R / 2)] at this
  exact this

/-! ## The two Caccioppoli slots -/

variable {kap R : ℝ}

/-- **First slot: the mass.**  The unweighted `L²` mass of the cut-off carrier is
controlled by the Gaussian-weighted mass on the concentration ball, with the
`R`-independent constant `exp(1/(4κ))`. -/
theorem cutoff_mass_le_weighted (hkap : 0 < kap) (hR : 0 < R) (x0 : E3) (t : ℝ)
    (psi : BallCutoff x0 R) {q : E3 → ℝ} (hq : Continuous q) :
    (∫ x, (psi.carrier q x) ^ 2)
      ≤ Real.exp (1 / (4 * kap))
        * ∫ x in concBall x0 R, torusGauss (kap * R ^ 2) x0 (t, x) * (q x) ^ 2 := by
  set S := concBall x0 R with hS
  have hScomp : IsCompact S := isCompact_concBall x0 hR.le
  have hSmeas : MeasurableSet S := measurableSet_concBall x0 hR.le
  have hcarr : Continuous (psi.carrier q) :=
    ((psi.smooth.continuous).mul hq)
  -- restrict to the ball
  have hzero : ∀ x ∉ S, (psi.carrier q x) ^ 2 = 0 := by
    intro x hx
    rw [psi.carrier_zero_outside q x hx]; ring
  have hrestrict : (∫ x, (psi.carrier q x) ^ 2) = ∫ x in S, (psi.carrier q x) ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- ψ² ≤ 1 on the ball
  have hint1 : IntegrableOn (fun x => (psi.carrier q x) ^ 2) S volume :=
    (hcarr.pow 2).continuousOn.integrableOn_compact hScomp
  have hint2 : IntegrableOn (fun x => (q x) ^ 2) S volume :=
    (hq.pow 2).continuousOn.integrableOn_compact hScomp
  have hintw : IntegrableOn
      (fun x => torusGauss (kap * R ^ 2) x0 (t, x) * (q x) ^ 2) S volume := by
    refine Continuous.continuousOn ?_ |>.integrableOn_compact hScomp
    exact (((continuous_torusGauss (kap * R ^ 2) x0).comp
      (continuous_const.prodMk continuous_id)).mul (hq.pow 2))
  have hstep1 : (∫ x in S, (psi.carrier q x) ^ 2) ≤ ∫ x in S, (q x) ^ 2 := by
    refine setIntegral_mono_on hint1 hint2 hSmeas fun x _ => ?_
    have hp : 0 ≤ psi.fn x := psi.nonneg x
    have h1 : psi.fn x ≤ 1 := psi.le_one x
    have : (psi.carrier q x) ^ 2 = (psi.fn x) ^ 2 * (q x) ^ 2 := by
      simp [BallCutoff.carrier]; ring
    rw [this]
    have hsq : (psi.fn x) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (q x), hsq]
  have hstep2 := setIntegral_le_gaussianWeighted_scaleInvariant hkap hR x0 t hSmeas
    (f := fun x => (q x) ^ 2) (fun x _ => sq_nonneg _) (fun x hx => hx) hint2 hintw
  rw [hrestrict]
  exact hstep1.trans hstep2

/-- **Second slot: the dissipation.**  The unweighted dissipation of the cut-off
carrier is controlled by the Gaussian-weighted dissipation plus the Caccioppoli
cut-off loss `L²` times the Gaussian-weighted mass. -/
theorem cutoff_dissipation_le_weighted (hkap : 0 < kap) (hR : 0 < R) (x0 : E3) (t : ℝ)
    (psi : BallCutoff x0 R) {q : E3 → ℝ} (hq : ContDiff ℝ 1 q) :
    (∫ x, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2)
      ≤ 2 * Real.exp (1 / (4 * kap))
        * ((∫ x in concBall x0 R,
              torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ q x‖ ^ 2)
            + psi.gradBound ^ 2
              * ∫ x in concBall x0 R, torusGauss (kap * R ^ 2) x0 (t, x) * (q x) ^ 2) := by
  set S := concBall x0 R with hS
  set L := psi.gradBound with hL
  set Gam : E3 → ℝ := fun x => torusGauss (kap * R ^ 2) x0 (t, x) with hGam
  have hScomp : IsCompact S := isCompact_concBall x0 hR.le
  have hSmeas : MeasurableSet S := measurableSet_concBall x0 hR.le
  have hGamcont : Continuous Gam :=
    (continuous_torusGauss (kap * R ^ 2) x0).comp (continuous_const.prodMk continuous_id)
  have hqc : Continuous q := hq.continuous
  have hdqc : Continuous (fun x => fderiv ℝ q x) := hq.continuous_fderiv (by norm_num)
  have hcarrd : Continuous (fun x => fderiv ℝ (psi.carrier q) x) :=
    (psi.carrier_contDiff hq).continuous_fderiv (by norm_num)
  -- restrict to the ball
  have hzero : ∀ x ∉ S, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2 = 0 := by
    intro x hx
    rw [psi.carrier_fderiv_zero_outside hR.le q hx]; simp
  have hrestrict : (∫ x, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2)
      = ∫ x in S, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2 :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  -- the pointwise bound, integrated
  set F : E3 → ℝ := fun x => ‖fderiv ℝ q x‖ ^ 2 + L ^ 2 * (q x) ^ 2 with hF
  have hFcont : Continuous F := by
    have := (hdqc.norm.pow 2)
    exact this.add (continuous_const.mul (hqc.pow 2))
  have hintL : IntegrableOn (fun x => ‖fderiv ℝ (psi.carrier q) x‖ ^ 2) S volume :=
    (hcarrd.norm.pow 2).continuousOn.integrableOn_compact hScomp
  have hintF : IntegrableOn (fun x => 2 * F x) S volume :=
    (continuous_const.mul hFcont).continuousOn.integrableOn_compact hScomp
  have hstep1 : (∫ x in S, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2) ≤ ∫ x in S, 2 * F x := by
    refine setIntegral_mono_on hintL hintF hSmeas fun x _ => ?_
    exact psi.carrier_fderiv_sq_le hq x
  -- unweight
  have hFint : IntegrableOn F S volume := hFcont.continuousOn.integrableOn_compact hScomp
  have hFw : IntegrableOn (fun x => Gam x * F x) S volume :=
    (hGamcont.mul hFcont).continuousOn.integrableOn_compact hScomp
  have hF0 : ∀ x ∈ S, 0 ≤ F x := by
    intro x _
    have : (0:ℝ) ≤ L ^ 2 * (q x) ^ 2 := by positivity
    have h2 : (0:ℝ) ≤ ‖fderiv ℝ q x‖ ^ 2 := sq_nonneg _
    linarith
  have hunw := setIntegral_le_gaussianWeighted_scaleInvariant hkap hR x0 t hSmeas
    (f := F) hF0 (fun x hx => hx) hFint hFw
  -- split the weighted integral
  have hsplit : (∫ x in S, Gam x * F x)
      = (∫ x in S, Gam x * ‖fderiv ℝ q x‖ ^ 2) + L ^ 2 * ∫ x in S, Gam x * (q x) ^ 2 := by
    have h1 : IntegrableOn (fun x => Gam x * ‖fderiv ℝ q x‖ ^ 2) S volume :=
      (hGamcont.mul (hdqc.norm.pow 2)).continuousOn.integrableOn_compact hScomp
    have h2 : IntegrableOn (fun x => Gam x * (q x) ^ 2) S volume :=
      (hGamcont.mul (hqc.pow 2)).continuousOn.integrableOn_compact hScomp
    have hpt : ∀ x, Gam x * F x
        = Gam x * ‖fderiv ℝ q x‖ ^ 2 + L ^ 2 * (Gam x * (q x) ^ 2) := by
      intro x; simp only [hF]; ring
    rw [setIntegral_congr_fun hSmeas (fun x _ => hpt x),
      integral_add h1 (h2.const_mul _), integral_const_mul]
  have hconst : (0:ℝ) ≤ Real.exp (1 / (4 * kap)) := (Real.exp_pos _).le
  rw [hrestrict]
  calc (∫ x in S, ‖fderiv ℝ (psi.carrier q) x‖ ^ 2)
      ≤ ∫ x in S, 2 * F x := hstep1
    _ = 2 * ∫ x in S, F x := by rw [integral_const_mul]
    _ ≤ 2 * (Real.exp (1 / (4 * kap)) * ∫ x in S, Gam x * F x) := by
        exact mul_le_mul_of_nonneg_left hunw (by norm_num)
    _ = 2 * Real.exp (1 / (4 * kap))
          * ((∫ x in S, Gam x * ‖fderiv ℝ q x‖ ^ 2)
              + L ^ 2 * ∫ x in S, Gam x * (q x) ^ 2) := by rw [hsplit]; ring

/-! ## The bridge to the parabolic embedding -/

/-- **The compact-support carrier bridge.**  Given

* a sup-in-time bound `Mw` for the Gaussian-weighted mass on the concentration
  ball,
* a bound `Dw` for the time-integrated Gaussian-weighted dissipation there,

the compactly supported carrier `ψ·q` obeys the parabolic `L^{10/3}` gain with

  `K = 2e^{1/(4κ)}·(Mw + Dw + L²(b−a)Mw)`.

All constants depend only on `(κ, R, L, b−a)`: the level of the truncation
enters only through `Mw` and `Dw`, which is exactly what the De Giorgi
iteration requires. -/
theorem compactCarrier_parabolic_gain (hkap : 0 < kap) (hR : 0 < R) (x0 : E3)
    (psi : BallCutoff x0 R) {a b Mw Dw : ℝ} (hab : a ≤ b) (hMw : 0 ≤ Mw) (hDw : 0 ≤ Dw)
    {q : ℝ → E3 → ℝ} (hq : ∀ t, ContDiff ℝ 1 (q t))
    (hmass : ∀ t ∈ Icc a b,
      (∫ x in concBall x0 R, torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ Mw)
    (hdiss : (∫ t in a..b, ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2) ≤ Dw)
    (hintM : IntervalIntegrable (fun t => ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) volume a b)
    (hintD : IntervalIntegrable (fun t => ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2) volume a b)
    (hint1 : IntervalIntegrable
      (fun t => ∫ x, |psi.carrier (q t) x| ^ (10 / 3 : ℝ)) volume a b)
    (hint2 : IntervalIntegrable
      (fun t => ∫ x, ‖fderiv ℝ (psi.carrier (q t)) x‖ ^ 2) volume a b) :
    (∫ t in a..b, ∫ x, |psi.carrier (q t) x| ^ (10 / 3 : ℝ))
      ≤ sobolevConstE3 ^ 2
        * (2 * Real.exp (1 / (4 * kap))
            * (Mw + Dw + psi.gradBound ^ 2 * (b - a) * Mw)) ^ (5 / 3 : ℝ) := by
  set L := psi.gradBound with hL
  set e1 := Real.exp (1 / (4 * kap)) with he1
  set K := 2 * e1 * (Mw + Dw + L ^ 2 * (b - a) * Mw) with hK
  have he1pos : 0 < e1 := Real.exp_pos _
  have he1ge : 1 ≤ e1 := Real.one_le_exp (by positivity)
  have hL0 : 0 ≤ L := psi.gradBound_nonneg
  have hba : 0 ≤ b - a := by linarith
  have hK0 : 0 ≤ K := by
    have : 0 ≤ Mw + Dw + L ^ 2 * (b - a) * Mw := by positivity
    positivity
  -- slot one
  have hSup : ∀ t ∈ Icc a b, (∫ x, (psi.carrier (q t) x) ^ 2) ≤ K := by
    intro t ht
    have h1 := cutoff_mass_le_weighted hkap hR x0 t psi (hq t).continuous
    have h2 : (∫ x in concBall x0 R, torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ Mw :=
      hmass t ht
    have h3 : e1 * (∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ e1 * Mw :=
      mul_le_mul_of_nonneg_left h2 he1pos.le
    have hKge : e1 * Mw ≤ K := by
      have hterm : 0 ≤ L ^ 2 * (b - a) * Mw := by positivity
      have : e1 * Mw ≤ 2 * e1 * Mw := by nlinarith [mul_nonneg he1pos.le hMw]
      have h4 : 2 * e1 * Mw ≤ K := by
        rw [hK]
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he1pos.le) hDw,
          mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) he1pos.le) hterm]
      linarith
    linarith [h1, h3, hKge]
  -- slot two
  have hpt : ∀ t ∈ Icc a b, (∫ x, ‖fderiv ℝ (psi.carrier (q t)) x‖ ^ 2)
      ≤ 2 * e1 * ((∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
          + L ^ 2 * ∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) := by
    intro t _
    exact cutoff_dissipation_le_weighted hkap hR x0 t psi (hq t)
  have hDiss : (∫ t in a..b, ∫ x, ‖fderiv ℝ (psi.carrier (q t)) x‖ ^ 2) ≤ K := by
    have hmajint : IntervalIntegrable (fun t => 2 * e1 * ((∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
      + L ^ 2 * ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2)) volume a b :=
      ((hintD.add (hintM.const_mul _)).const_mul _)
    have hmono := intervalIntegral.integral_mono_on hab hint2 hmajint hpt
    have hval : (∫ t in a..b, 2 * e1 * ((∫ x in concBall x0 R,
          torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
        + L ^ 2 * ∫ x in concBall x0 R,
          torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2))
        = 2 * e1 * ((∫ t in a..b, ∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
          + L ^ 2 * ∫ t in a..b, ∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hintD
        (hintM.const_mul _), intervalIntegral.integral_const_mul]
    rw [hval] at hmono
    -- the mass term integrates to at most `(b−a)·Mw`
    have hmassint : (∫ t in a..b, ∫ x in concBall x0 R,
        torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ (b - a) * Mw := by
      have := intervalIntegral.integral_mono_on hab hintM
        (intervalIntegrable_const (c := Mw)) hmass
      simpa [mul_comm] using this
    have hfin : 2 * e1 * ((∫ t in a..b, ∫ x in concBall x0 R,
          torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
        + L ^ 2 * ∫ t in a..b, ∫ x in concBall x0 R,
          torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2) ≤ K := by
      have hcoef : (0:ℝ) ≤ 2 * e1 := by positivity
      have hsum : (∫ t in a..b, ∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
          + L ^ 2 * ∫ t in a..b, ∫ x in concBall x0 R,
            torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2
          ≤ Mw + Dw + L ^ 2 * (b - a) * Mw := by
        have hL2 : (0:ℝ) ≤ L ^ 2 := sq_nonneg _
        nlinarith [hdiss, hmassint, hMw]
      calc 2 * e1 * ((∫ t in a..b, ∫ x in concBall x0 R,
              torusGauss (kap * R ^ 2) x0 (t, x) * ‖fderiv ℝ (q t) x‖ ^ 2)
            + L ^ 2 * ∫ t in a..b, ∫ x in concBall x0 R,
              torusGauss (kap * R ^ 2) x0 (t, x) * (q t x) ^ 2)
          ≤ 2 * e1 * (Mw + Dw + L ^ 2 * (b - a) * Mw) :=
            mul_le_mul_of_nonneg_left hsum hcoef
        _ = K := by rw [hK]
    linarith [hmono, hfin]
  exact parabolic_gain_of_caccioppoli (fun t => psi.carrier (q t)) hab hK0
    (fun t => psi.carrier_contDiff (hq t))
    (fun t => psi.carrier_hasCompactSupport hR.le (q t)) hSup hDiss hint1 hint2

end ClayNS

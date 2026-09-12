/-
# Pressure gauge invariance of the localized Kármán–Howarth error

`RequestProject/NavierStokes/KarmanHowarth.lean` proves the localized
Kármán–Howarth identity, and `KarmanHowarthCutoffError.lean` bounds its error
term `E = E_cutoff + E_pressure` by `6·G·K_F + 2|ν|·K_q·H + 6·G·K_q·K_w`, where
`K_F` bounds the increment flux `F = q·u(·+h) + δ_h p·δ_h u`.

That bound asks for a uniform *pointwise* bound on the pressure increment
`δ_h p`.  For a merely bounded velocity this is not available: the pressure is
only controlled at Calderón–Zygmund/BMO level.  This file removes the
requirement.

The observation is that the pressure enters the error only through the pairing
`∫ ∇Φ·(δ_h p · δ_h u)`, and that the increment `δ_h u` is divergence free
(`ClayNS.divg_incrVec`).  Hence for **every** constant `c`

`∫ ∇Φ·(c · δ_h u) = ∫ div(cΦ δ_h u) = 0`,

so `δ_h p` may be replaced by `δ_h p − c` at no cost — in particular by
`δ_h p − (δ_h p)_{supp ∇Φ}`, an annular mean.  Results:

* `ClayNS.cellInt_gradPhi_dot_incr_eq_zero` — the cancellation itself.
* `ClayNS.incrFluxGauge` — the gauge-fixed increment flux, and
  `ClayNS.wCutoffFlux_gauge` — the flux error is unchanged by the gauge.
* `ClayNS.abs_khError_le_gauge` — the error bound in which the pressure enters
  only through the gauge-fixed flux, i.e. only through the *oscillation* of
  `δ_h p` on the support of `∇Φ`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.KarmanHowarthCutoffError

open scoped BigOperators

noncomputable section

namespace ClayNS

/-! ## The divergence-free cancellation -/

/-- **The increment pairs to zero against a cutoff gradient.**  Since
`δ_h u` is divergence free and `Φ δ_h u` is periodic,
`∫_cell ∇Φ·δ_h u = ∫_cell div(Φ δ_h u) = 0`. -/
theorem cellInt_gradPhi_dot_incr_eq_zero {V : STime → E3} {Phi : STime → ℝ} (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    cellInt (fun x => ∑ i, dvec (0, ee i) Phi (t, x) * incrComp h V i (t, x)) = 0 := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (incrVec h V) := contDiff_incrVec h hV
  have hC : ContDiff ℝ (⊤ : ℕ∞) fun w : STime => Phi w • incrVec h V w := hPhi.smul hG
  have hper : SpacePeriodic fun w : STime => Phi w • incrVec h V w := by
    intro z j
    show Phi (z.1, z.2 + ee j) • incrVec h V (z.1, z.2 + ee j) = Phi z • incrVec h V z
    rw [hPhiper z j, spacePeriodic_incrVec h hVper z j]
  have hpt : ∀ x : E3, divg (fun w : STime => Phi w • incrVec h V w) (t, x)
      = ∑ i, dvec (0, ee i) Phi (t, x) * incrComp h V i (t, x) := by
    intro x
    rw [divg_smul Phi (incrVec h V) hPhi hG (t, x), divg_incrVec h hV hdiv (t, x), mul_zero,
      add_zero]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hzero := cellInt_divg_eq_zero _ hC hper t
  rwa [cellInt_congr hpt] at hzero

/-! ## The gauge-fixed increment flux -/

/-- The increment energy flux with the pressure increment shifted by a constant
`c`: `F_c = q·u(·+h) + (δ_h p − c)·δ_h u`.  The constant is the free gauge; the
intended choice is the mean of `δ_h p` over the support of `∇Φ`. -/
def incrFluxGauge (c : ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ) : STime → E3 :=
  fun z => incrQuad h V z • shift h V z + (incrPres h P z - c) • incrVec h V z

lemma contDiff_incrFluxGauge {V : STime → E3} {P : STime → ℝ} (c : ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P) :
    ContDiff ℝ (⊤ : ℕ∞) (incrFluxGauge c h V P) :=
  ((contDiff_incrQuad h hV).smul (contDiff_shift h hV)).add
    (((contDiff_incrPres h hP).sub contDiff_const).smul (contDiff_incrVec h hV))

lemma incrFlux_eq_gauge_add (c : ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ) (z : STime)
    (i : Fin 3) :
    incrFlux h V P z i = incrFluxGauge c h V P z i + c * incrComp h V i z := by
  simp only [incrFlux, incrFluxGauge, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    incrVec_coord]
  ring

/-- **Pressure gauge invariance of the flux error.**  For every constant `c`,
the cutoff flux error `∫ ∇Φ·F` is unchanged when the pressure increment is
replaced by `δ_h p − c`. -/
theorem wCutoffFlux_gauge {V : STime → E3} {P Phi : STime → ℝ} (c : ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0) (t : ℝ) :
    wCutoffFlux Phi h V P t
      = cellInt fun x => ∑ i, dvec (0, ee i) Phi (t, x) * incrFluxGauge c h V P (t, x) i := by
  have hsplit : ∀ x : E3,
      (∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i)
        = (∑ i, dvec (0, ee i) Phi (t, x) * incrFluxGauge c h V P (t, x) i)
          + c * ∑ i, dvec (0, ee i) Phi (t, x) * incrComp h V i (t, x) := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [incrFlux_eq_gauge_add c h V P (t, x) i]; ring
  have cg : Continuous fun x : E3 =>
      ∑ i, dvec (0, ee i) Phi (t, x) * incrFluxGauge c h V P (t, x) i :=
    continuous_finset_sum _ fun i _ =>
      (continuous_slice (contDiff_dvec Phi hPhi (0, ee i)) t).mul
        (continuous_slice (contDiff_coord _ (contDiff_incrFluxGauge c h hV hP) i) t)
  have cw : Continuous fun x : E3 =>
      c * ∑ i, dvec (0, ee i) Phi (t, x) * incrComp h V i (t, x) :=
    continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (continuous_slice (contDiff_dvec Phi hPhi (0, ee i)) t).mul
        (continuous_slice (contDiff_incrComp h hV i) t))
  rw [wCutoffFlux, cellInt_congr hsplit, cellInt_add cg cw, cellInt_const_mul,
    cellInt_gradPhi_dot_incr_eq_zero h hV hPhi hVper hPhiper hdiv t]
  ring

/-- The flux error is bounded by any pointwise bound on the *gauge-fixed*
integrand.  Only the oscillation of `δ_h p` where `∇Φ ≠ 0` can matter. -/
theorem abs_wCutoffFlux_le_gauge {V : STime → E3} {P Phi : STime → ℝ} {Gf : ℝ} (c : ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hGf : ∀ (z : STime) (i : Fin 3), |dvec (0, ee i) Phi z * incrFluxGauge c h V P z i| ≤ Gf)
    (t : ℝ) : |wCutoffFlux Phi h V P t| ≤ 3 * Gf := by
  have cg : Continuous fun x : E3 =>
      ∑ i, dvec (0, ee i) Phi (t, x) * incrFluxGauge c h V P (t, x) i :=
    continuous_finset_sum _ fun i _ =>
      (continuous_slice (contDiff_dvec Phi hPhi (0, ee i)) t).mul
        (continuous_slice (contDiff_coord _ (contDiff_incrFluxGauge c h hV hP) i) t)
  rw [wCutoffFlux_gauge c h hV hP hPhi hVper hPhiper hdiv t]
  refine cellInt_abs_le cg fun x => ?_
  calc |∑ i, dvec (0, ee i) Phi (t, x) * incrFluxGauge c h V P (t, x) i|
      ≤ ∑ i : Fin 3, Gf := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hGf (t, x) i)
    _ = 3 * Gf := by simp [mul_comm]

/-- **The cutoff error bound with the pressure in gauge-fixed form.**  Compared
with `ClayNS.abs_khError_le`, no bound on `δ_h p` itself is required: the
pressure enters only through the gauge-fixed flux `F_c`, hence only through the
oscillation of `δ_h p` on the support of `∇Φ`, and the gauge constant `c` is
free. -/
theorem abs_khError_le_gauge {nu G H Gf Kq Kw : ℝ} {V : STime → E3} {P Phi : STime → ℝ} {h : E3}
    (c : ℝ) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hVper : SpacePeriodic V) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hG : ∀ (z : STime) (i : Fin 3), |dvec (0, ee i) Phi z| ≤ G)
    (hH : ∀ z : STime, |lap Phi z| ≤ H)
    (hGf : ∀ (z : STime) (i : Fin 3), |dvec (0, ee i) Phi z * incrFluxGauge c h V P z i| ≤ Gf)
    (hKq : ∀ z : STime, |incrQuad h V z| ≤ Kq)
    (hKw : ∀ (z : STime) (j : Fin 3), |incrComp h V j z| ≤ Kw)
    (t : ℝ) :
    |khError nu Phi h V P t| ≤ 6 * Gf + 2 * (|nu| * (Kq * H)) + 6 * (G * (Kq * Kw)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  have b1 : |wCutoffFlux Phi h V P t| ≤ 3 * Gf :=
    abs_wCutoffFlux_le_gauge c h hV hP hPhi hVper hPhiper hdiv hGf t
  have c2 : Continuous fun x : E3 => nu * incrQuad h V (t, x) * lap Phi (t, x) :=
    (continuous_const.mul (continuous_slice hq t)).mul
      (continuous_slice (contDiff_lapFun hPhi) t)
  have b2 : |wCutoffLap nu Phi h V t| ≤ |nu| * (Kq * H) := by
    refine cellInt_abs_le c2 fun x => ?_
    rw [mul_assoc, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg nu)
    rw [abs_mul]
    exact mul_le_mul (hKq (t, x)) (hH (t, x)) (abs_nonneg _)
      ((abs_nonneg _).trans (hKq (t, x)))
  have c3 : Continuous fun x : E3 =>
      incrQuad h V (t, x) * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) Phi (t, x) :=
    (continuous_slice hq t).mul (continuous_finset_sum _ fun j _ =>
      (continuous_slice (contDiff_incrComp h hV j) t).mul
        (continuous_slice (contDiff_dvec Phi hPhi (0, ee j)) t))
  have b3 : |wCutoffTransport Phi h V t| ≤ Kq * (3 * (Kw * G)) := by
    refine cellInt_abs_le c3 fun x => ?_
    rw [abs_mul]
    exact mul_le_mul (hKq (t, x))
      (abs_sum_three_mul_le (fun j => hKw (t, x) j) (fun j => hG (t, x) j))
      (abs_nonneg _) ((abs_nonneg _).trans (hKq (t, x)))
  have key : |khError nu Phi h V P t|
      ≤ 2 * |wCutoffFlux Phi h V P t| + 2 * |wCutoffLap nu Phi h V t|
        + 2 * |wCutoffTransport Phi h V t| := by
    simp only [khError]
    have h1 := abs_add_le (2 * wCutoffFlux Phi h V P t) (2 * wCutoffLap nu Phi h V t)
    have h2 : |2 * wCutoffFlux Phi h V P t + 2 * wCutoffLap nu Phi h V t
          - 2 * wCutoffTransport Phi h V t|
        ≤ |2 * wCutoffFlux Phi h V P t + 2 * wCutoffLap nu Phi h V t|
          + |2 * wCutoffTransport Phi h V t| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add_le (2 * wCutoffFlux Phi h V P t + 2 * wCutoffLap nu Phi h V t)
          (-(2 * wCutoffTransport Phi h V t))
    have e1 : |2 * wCutoffFlux Phi h V P t| = 2 * |wCutoffFlux Phi h V P t| := by
      rw [abs_mul]; norm_num
    have e2 : |2 * wCutoffLap nu Phi h V t| = 2 * |wCutoffLap nu Phi h V t| := by
      rw [abs_mul]; norm_num
    have e3 : |2 * wCutoffTransport Phi h V t| = 2 * |wCutoffTransport Phi h V t| := by
      rw [abs_mul]; norm_num
    linarith [h1, h2, e1, e2, e3]
  linarith [key, b1, b2, b3]

end ClayNS

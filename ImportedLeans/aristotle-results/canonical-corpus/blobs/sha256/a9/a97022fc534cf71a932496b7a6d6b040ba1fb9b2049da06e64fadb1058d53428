/-
# The cutoff error in the localized Kármán–Howarth identity

`RequestProject/NavierStokes/KarmanHowarth.lean` proves the exact identity

`∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + E`,   `E = E_cutoff + E_pressure`,

with

`E = 2∫∇Φ·F + 2ν∫qΔΦ − 2∫q(δ_h u·∇Φ)`,  `F = q u(·+h) + δ_h p δ_h u`.

This file isolates `E` as a single quantity `ClayNS.khError` and proves the two
facts one needs in order to run the intermediate-scale argument
`1 ≪ R_k ≪ M_k`:

* `ClayNS.abs_khError_le` — a completely explicit bound
  `|E| ≤ 6·G·K_F + 2|ν|·K_q·H + 6·G·K_q·K_w`, where `G` bounds `|∇Φ|`, `H`
  bounds `|ΔΦ|`, and `K_F, K_q, K_w` bound the increment flux, the increment
  energy density and the increment itself.  Consequently a cutoff family whose
  first and second derivatives tend to zero uniformly, evaluated on fields with
  uniformly bounded increments, flux and pressure increment, has vanishing
  cutoff error: this is exactly the criterion `E_cutoff + E_pressure → 0`.
* `ClayNS.karman_howarth_torus` — the limiting case `Φ ≡ 1`, i.e. the exact
  homogeneous Kármán–Howarth–Monin equation on the periodicity cell,
  `∂_t S₂ + ∇_h·F₃ = −2ν∫|∇_x δ_h u|²`, with no error at all.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.KarmanHowarth

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace ClayNS

/-! ## Two elementary facts about the cell integral -/

/-- A uniform pointwise bound gives the same bound on the cell average. -/
lemma cellInt_abs_le {f : E3 → ℝ} (hf : Continuous f) {C : ℝ} (h : ∀ x, |f x| ≤ C) :
    |cellInt f| ≤ C := by
  have hup : cellInt f ≤ C := by
    have := cellInt_mono hf continuous_const fun x => (le_abs_self (f x)).trans (h x)
    rwa [cellInt_const] at this
  have hlo : -C ≤ cellInt f := by
    have := cellInt_mono continuous_const hf fun x => neg_le_of_abs_le (h x)
    rwa [cellInt_const] at this
  exact abs_le.mpr ⟨hlo, hup⟩

/-- A sum of three products of bounded factors. -/
lemma abs_sum_three_mul_le {a b : Fin 3 → ℝ} {G K : ℝ} (ha : ∀ i, |a i| ≤ G)
    (hb : ∀ i, |b i| ≤ K) : |∑ i, a i * b i| ≤ 3 * (G * K) := by
  have hstep : |∑ i, a i * b i| ≤ ∑ _i : Fin 3, G * K := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (ha i) (hb i) (abs_nonneg _) ((abs_nonneg _).trans (ha i))
  simpa using hstep

/-! ## The total cutoff error -/

/-- The total error term of the localized Kármán–Howarth identity:
`E = 2∫∇Φ·F + 2ν∫qΔΦ − 2∫q(δ_h u·∇Φ)`.  Every summand carries a derivative of
the cutoff `Φ`. -/
def khError (nu : ℝ) (Phi : STime → ℝ) (h : E3) (V : STime → E3) (P : STime → ℝ) (t : ℝ) : ℝ :=
  2 * wCutoffFlux Phi h V P t + 2 * wCutoffLap nu Phi h V t - 2 * wCutoffTransport Phi h V t

/-- **The localized Kármán–Howarth identity, in error form**:
`∂_t S₂ + ∇_h·F₃ = −2ν∫Φ|∇_x δ_h u|² + E`. -/
theorem localized_karman_howarth_error_form (nu : ℝ) (V : STime → E3) (P Phi : STime → ℝ)
    (h : E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi) (hPhiT : ∀ z : STime, dvec (1, 0) Phi z = 0)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P) (hPhiper : SpacePeriodic Phi)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (fun r : ℝ => strFun Phi V r h)
      ((- (2 * wDissip nu Phi h V t) + khError nu Phi h V P t) - strFluxDivH Phi V t h) t := by
  have hbase := localized_karman_howarth nu V P Phi h hV hP hPhi hPhiT hVper hPper hPhiper
    hdiv hmom t
  have hval : (- (2 * wDissip nu Phi h V t) + khError nu Phi h V P t)
      - strFluxDivH Phi V t h
      = (- (2 * wDissip nu Phi h V t) + 2 * wCutoffFlux Phi h V P t
          + 2 * wCutoffLap nu Phi h V t - 2 * wCutoffTransport Phi h V t)
        - strFluxDivH Phi V t h := by
    simp only [khError]; ring
  rw [hval]
  exact hbase

/-- **The cutoff error is controlled by the derivatives of the cutoff.**

If `|∂_iΦ| ≤ G` and `|ΔΦ| ≤ H` pointwise, and if the increment flux, the
increment energy density and the increment itself are bounded by `Kf`, `Kq` and
`Kw`, then

`|E| ≤ 6·G·Kf + 2|ν|·Kq·H + 6·G·Kq·Kw`.

Hence for a family of cutoffs with `G, H → 0` — a cutoff spread over a scale
`R → ∞` — evaluated on a family of fields with uniformly bounded increments,
increment flux and increment pressure, the cutoff error vanishes.  This is the
quantitative form of the requirement `E_cutoff + E_pressure → 0` on an
intermediate scale. -/
theorem abs_khError_le {nu G H Kf Kq Kw : ℝ} {V : STime → E3} {P Phi : STime → ℝ} {h : E3}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hPhi : ContDiff ℝ (⊤ : ℕ∞) Phi)
    (hG : ∀ (z : STime) (i : Fin 3), |dvec (0, ee i) Phi z| ≤ G)
    (hH : ∀ z : STime, |lap Phi z| ≤ H)
    (hKf : ∀ (z : STime) (i : Fin 3), |incrFlux h V P z i| ≤ Kf)
    (hKq : ∀ z : STime, |incrQuad h V z| ≤ Kq)
    (hKw : ∀ (z : STime) (j : Fin 3), |incrComp h V j z| ≤ Kw)
    (t : ℝ) :
    |khError nu Phi h V P t| ≤ 6 * (G * Kf) + 2 * (|nu| * (Kq * H)) + 6 * (G * (Kq * Kw)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) (incrQuad h V) := contDiff_incrQuad h hV
  -- the flux error
  have c1 : Continuous fun x : E3 => ∑ i, dvec (0, ee i) Phi (t, x) * incrFlux h V P (t, x) i :=
    continuous_finset_sum _ fun i _ =>
      (continuous_slice (contDiff_dvec Phi hPhi (0, ee i)) t).mul
        (continuous_slice (contDiff_coord _ (contDiff_incrFlux h hV hP) i) t)
  have b1 : |wCutoffFlux Phi h V P t| ≤ 3 * (G * Kf) :=
    cellInt_abs_le c1 fun x =>
      abs_sum_three_mul_le (fun i => hG (t, x) i) (fun i => hKf (t, x) i)
  -- the viscous error
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
  -- the transport error
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

/-! ## The homogeneous case: the Kármán–Howarth–Monin equation on the cell -/

@[simp] lemma dvec_const_fun (c : ℝ) (a z : STime) : dvec a (fun _ : STime => c) z = 0 := by
  simp [dvec]

@[simp] lemma lap_const_fun (c : ℝ) (z : STime) : lap (fun _ : STime => c) z = 0 := by
  simp [lap, dspace]

lemma wCutoffFlux_const (h : E3) (V : STime → E3) (P : STime → ℝ) (t : ℝ) :
    wCutoffFlux (fun _ => 1) h V P t = 0 := by
  have : ∀ x : E3,
      (∑ i, dvec (0, ee i) (fun _ : STime => (1 : ℝ)) (t, x) * incrFlux h V P (t, x) i)
        = (0 : ℝ) := by
    intro x; simp
  rw [wCutoffFlux, cellInt_congr this, cellInt_const]

lemma wCutoffLap_const (nu : ℝ) (h : E3) (V : STime → E3) (t : ℝ) :
    wCutoffLap nu (fun _ => 1) h V t = 0 := by
  have : ∀ x : E3,
      nu * incrQuad h V (t, x) * lap (fun _ : STime => (1 : ℝ)) (t, x) = (0 : ℝ) := by
    intro x; simp
  rw [wCutoffLap, cellInt_congr this, cellInt_const]

lemma wCutoffTransport_const (h : E3) (V : STime → E3) (t : ℝ) :
    wCutoffTransport (fun _ => 1) h V t = 0 := by
  have : ∀ x : E3, incrQuad h V (t, x)
      * ∑ j, incrComp h V j (t, x) * dvec (0, ee j) (fun _ : STime => (1 : ℝ)) (t, x)
        = (0 : ℝ) := by
    intro x; simp
  rw [wCutoffTransport, cellInt_congr this, cellInt_const]

/-- **The Kármán–Howarth–Monin equation on the periodicity cell.**  With the
trivial cutoff `Φ ≡ 1` the error term disappears completely and the localized
identity becomes the exact homogeneous relation

`∂_t S₂ + ∇_h·F₃ = −2ν∫|∇_x δ_h u|²`.

The pressure has cancelled outright, and the only remaining term is the
manifestly nonpositive increment dissipation. -/
theorem karman_howarth_torus (nu : ℝ) (V : STime → E3) (P : STime → ℝ) (h : E3)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hPper : SpacePeriodic P)
    (hdiv : ∀ z : STime, divg V z = 0)
    (hmom : ∀ z : STime, dtime V z + adv V z = - grad P z + nu • lap V z)
    (t : ℝ) :
    HasDerivAt (fun r : ℝ => strFun (fun _ => 1) V r h)
      (- (2 * wDissip nu (fun _ => 1) h V t) - strFluxDivH (fun _ => 1) V t h) t := by
  have hPhi : ContDiff ℝ (⊤ : ℕ∞) fun _ : STime => (1 : ℝ) := contDiff_const
  have hPhiT : ∀ z : STime, dvec (1, 0) (fun _ : STime => (1 : ℝ)) z = 0 := fun z => by simp
  have hPhiper : SpacePeriodic fun _ : STime => (1 : ℝ) := fun _ _ => rfl
  have hbase := localized_karman_howarth nu V P (fun _ => 1) h hV hP hPhi hPhiT hVper hPper
    hPhiper hdiv hmom t
  rw [wCutoffFlux_const, wCutoffLap_const, wCutoffTransport_const] at hbase
  simpa using hbase

end ClayNS

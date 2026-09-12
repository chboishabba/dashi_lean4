/-
# A derived continuation estimate: Grönwall control of the enstrophy by the
# velocity gradient.

The Beale–Kato–Majda / Serrin continuation step of the Clay ladder asserts that
a solution stays smooth as long as a suitable norm of the vorticity or of the
velocity gradient stays finite.  In the Agda development this step is opaque
record data.  Here the analytic core of the estimate is derived from the global
enstrophy balance of `RequestProject/NavierStokes/GlobalEnergy.lean`:

* `ClayNS.stretching_bound` — the algebraic bound
  `∑_a ω_a (ω·∇)u_a ≤ 3 M |ω|²` when every component of `∇u` is bounded by `M`;
* `ClayNS.enstrophy_production_le` — its integrated form on the torus;
* `ClayNS.enstrophy_gronwall` — the Grönwall conclusion
  `∫_cell ½|ω(t)|² ≤ (∫_cell ½|ω(0)|²) · e^{6Mt}` for `t ≥ 0`.

This is a genuine conditional continuation bound: a uniform bound on the
velocity gradient forbids enstrophy blow-up.  It does *not* close the Clay
target, which needs the reverse implication (control of `∇u` from the data).

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GlobalEnergy

open scoped BigOperators
open MeasureTheory Set

noncomputable section

namespace ClayNS

/-! ## The algebraic vortex-stretching bound -/

/-- If every entry of the matrix `D` is bounded by `M` in absolute value, the
stretching form `∑_a w_a ∑_j w_j D_{ja}` is bounded by `3 M |w|²`. -/
lemma stretching_bound (M : ℝ) (w : Fin 3 → ℝ) (D : Fin 3 → Fin 3 → ℝ)
    (hD : ∀ j a, |D j a| ≤ M) :
    ∑ a, w a * ∑ j, w j * D j a ≤ 3 * M * ∑ a, w a * w a := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hD 0 0)
  have hterm : ∀ a j : Fin 3, w a * (w j * D j a) ≤ M * ((w a * w a + w j * w j) / 2) := by
    intro a j
    have habs : |w a * w j| ≤ (w a * w a + w j * w j) / 2 := by
      nlinarith [sq_nonneg (|w a| - |w j|), abs_mul (w a) (w j), sq_abs (w a), sq_abs (w j),
        abs_nonneg (w a), abs_nonneg (w j)]
    have h1 : w a * (w j * D j a) ≤ |w a * w j| * M := by
      have hrw : w a * (w j * D j a) = (w a * w j) * D j a := by ring
      rw [hrw]
      calc (w a * w j) * D j a ≤ |(w a * w j) * D j a| := le_abs_self _
        _ = |w a * w j| * |D j a| := abs_mul _ _
        _ ≤ |w a * w j| * M := mul_le_mul_of_nonneg_left (hD j a) (abs_nonneg _)
    nlinarith [h1, habs, hM0, abs_nonneg (w a * w j)]
  calc ∑ a, w a * ∑ j, w j * D j a = ∑ a, ∑ j, w a * (w j * D j a) :=
        Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
    _ ≤ ∑ a, ∑ j, M * ((w a * w a + w j * w j) / 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ => hterm a j
    _ = 3 * M * ∑ a, w a * w a := by
        simp [Fin.sum_univ_three]; ring

/-! ## The integrated production bound -/

/-- Global vortex-stretching production, the source term of the enstrophy
balance. -/
def production (V : STime → E3) (t : ℝ) : ℝ :=
  cellInt (fun x => ∑ a, vortComp V a (t, x)
    * ∑ j, vortComp V j (t, x) * dvec (0, ee j) (fun w => V w a) (t, x))

lemma continuous_production_slice (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (t : ℝ) :
    Continuous (fun x : E3 => ∑ a, vortComp V a (t, x)
      * ∑ j, vortComp V j (t, x) * dvec (0, ee j) (fun w => V w a) (t, x)) := by
  refine continuous_time_slice (f := fun z : STime => ∑ a, vortComp V a z
      * ∑ j, vortComp V j z * dvec (0, ee j) (fun w => V w a) z) ?_ t
  refine continuous_finset_sum _ fun a _ => (contDiff_vortComp V hV a).continuous.mul ?_
  exact continuous_finset_sum _ fun j _ =>
    (contDiff_vortComp V hV j).continuous.mul
      (continuous_dvec _ (contDiff_coord V hV a) (0, ee j))

/-- **Production bound.**  If every component of `∇u` is bounded by `M`, the
global vortex-stretching production is bounded by `6 M` times the enstrophy. -/
theorem enstrophy_production_le (M : ℝ) (V : STime → E3) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    (t : ℝ) (hM : ∀ (x : E3) (j a : Fin 3), |dvec (0, ee j) (fun w => V w a) (t, x)| ≤ M) :
    production V t ≤ 6 * M * enstrophy V t := by
  have hens : Continuous (fun x : E3 => 6 * M * ens V (t, x)) :=
    continuous_const.mul (continuous_time_slice
      (contDiff_quad (vortComp V) (fun a => contDiff_vortComp V hV a)).continuous t)
  have hpt : ∀ x : E3,
      (∑ a, vortComp V a (t, x)
        * ∑ j, vortComp V j (t, x) * dvec (0, ee j) (fun w => V w a) (t, x))
        ≤ 6 * M * ens V (t, x) := by
    intro x
    have h := stretching_bound M (fun a => vortComp V a (t, x))
      (fun j a => dvec (0, ee j) (fun w => V w a) (t, x)) (fun j a => hM x j a)
    have hq : ens V (t, x) = (1 / 2 : ℝ) * ∑ a, vortComp V a (t, x) * vortComp V a (t, x) := rfl
    rw [hq]
    linarith
  calc production V t
      ≤ cellInt (fun x => 6 * M * ens V (t, x)) :=
        cellInt_mono (continuous_production_slice V hV t) hens hpt
    _ = 6 * M * enstrophy V t := cellInt_const_mul _ _

/-! ## The Grönwall continuation bound -/

/-- **Conditional enstrophy bound.**  If every component of the velocity
gradient stays bounded by `M`, then the cell enstrophy of a smooth periodic
divergence-free solution grows at most like `e^{6Mt}`:

`∫_cell ½|ω(t)|² ≤ (∫_cell ½|ω(0)|²) · e^{6Mt}` for `t ≥ 0`.

In particular enstrophy cannot blow up while `∇u` remains bounded. -/
theorem enstrophy_gronwall (nu M : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (hM : ∀ (z : STime) (j a : Fin 3), |dvec (0, ee j) (fun w => V w a) z| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    enstrophy V t ≤ enstrophy V 0 * Real.exp (6 * M * t) := by
  set D : ℝ → ℝ := fun s => cellInt (fun x => gradSq (vortComp V) (s, x)) with hD
  have hbal : ∀ s : ℝ, HasDerivAt (enstrophy V) (production V s - nu * D s) s :=
    fun s => enstrophy_balance nu V P hV hP hVper hdiv hmom s
  have hDnn : ∀ s : ℝ, 0 ≤ D s := fun s => cellInt_nonneg fun x => gradSq_nonneg _ _
  have hPr : ∀ s : ℝ, production V s ≤ 6 * M * enstrophy V s :=
    fun s => enstrophy_production_le M V hV s fun x j a => hM (s, x) j a
  -- the exponentially damped enstrophy is nonincreasing
  set g : ℝ → ℝ := fun s => enstrophy V s * Real.exp (-(6 * M * s)) with hg
  have hexp : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-(6 * M * r)))
      (Real.exp (-(6 * M * s)) * (-(6 * M))) s := by
    intro s
    have hlin : HasDerivAt (fun r : ℝ => -(6 * M * r)) (-(6 * M)) s := by
      simpa using ((hasDerivAt_id s).const_mul (6 * M)).neg
    exact (Real.hasDerivAt_exp (-(6 * M * s))).comp s hlin
  have hgderiv : ∀ s : ℝ, HasDerivAt g
      ((production V s - nu * D s) * Real.exp (-(6 * M * s))
        + enstrophy V s * (Real.exp (-(6 * M * s)) * (-(6 * M)))) s :=
    fun s => (hbal s).mul (hexp s)
  have hgnonpos : ∀ s : ℝ, deriv g s ≤ 0 := by
    intro s
    rw [(hgderiv s).deriv]
    have hE : 0 < Real.exp (-(6 * M * s)) := Real.exp_pos _
    have hstep : production V s - nu * D s - 6 * M * enstrophy V s ≤ 0 := by
      have := hPr s
      have h2 : 0 ≤ nu * D s := mul_nonneg hnu (hDnn s)
      linarith
    nlinarith [hE, hstep]
  have hganti : Antitone g :=
    antitone_of_deriv_nonpos (fun s => (hgderiv s).differentiableAt) hgnonpos
  have hgt : g t ≤ g 0 := hganti ht
  have hg0 : g 0 = enstrophy V 0 := by simp [hg]
  have hpos : 0 < Real.exp (6 * M * t) := Real.exp_pos _
  have hinv : Real.exp (-(6 * M * t)) * Real.exp (6 * M * t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_right (hgt.trans_eq hg0) hpos.le
  calc enstrophy V t
      = enstrophy V t * Real.exp (-(6 * M * t)) * Real.exp (6 * M * t) := by
        rw [mul_assoc, hinv, mul_one]
    _ ≤ enstrophy V 0 * Real.exp (6 * M * t) := hmul

/-- **Beale–Kato–Majda / Serrin-type continuation bound.**  If the velocity
gradient at time `s` is bounded by `M s` with `M` continuous, then the cell
enstrophy obeys

`∫_cell ½|ω(t)|² ≤ (∫_cell ½|ω(0)|²) · exp (6 ∫₀ᵗ M)`,

so the enstrophy stays finite as long as `∫ ‖∇u‖_∞` does — the time-integrated
form of the continuation criterion. -/
theorem enstrophy_gronwall_integral (nu : ℝ) (V : STime → E3) (P : STime → ℝ)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hP : ContDiff ℝ (⊤ : ℕ∞) P)
    (hVper : SpacePeriodic V) (hnu : 0 ≤ nu)
    (hdiv : ∀ w : STime, divg V w = 0)
    (hmom : ∀ w : STime, dtime V w + adv V w = - grad P w + nu • lap V w)
    (M : ℝ → ℝ) (hMc : Continuous M)
    (hM : ∀ (s : ℝ) (x : E3) (j a : Fin 3),
      |dvec (0, ee j) (fun w => V w a) (s, x)| ≤ M s)
    {t : ℝ} (ht : 0 ≤ t) :
    enstrophy V t ≤ enstrophy V 0 * Real.exp (6 * ∫ s in (0 : ℝ)..t, M s) := by
  set D : ℝ → ℝ := fun s => cellInt (fun x => gradSq (vortComp V) (s, x)) with hD
  have hbal : ∀ s : ℝ, HasDerivAt (enstrophy V) (production V s - nu * D s) s :=
    fun s => enstrophy_balance nu V P hV hP hVper hdiv hmom s
  have hDnn : ∀ s : ℝ, 0 ≤ D s := fun s => cellInt_nonneg fun x => gradSq_nonneg _ _
  have hPr : ∀ s : ℝ, production V s ≤ 6 * M s * enstrophy V s :=
    fun s => enstrophy_production_le (M s) V hV s fun x j a => hM s x j a
  have hEnn : ∀ s : ℝ, 0 ≤ enstrophy V s := fun s => cellInt_nonneg fun x =>
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun a _ => mul_self_nonneg _)
  -- the accumulated gradient bound and its derivative
  set A : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, 6 * M r with hA
  have hAd : ∀ s : ℝ, HasDerivAt A (6 * M s) s := by
    intro s
    have hc : Continuous (fun r : ℝ => 6 * M r) := continuous_const.mul hMc
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hexp : ∀ s : ℝ, HasDerivAt (fun r : ℝ => Real.exp (-(A r)))
      (Real.exp (-(A s)) * (-(6 * M s))) s := by
    intro s
    have hneg : HasDerivAt (fun r : ℝ => -(A r)) (-(6 * M s)) s := (hAd s).neg
    exact (Real.hasDerivAt_exp (-(A s))).comp s hneg
  set g : ℝ → ℝ := fun s => enstrophy V s * Real.exp (-(A s)) with hg
  have hgderiv : ∀ s : ℝ, HasDerivAt g
      ((production V s - nu * D s) * Real.exp (-(A s))
        + enstrophy V s * (Real.exp (-(A s)) * (-(6 * M s)))) s :=
    fun s => (hbal s).mul (hexp s)
  have hgnonpos : ∀ s : ℝ, deriv g s ≤ 0 := by
    intro s
    rw [(hgderiv s).deriv]
    have hE : 0 < Real.exp (-(A s)) := Real.exp_pos _
    have hstep : production V s - nu * D s - 6 * M s * enstrophy V s ≤ 0 := by
      have h1 := hPr s
      have h2 : 0 ≤ nu * D s := mul_nonneg hnu (hDnn s)
      linarith
    nlinarith [hE, hstep]
  have hganti : Antitone g :=
    antitone_of_deriv_nonpos (fun s => (hgderiv s).differentiableAt) hgnonpos
  have hgt : g t ≤ g 0 := hganti ht
  have hA0 : A 0 = 0 := by simp [hA]
  have hg0 : g 0 = enstrophy V 0 := by simp [hg, hA0]
  have hAt : A t = 6 * ∫ s in (0 : ℝ)..t, M s := by
    rw [hA]; exact intervalIntegral.integral_const_mul _ _
  have hpos : 0 < Real.exp (A t) := Real.exp_pos _
  have hinv : Real.exp (-(A t)) * Real.exp (A t) = 1 := by
    rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_right (hgt.trans_eq hg0) hpos.le
  have hfin : enstrophy V t ≤ enstrophy V 0 * Real.exp (A t) := by
    calc enstrophy V t
        = enstrophy V t * Real.exp (-(A t)) * Real.exp (A t) := by
          rw [mul_assoc, hinv, mul_one]
      _ ≤ enstrophy V 0 * Real.exp (A t) := hmul
  rwa [hAt] at hfin

end ClayNS

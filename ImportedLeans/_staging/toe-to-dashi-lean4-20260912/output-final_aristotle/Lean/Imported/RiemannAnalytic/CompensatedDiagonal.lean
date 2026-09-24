/-
**G12 — the compensated anchored kernel on the prime diagonal: exact vanishing,
the near/far split, and the exact size of the gain it produces.**

G11 left the programme with

    `𝒟(α) ≤ 8Λ²α²·𝒜(α)`   (`compensatedMinor_le_twisted_uniform`)

together with two negative theorems: no absolute budget can force `α = 0`
(`absolute_budget_insufficient`) and no *universal* weight-theoretic contraction
factor `η < 1` exists (`no_uniform_twisted_contraction`).  So the remaining gain
has to come from the structure of the anchored kernel on the actual
log-frequency set.

This file isolates that structure exactly, with no asymptotics:

* `minorForm_diag_term_zero`, `minorForm_eq_offDiag` — **exact diagonal
  vanishing**: every diagonal term of the anchored observable is literally `0`,
  because the kernel is evaluated at `λ_n − λ_n = 0`.  This is the second-order
  zero the compensated observable inserts on the prime diagonal, and it is an
  identity, not an estimate.

* `minorForm_le_quadDiffForm`, `quadDiffForm_eq_two_varForm` — the observable is
  dominated by the **second-difference form** `∑ₙ∑ₘ wₙwₘ(λₙ−λₘ)²`, which is
  exactly twice the log-variance `S₀S₂ − S₁²`.

* `minorForm_eq_near_add_far` and the two one-sided bounds
  `nearPart_le_nearMass`, `farPart_le_farMass`, `farPart_le_second_difference`,
  assembled in `minorForm_le_nearFar` — the exact near/far split at a threshold
  `Δ` in the log-frequency difference:

      `𝒜 ≤ (s²Δ²/2)·N(Δ) + 2·F(Δ)`,

  where `N(Δ)`, `F(Δ)` are the near and far pair masses.

* `offLineTarget_excluded_of_nearFar_gain` — the consumer: if the near/far
  budget beats the geometric floor, the off-line displacement is *exactly* zero.

* **The adversarial part (Q12.5), proved, not assumed.**
  `nearPart_twoPoint_ge` shows the near-diagonal bound is sharp up to the factor
  `4`: a two-point configuration at spacing `Δ` realises it.  Hence the gain
  produced by the quadratic diagonal zero is exactly the factor `(sΔ)²` and
  nothing more.  `nearPart_twoPoint_eq_nearMass_of_pi` shows that once
  `sΔ = π` the gain is *zero*: the near part equals the full near mass.
  Consequently `η_prime(T) → 0` cannot follow from the diagonal zero alone; it
  requires `sΔ → 0`, i.e. genuine information about the spacing of the actual
  log-prime frequencies relative to the window scale.

Nothing here mentions `ζ`, and nothing below is assumed anywhere else.
-/
import RiemannAnalytic.TwistedNormalization

namespace RiemannAnalytic

open Finset

variable {d : ℕ}

/-! ### Exact vanishing on the diagonal -/

/-- Every diagonal term of the anchored observable is exactly zero: the kernel
is evaluated at `λ_n − λ_n = 0`. -/
theorem minorForm_diag_term_zero (w lam : Fin d → ℝ) (s : ℝ) (n : Fin d) :
    w n * w n * (1 - Real.cos (s * (lam n - lam n))) = 0 := by
  simp

/-- **Exact diagonal vanishing.**  The anchored observable is a sum over
*off-diagonal* pairs only. -/
theorem minorForm_eq_offDiag (w lam : Fin d → ℝ) (s : ℝ) :
    minorForm w lam s
      = ∑ n, ∑ m ∈ Finset.univ.erase n,
          w n * w m * (1 - Real.cos (s * (lam n - lam m))) := by
  unfold minorForm
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ n), minorForm_diag_term_zero w lam s n,
    sub_zero]

/-! ### The second-difference (log-variance) form -/

/-- The second-difference form `∑ₙ∑ₘ wₙwₘ(λₙ−λₘ)²`: the object the compensated
observable actually sees, with the quadratic zero on the diagonal explicit. -/
noncomputable def quadDiffForm (w lam : Fin d → ℝ) : ℝ :=
  ∑ n, ∑ m, w n * w m * (lam n - lam m) ^ 2

/-- The second-difference form is exactly twice the log-variance
`S₀S₂ − S₁²`. -/
theorem quadDiffForm_eq_two_varForm (w lam : Fin d → ℝ) :
    quadDiffForm w lam = 2 * varForm w lam := by
  unfold quadDiffForm varForm
  have hexp : ∀ n : Fin d, ∑ m, w n * w m * (lam n - lam m) ^ 2
      = (w n * lam n ^ 2) * (∑ m, w m) - 2 * (w n * lam n) * (∑ m, w m * lam m)
        + w n * (∑ m, w m * lam m ^ 2) := by
    intro n
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  rw [Finset.sum_congr rfl fun n _ => hexp n, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The anchored observable is dominated by the second-difference form. -/
theorem minorForm_le_quadDiffForm {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (s : ℝ) :
    minorForm w lam s ≤ s ^ 2 / 2 * quadDiffForm w lam := by
  unfold minorForm quadDiffForm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hk : 1 - Real.cos (s * (lam n - lam m)) ≤ (s * (lam n - lam m)) ^ 2 / 2 :=
    one_sub_cos_le_half_sq _
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  nlinarith [mul_le_mul_of_nonneg_left hk hww]

/-! ### The near/far split -/

/-- The near-diagonal part of the anchored observable: pairs whose
log-frequency difference is at most `Δ`. -/
noncomputable def nearPart (w lam : Fin d → ℝ) (s Delta : ℝ) : ℝ :=
  ∑ n, ∑ m ∈ Finset.univ.filter (fun m => |lam n - lam m| ≤ Delta),
      w n * w m * (1 - Real.cos (s * (lam n - lam m)))

/-- The far-diagonal part of the anchored observable. -/
noncomputable def farPart (w lam : Fin d → ℝ) (s Delta : ℝ) : ℝ :=
  ∑ n, ∑ m ∈ Finset.univ.filter (fun m => ¬ |lam n - lam m| ≤ Delta),
      w n * w m * (1 - Real.cos (s * (lam n - lam m)))

/-- The near-diagonal pair mass. -/
noncomputable def nearMass (w lam : Fin d → ℝ) (Delta : ℝ) : ℝ :=
  ∑ n, ∑ m ∈ Finset.univ.filter (fun m => |lam n - lam m| ≤ Delta), w n * w m

/-- The far-diagonal pair mass. -/
noncomputable def farMass (w lam : Fin d → ℝ) (Delta : ℝ) : ℝ :=
  ∑ n, ∑ m ∈ Finset.univ.filter (fun m => ¬ |lam n - lam m| ≤ Delta), w n * w m

/-- **The exact near/far split.** -/
theorem minorForm_eq_near_add_far (w lam : Fin d → ℝ) (s Delta : ℝ) :
    minorForm w lam s = nearPart w lam s Delta + farPart w lam s Delta := by
  unfold minorForm nearPart farPart
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by
    rw [Finset.sum_filter_add_sum_filter_not]

/-- **The near-diagonal bound.**  On the near region the quadratic diagonal zero
gives the gain factor `(sΔ)²/2` against the near pair mass. -/
theorem nearPart_le_nearMass {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (s Delta : ℝ) :
    nearPart w lam s Delta ≤ s ^ 2 * Delta ^ 2 / 2 * nearMass w lam Delta := by
  unfold nearPart nearMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hclose : |lam n - lam m| ≤ Delta := (Finset.mem_filter.mp hm).2
  have hsq : (lam n - lam m) ^ 2 ≤ Delta ^ 2 := by
    have h0 : 0 ≤ |lam n - lam m| := abs_nonneg _
    nlinarith [sq_abs (lam n - lam m), hclose, h0]
  have hk : 1 - Real.cos (s * (lam n - lam m)) ≤ (s * (lam n - lam m)) ^ 2 / 2 :=
    one_sub_cos_le_half_sq _
  have hkk : 1 - Real.cos (s * (lam n - lam m)) ≤ s ^ 2 * Delta ^ 2 / 2 := by
    have : (s * (lam n - lam m)) ^ 2 ≤ s ^ 2 * Delta ^ 2 := by
      have := sq_nonneg s; nlinarith [hsq]
    linarith
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  nlinarith [mul_le_mul_of_nonneg_left hkk hww]

/-- **The far-diagonal bound.**  The kernel is bounded by `2` there. -/
theorem farPart_le_farMass {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (s Delta : ℝ) :
    farPart w lam s Delta ≤ 2 * farMass w lam Delta := by
  unfold farPart farMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hk : 1 - Real.cos (s * (lam n - lam m)) ≤ 2 := by
    have := Real.neg_one_le_cos (s * (lam n - lam m)); linarith
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  nlinarith [mul_le_mul_of_nonneg_left hk hww]

/-- On the far region the quadratic factor `(λₙ−λₘ)²` is at least `Δ²`, so the
far mass is itself controlled by the second-difference form. -/
theorem farPart_le_second_difference {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n)
    {Delta : ℝ} (hDelta : 0 < Delta) (s : ℝ) :
    farPart w lam s Delta
      ≤ 2 / Delta ^ 2 *
        ∑ n, ∑ m ∈ Finset.univ.filter (fun m => ¬ |lam n - lam m| ≤ Delta),
            w n * w m * (lam n - lam m) ^ 2 := by
  unfold farPart
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m hm => ?_
  have hfar : Delta < |lam n - lam m| := not_le.mp (Finset.mem_filter.mp hm).2
  have hsq : Delta ^ 2 ≤ (lam n - lam m) ^ 2 := by
    nlinarith [sq_abs (lam n - lam m), hDelta, hfar]
  have hk : 1 - Real.cos (s * (lam n - lam m)) ≤ 2 := by
    have := Real.neg_one_le_cos (s * (lam n - lam m)); linarith
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  have hD2 : 0 < Delta ^ 2 := by positivity
  have hstep : 1 - Real.cos (s * (lam n - lam m)) ≤ 2 / Delta ^ 2 * (lam n - lam m) ^ 2 := by
    have h2 : 2 ≤ 2 / Delta ^ 2 * (lam n - lam m) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hD2]
      nlinarith [hsq]
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hstep hww]

/-- **The assembled near/far budget for the anchored observable.** -/
theorem minorForm_le_nearFar {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (s Delta : ℝ) :
    minorForm w lam s
      ≤ s ^ 2 * Delta ^ 2 / 2 * nearMass w lam Delta + 2 * farMass w lam Delta := by
  rw [minorForm_eq_near_add_far w lam s Delta]
  exact add_le_add (nearPart_le_nearMass hw s Delta) (farPart_le_farMass hw s Delta)

/-- **The compensated observable in near/far form.**  Combining the G11 twisted
normalization with the near/far split: the compensated observable carries the
factor `α²` *and* the near-diagonal gain `(sΔ)²`. -/
theorem compensatedMinor_le_nearFar {w lam : Fin d → ℝ} {s alpha Lam Delta : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 8 * Lam ^ 2 * alpha ^ 2 *
        (s ^ 2 * Delta ^ 2 / 2 * nearMass (coshWeight w lam alpha) lam Delta
          + 2 * farMass (coshWeight w lam alpha) lam Delta) := by
  have hW : ∀ n, 0 ≤ coshWeight w lam alpha n := fun n =>
    mul_nonneg (hw n) (Real.cosh_pos _).le
  have hbase := compensatedMinor_le_twisted_uniform (s := s) (alpha := alpha) (Lam := Lam) hw hLam
  have hsplit := minorForm_le_nearFar (w := coshWeight w lam alpha) (lam := lam) hW s Delta
  have hfac : 0 ≤ 8 * Lam ^ 2 * alpha ^ 2 := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left hsplit hfac)

/-! ### The consumer: exact exclusion from a near/far gain -/

/-- **The near/far consumer.**  If the anchored defect is dominated by the
compensated observable, obeys the geometric floor, and the near/far budget beats
the floor constant, then the off-line displacement is exactly zero.  This is the
literal shape the remaining prime-side estimate has to produce. -/
theorem offLineTarget_excluded_of_nearFar_gain {w lam : Fin d → ℝ}
    {s alpha Lam Delta c L D : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam)
    (hc : 0 < c) (hL : 0 < L) (hD : 0 ≤ D)
    (hdefect : D ≤ compensatedMinor (coshWeight w lam) lam s alpha)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D)
    (hgain : 8 * Lam ^ 2 *
        (s ^ 2 * Delta ^ 2 / 2 * nearMass (coshWeight w lam alpha) lam Delta
          + 2 * farMass (coshWeight w lam alpha) lam Delta) < c * L ^ 6) :
    alpha = 0 := by
  set B : ℝ := s ^ 2 * Delta ^ 2 / 2 * nearMass (coshWeight w lam alpha) lam Delta
      + 2 * farMass (coshWeight w lam alpha) lam Delta with hB
  have hW : ∀ n, 0 ≤ coshWeight w lam alpha n := fun n =>
    mul_nonneg (hw n) (Real.cosh_pos _).le
  have hBnonneg : 0 ≤ 8 * Lam ^ 2 * B := by
    have h1 : 0 ≤ minorForm (coshWeight w lam alpha) lam s := minorForm_nonneg s hW
    have h2 := minorForm_le_nearFar (w := coshWeight w lam alpha) (lam := lam) hW s Delta
    have hL2 : (0 : ℝ) ≤ 8 * Lam ^ 2 := by positivity
    nlinarith [h1, h2]
  have hcL : 0 < c * L ^ 6 := by positivity
  set eta : ℝ := 8 * Lam ^ 2 * B / (c * L ^ 6) with heta
  have heta1 : eta < 1 := (div_lt_one hcL).mpr (by rw [hB] at hgain ⊢; linarith)
  have hetanonneg : 0 ≤ eta := div_nonneg hBnonneg hcL.le
  have hchain : D ≤ 8 * Lam ^ 2 * B * alpha ^ 2 := by
    have := compensatedMinor_le_nearFar (w := w) (lam := lam) (s := s) (alpha := alpha)
      (Lam := Lam) (Delta := Delta) hw hLam
    rw [← hB] at this
    nlinarith [hdefect, this]
  have hrel : D ≤ eta * D := by
    have hstep : eta * (c * L ^ 6 * alpha ^ 2) ≤ eta * D :=
      mul_le_mul_of_nonneg_left hfloor hetanonneg
    have heq : eta * (c * L ^ 6 * alpha ^ 2) = 8 * Lam ^ 2 * B * alpha ^ 2 := by
      rw [heta]; field_simp
    linarith [hchain, hstep, heq.le, heq.ge]
  exact offLineTarget_excluded_of_relative_budget hc hL hD heta1 hfloor hrel

/-! ### Q12.5, adversarially: exactly how much the diagonal zero is worth -/

/-- A quantitative lower bound for the anchored kernel: `1 − cos x ≥ x²/4` on
`|x| ≤ 1`.  Together with `one_sub_cos_le_half_sq` this pins the kernel to the
quadratic model on the near region. -/
theorem quarter_sq_le_one_sub_cos {x : ℝ} (hx : |x| ≤ 1) : x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have hb := Real.cos_bound hx
  have hb' : Real.cos x - (1 - x ^ 2 / 2) ≤ |x| ^ 4 * (5 / 96) :=
    (abs_le.mp hb).2
  have hx2 : x ^ 2 ≤ 1 := by
    nlinarith [sq_abs x, abs_nonneg x, hx]
  have hx4 : |x| ^ 4 ≤ x ^ 2 := by
    have hrw : |x| ^ 4 = x ^ 2 * x ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
    rw [hrw]
    nlinarith [sq_nonneg x, hx2]
  nlinarith [hb', hx4]

/-- The two-point weight family. -/
noncomputable def twoPointWeight : Fin 2 → ℝ := ![1, 1]

/-- The two-point log-frequency family at spacing `Δ`. -/
noncomputable def twoPointFreq (Delta : ℝ) : Fin 2 → ℝ := ![0, Delta]

theorem twoPointWeight_nonneg : ∀ n, 0 ≤ twoPointWeight n := by
  intro n; fin_cases n <;> simp [twoPointWeight]

theorem minorForm_twoPoint (s Delta : ℝ) :
    minorForm twoPointWeight (twoPointFreq Delta) s = 2 * (1 - Real.cos (s * Delta)) := by
  simp [minorForm, twoPointWeight, twoPointFreq, Fin.sum_univ_two, mul_comm]
  ring

/-- At spacing exactly `Δ` every pair of the two-point family is near-diagonal. -/
theorem twoPoint_filter_eq_univ {Delta : ℝ} (hDelta : 0 ≤ Delta) (n : Fin 2) :
    Finset.univ.filter
        (fun m => |twoPointFreq Delta n - twoPointFreq Delta m| ≤ Delta) = Finset.univ := by
  refine Finset.filter_true_of_mem fun m _ => ?_
  fin_cases n <;> fin_cases m <;>
    simp [twoPointFreq, abs_of_nonneg hDelta, abs_of_nonpos (neg_nonpos.mpr hDelta), hDelta]

theorem nearMass_twoPoint {Delta : ℝ} (hDelta : 0 ≤ Delta) :
    nearMass twoPointWeight (twoPointFreq Delta) Delta = 4 := by
  unfold nearMass
  have h : ∀ n : Fin 2, ∑ m ∈ Finset.univ.filter
      (fun m => |twoPointFreq Delta n - twoPointFreq Delta m| ≤ Delta),
      twoPointWeight n * twoPointWeight m
      = ∑ m : Fin 2, twoPointWeight n * twoPointWeight m := by
    intro n; rw [twoPoint_filter_eq_univ hDelta n]
  rw [Finset.sum_congr rfl fun n _ => h n]
  simp [twoPointWeight, Fin.sum_univ_two]
  norm_num

theorem nearPart_twoPoint {Delta : ℝ} (hDelta : 0 ≤ Delta) (s : ℝ) :
    nearPart twoPointWeight (twoPointFreq Delta) s Delta
      = 2 * (1 - Real.cos (s * Delta)) := by
  have hfar : farPart twoPointWeight (twoPointFreq Delta) s Delta = 0 := by
    unfold farPart
    refine Finset.sum_eq_zero fun n _ => ?_
    have : Finset.univ.filter
        (fun m => ¬ |twoPointFreq Delta n - twoPointFreq Delta m| ≤ Delta) = ∅ := by
      rw [Finset.filter_not, twoPoint_filter_eq_univ hDelta n, Finset.sdiff_self]
    rw [this, Finset.sum_empty]
  have hsplit := minorForm_eq_near_add_far twoPointWeight (twoPointFreq Delta) s Delta
  rw [minorForm_twoPoint, hfar, add_zero] at hsplit
  exact hsplit.symm

/-- **The near-diagonal bound is sharp up to the factor `4`.**  A two-point
configuration at spacing `Δ` realises `nearPart ≥ ¼·(s²Δ²/2)·nearMass`.  So the
gain produced by the quadratic diagonal zero is exactly the factor `(sΔ)²` and
nothing better: no further cancellation can be extracted from the kernel alone. -/
theorem nearPart_twoPoint_ge {s Delta : ℝ} (hDelta : 0 ≤ Delta) (hs : 0 ≤ s)
    (hsD : s * Delta ≤ 1) :
    1 / 4 * (s ^ 2 * Delta ^ 2 / 2 * nearMass twoPointWeight (twoPointFreq Delta) Delta)
      ≤ nearPart twoPointWeight (twoPointFreq Delta) s Delta := by
  have habs : |s * Delta| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg hs hDelta)]; exact hsD
  have hlow := quarter_sq_le_one_sub_cos habs
  rw [nearPart_twoPoint hDelta, nearMass_twoPoint hDelta]
  nlinarith [hlow]

/-- **And the gain is worth nothing once the window is wide.**  If `sΔ = π`
the near part equals the *entire* near mass: the quadratic diagonal zero
produces no gain at all.  Hence a vanishing relative prime budget cannot follow
from the diagonal structure alone — it requires `sΔ → 0`, a statement about the
actual spacing of log-prime frequencies against the window scale. -/
theorem nearPart_twoPoint_eq_nearMass_of_pi {s Delta : ℝ} (hDelta : 0 ≤ Delta)
    (hsD : s * Delta = Real.pi) :
    nearPart twoPointWeight (twoPointFreq Delta) s Delta
      = nearMass twoPointWeight (twoPointFreq Delta) Delta := by
  rw [nearPart_twoPoint hDelta, nearMass_twoPoint hDelta, hsD, Real.cos_pi]
  norm_num

/-- **The exact criterion the prime side must meet.**  For the two-point model
the near/far budget is contractive against a floor `cL⁶` precisely when the
product `sΔ` is small enough; there is no configuration-free choice.  Stated as
the theorem that a contraction forces a smallness relation between the window
scale, the spacing and the floor. -/
theorem nearFar_contraction_forces_small_spacing {s Delta Lam c L : ℝ}
    (hDelta : 0 ≤ Delta)
    (hgain : 8 * Lam ^ 2 *
        (s ^ 2 * Delta ^ 2 / 2 * nearMass twoPointWeight (twoPointFreq Delta) Delta
          + 2 * farMass twoPointWeight (twoPointFreq Delta) Delta) < c * L ^ 6) :
    16 * Lam ^ 2 * s ^ 2 * Delta ^ 2 < c * L ^ 6 := by
  have hfar : farMass twoPointWeight (twoPointFreq Delta) Delta = 0 := by
    unfold farMass
    refine Finset.sum_eq_zero fun n _ => ?_
    have : Finset.univ.filter
        (fun m => ¬ |twoPointFreq Delta n - twoPointFreq Delta m| ≤ Delta) = ∅ := by
      rw [Finset.filter_not, twoPoint_filter_eq_univ hDelta n, Finset.sdiff_self]
    rw [this, Finset.sum_empty]
  rw [nearMass_twoPoint hDelta, hfar] at hgain
  nlinarith [hgain]

end RiemannAnalytic

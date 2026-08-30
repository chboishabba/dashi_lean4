import RiemannAnalytic.SourceNormalization

/-!
# G14 — the log-frequency pigeonhole experiment, and its exact no-go

The proposed cheap structural test for the remaining prime obligation was:

> decompose log-frequency space into `J` nested shells; if the total off-diagonal
> mass is finite there must be a shell whose relative mass is `≲ 1/J`; choose the
> cutoff there and balance the near-diagonal Taylor gain `(tΔ)²` against the far
> mass loss.

This module carries the experiment out at literal strength and reports the exact
outcome.

* The deterministic half is **true and proved**: `exists_thin_logFrequency_shell`
  — for any nonnegative pair weights and any nested family of cutoffs there is a
  shell whose *incremental* mass is at most the total mass divided by `J`.

* The analytic half **fails, and the failure is proved, not conjectured**:
  a thin shell is not a thin tail.  `farMass_ge_of_logVar` shows that a weight
  family whose log-frequencies lie in a window of width `W` and whose log
  variance is at least `κ` times the squared total mass has far mass at least
  `κ/W²` times the squared total mass at **every** cutoff `Δ ≤ √κ`.  Applied to
  the literal cosh-twisted von Mangoldt weights (where G13 proved `κ = 10⁻⁷`
  and `W = log N`), this gives `zetaFarMass_ge`:

```
10⁻⁷ S₀² / (log N)²  ≤  farMass_N(α, Δ)      for every Δ ≤ 10⁻⁴.
```

* Consequently `zeta_nearFar_strictly_worse_than_global`: in exactly the regime
  where the near-diagonal Taylor gain would be useful — small phase
  `t log N ≪ 1` — the far term of the near/far budget **alone** already exceeds
  the global bound `15000 t²S₀²` proved in `SourceNormalization`.  The near/far
  selection is therefore strictly worse than doing nothing.

So the answer to the experiment is definite: the deterministic scale-selection
argument is sound but cannot supply the missing factor, because the literal
twisted von Mangoldt measure has no thin log-frequency tail at any scale.  The
remaining unknown is unchanged and is the source normalization constant
(`SourceNormalization.offLineZero_excluded_of_sourceRatio`).
-/

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ### Near and far pair mass -/

/-- The near-diagonal pair mass at log-frequency cutoff `Δ`. -/
noncomputable def nearMassN (s : Finset ℕ) (w l : ℕ → ℝ) (Delta : ℝ) : ℝ :=
  ∑ n ∈ s, ∑ m ∈ s.filter (fun m => |l n - l m| ≤ Delta), w n * w m

/-- The far-diagonal (tail) pair mass at log-frequency cutoff `Δ`. -/
noncomputable def farMassN (s : Finset ℕ) (w l : ℕ → ℝ) (Delta : ℝ) : ℝ :=
  ∑ n ∈ s, ∑ m ∈ s.filter (fun m => ¬ |l n - l m| ≤ Delta), w n * w m

theorem nearMass_add_farMass (s : Finset ℕ) (w l : ℕ → ℝ) (Delta : ℝ) :
    nearMassN s w l Delta + farMassN s w l Delta = (∑ n ∈ s, w n) ^ 2 := by
  unfold nearMassN farMassN
  rw [← Finset.sum_add_distrib]
  have hrow : ∀ n ∈ s,
      (∑ m ∈ s.filter (fun m => |l n - l m| ≤ Delta), w n * w m)
        + (∑ m ∈ s.filter (fun m => ¬ |l n - l m| ≤ Delta), w n * w m)
        = w n * ∑ m ∈ s, w m := fun n _ => by
    rw [Finset.sum_filter_add_sum_filter_not, Finset.mul_sum]
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_mul, sq]

theorem farMassN_nonneg {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n) (Delta : ℝ) :
    0 ≤ farMassN s w l Delta := by
  refine Finset.sum_nonneg fun n hn => Finset.sum_nonneg fun m hm => ?_
  exact mul_nonneg (hw n hn) (hw m (Finset.mem_filter.mp hm).1)

theorem nearMassN_nonneg {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n) (Delta : ℝ) :
    0 ≤ nearMassN s w l Delta := by
  refine Finset.sum_nonneg fun n hn => Finset.sum_nonneg fun m hm => ?_
  exact mul_nonneg (hw n hn) (hw m (Finset.mem_filter.mp hm).1)

theorem farMassN_le_total {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n) (Delta : ℝ) :
    farMassN s w l Delta ≤ (∑ n ∈ s, w n) ^ 2 := by
  have h := nearMass_add_farMass s w l Delta
  have := nearMassN_nonneg hw (l := l) (s := s) (w := w) Delta
  linarith

/-- The far mass is antitone in the cutoff: a smaller cutoff sees more mass. -/
theorem farMassN_antitone {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n)
    {Delta Delta' : ℝ} (h : Delta ≤ Delta') :
    farMassN s w l Delta' ≤ farMassN s w l Delta := by
  unfold farMassN
  refine Finset.sum_le_sum fun n hn => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, fun hle => hm.2 (le_trans hle h)⟩
  · intro m hm _
    exact mul_nonneg (hw n hn) (hw m (Finset.mem_filter.mp hm).1)

/-! ### The deterministic pigeonhole cut -/

/-- **`LogFrequencyPigeonholeCut`.**  For any nonnegative pair weights and any
family of log-frequency cutoffs `Δ₀, Δ₁, …` — in the intended application a
decreasing (dyadic) family, though the proof needs no monotonicity — one of the
first `J` shells carries incremental mass at most `1/J` of the total pair mass.
This is the deterministic half of the scale-selection experiment, and it is
unconditionally true. -/
theorem exists_thin_logFrequency_shell {s : Finset ℕ} {w l : ℕ → ℝ}
    (hw : ∀ n ∈ s, 0 ≤ w n) {J : ℕ} (hJ : 0 < J) (Dl : ℕ → ℝ) :
    ∃ j < J, farMassN s w l (Dl (j + 1)) - farMassN s w l (Dl j)
      ≤ (∑ n ∈ s, w n) ^ 2 / J := by
  by_contra hcon
  push_neg at hcon
  set f : ℕ → ℝ := fun j => farMassN s w l (Dl j) with hf
  have htel : ∑ j ∈ Finset.range J, (f (j + 1) - f j) = f J - f 0 :=
    Finset.sum_range_sub f J
  have hlow : (∑ n ∈ s, w n) ^ 2 < ∑ j ∈ Finset.range J, (f (j + 1) - f j) := by
    have hlt : ∀ j ∈ Finset.range J,
        (∑ n ∈ s, w n) ^ 2 / J < f (j + 1) - f j := fun j hj =>
      hcon j (Finset.mem_range.mp hj)
    have hsum := Finset.sum_lt_sum_of_nonempty
      (Finset.nonempty_range_iff.mpr hJ.ne') hlt
    have hconst : ∑ _j ∈ Finset.range J, (∑ n ∈ s, w n) ^ 2 / J
        = (∑ n ∈ s, w n) ^ 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rwa [hconst] at hsum
  have hupper : f J - f 0 ≤ (∑ n ∈ s, w n) ^ 2 := by
    have h1 : f J ≤ (∑ n ∈ s, w n) ^ 2 := farMassN_le_total hw _
    have h2 : 0 ≤ f 0 := farMassN_nonneg hw _
    linarith
  rw [htel] at hlow
  linarith

/-! ### Why the thin shell does not help: the tail is never thin -/

/-- If all log-frequency separations are at most `W`, the log-variance is
controlled by the near mass at scale `Δ` and the far mass at scale `W`:
`2·logVar ≤ Δ²·nearMass + W²·farMass`. -/
theorem twice_logVar_le_nearFar {s : Finset ℕ} {w l : ℕ → ℝ} {W Delta : ℝ}
    (hw : ∀ n ∈ s, 0 ≤ w n) (hW : ∀ n ∈ s, ∀ m ∈ s, |l n - l m| ≤ W) :
    2 * logVar s w l ≤ Delta ^ 2 * nearMassN s w l Delta + W ^ 2 * farMassN s w l Delta := by
  have hid := varForm_eq_double s w l
  have hrow : ∀ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2
      ≤ (∑ m ∈ s.filter (fun m => |l n - l m| ≤ Delta), Delta ^ 2 * (w n * w m))
        + (∑ m ∈ s.filter (fun m => ¬ |l n - l m| ≤ Delta), W ^ 2 * (w n * w m)) := by
    intro n hn
    rw [← Finset.sum_filter_add_sum_filter_not s (fun m => |l n - l m| ≤ Delta)]
    refine add_le_add (Finset.sum_le_sum fun m hm => ?_) (Finset.sum_le_sum fun m hm => ?_)
    · obtain ⟨hms, hclose⟩ := Finset.mem_filter.mp hm
      have hww : 0 ≤ w n * w m := mul_nonneg (hw n hn) (hw m hms)
      have hsq : (l n - l m) ^ 2 ≤ Delta ^ 2 := by
        nlinarith [abs_nonneg (l n - l m), sq_abs (l n - l m), hclose]
      nlinarith [mul_le_mul_of_nonneg_left hsq hww]
    · obtain ⟨hms, _⟩ := Finset.mem_filter.mp hm
      have hww : 0 ≤ w n * w m := mul_nonneg (hw n hn) (hw m hms)
      have hsq : (l n - l m) ^ 2 ≤ W ^ 2 := by
        nlinarith [abs_nonneg (l n - l m), sq_abs (l n - l m), hW n hn m hms]
      nlinarith [mul_le_mul_of_nonneg_left hsq hww]
  have hsum : ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2
      ≤ Delta ^ 2 * nearMassN s w l Delta + W ^ 2 * farMassN s w l Delta := by
    have hle := Finset.sum_le_sum hrow
    rw [Finset.sum_add_distrib] at hle
    unfold nearMassN farMassN
    rw [Finset.mul_sum, Finset.mul_sum]
    have h1 : ∀ n ∈ s, Delta ^ 2 * ∑ m ∈ s.filter (fun m => |l n - l m| ≤ Delta), w n * w m
        = ∑ m ∈ s.filter (fun m => |l n - l m| ≤ Delta), Delta ^ 2 * (w n * w m) :=
      fun n _ => by rw [Finset.mul_sum]
    have h2 : ∀ n ∈ s, W ^ 2 * ∑ m ∈ s.filter (fun m => ¬ |l n - l m| ≤ Delta), w n * w m
        = ∑ m ∈ s.filter (fun m => ¬ |l n - l m| ≤ Delta), W ^ 2 * (w n * w m) :=
      fun n _ => by rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2]
    exact hle
  unfold logVar
  rw [hid]
  linarith

/-- **The tail is never thin.**  If the log-variance is at least `κ` times the
squared total mass and all separations are at most `W`, then at *every* cutoff
`Δ` with `Δ² ≤ κ` the far mass is at least `κ/W²` times the squared total mass.
No pigeonhole choice of cutoff can evade this. -/
theorem farMass_ge_of_logVar {s : Finset ℕ} {w l : ℕ → ℝ} {W Delta kappa : ℝ}
    (hw : ∀ n ∈ s, 0 ≤ w n) (hW : ∀ n ∈ s, ∀ m ∈ s, |l n - l m| ≤ W) (hW0 : 0 < W)
    (hvar : kappa * (∑ n ∈ s, w n) ^ 2 ≤ logVar s w l)
    (hDelta : Delta ^ 2 ≤ kappa) :
    kappa * (∑ n ∈ s, w n) ^ 2 / W ^ 2 ≤ farMassN s w l Delta := by
  have hmain := twice_logVar_le_nearFar (W := W) (Delta := Delta) hw hW
  have hnear : nearMassN s w l Delta ≤ (∑ n ∈ s, w n) ^ 2 := by
    have h := nearMass_add_farMass s w l Delta
    have := farMassN_nonneg hw (l := l) (s := s) (w := w) Delta
    linarith
  have hnn : 0 ≤ (∑ n ∈ s, w n) ^ 2 := sq_nonneg _
  have hnearmass : 0 ≤ nearMassN s w l Delta := nearMassN_nonneg hw Delta
  have hD2 : 0 ≤ Delta ^ 2 := sq_nonneg _
  have hstep : Delta ^ 2 * nearMassN s w l Delta ≤ kappa * (∑ n ∈ s, w n) ^ 2 := by
    calc Delta ^ 2 * nearMassN s w l Delta
        ≤ Delta ^ 2 * (∑ n ∈ s, w n) ^ 2 := mul_le_mul_of_nonneg_left hnear hD2
      _ ≤ kappa * (∑ n ∈ s, w n) ^ 2 := mul_le_mul_of_nonneg_right hDelta hnn
  have hW2 : 0 < W ^ 2 := by positivity
  rw [div_le_iff₀ hW2]
  nlinarith [hmain, hvar, hstep]

/-! ### The literal instantiation: the twisted von Mangoldt tail -/

/-- Every log-frequency separation inside `[1,N]` is at most `log N`. -/
theorem zeta_window (N : ℕ) :
    ∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N, |Real.log n - Real.log m| ≤ Real.log N := by
  intro n hn m hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hlogn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hlognN : Real.log n ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hn1); exact_mod_cast hnN
  have hlogmN : Real.log m ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hm1); exact_mod_cast hmN
  rw [abs_le]; constructor <;> linarith

/-- **The literal no-thin-tail theorem.**  For the actual cosh-twisted von
Mangoldt weights, at every log-frequency cutoff `Δ ≤ 10⁻⁴`,

```
10⁻⁷ S₀² / (log N)²  ≤  farMass_N(α, Δ),
```

uniformly for `|α| < 1/2` and `N ≥ 10⁹`.  The tail mass is therefore never
smaller than an inverse-logarithmic fraction of the total, whatever cutoff a
pigeonhole argument selects. -/
theorem zetaFarMass_ge {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ)) {α : ℝ} (hα : |α| < 1 / 2)
    {Delta : ℝ} (hDelta : Delta ^ 2 ≤ 1 / 10 ^ 7) :
    (1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2 / (Real.log N) ^ 2
      ≤ farMassN (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n) Delta := by
  have hlogpos : 0 < Real.log N := by
    have h1 : (1 : ℝ) < (N : ℝ) := by nlinarith
    exact Real.log_pos h1
  have hvar : (1 / 10 ^ 7 : ℝ) * (∑ n ∈ Icc 1 N, coshVonMangoldt α n) ^ 2
      ≤ logVar (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n) := by
    rw [logVar_icc_eq, ← twistedMoment_zero]
    exact zetaTwistedPrimeVariance_lower hN hα
  have := farMass_ge_of_logVar (s := Icc 1 N) (w := coshVonMangoldt α)
    (l := fun n => Real.log n) (W := Real.log N) (Delta := Delta) (kappa := 1 / 10 ^ 7)
    (fun n _ => coshVonMangoldt_nonneg α n) (zeta_window N) hlogpos hvar hDelta
  rwa [← twistedMoment_zero] at this

/-- **The exact no-go for the near/far selection experiment.**  In the
small-phase regime — precisely the regime in which the near-diagonal Taylor gain
`(tΔ)²` would be useful — the *far term alone* of the near/far budget already
exceeds the unconditional global bound `15000 t²S₀²` of
`zetaAnchoredPrimeForm_le`.  So no choice of log-frequency cutoff, pigeonhole or
otherwise, improves on the global estimate. -/
theorem zeta_nearFar_strictly_worse_than_global {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) {Delta t : ℝ} (hDelta : Delta ^ 2 ≤ 1 / 10 ^ 7)
    (hS : 0 < twistedMoment N α 0)
    (ht : t ^ 2 * (Real.log N) ^ 2 < 1 / (15000 * 10 ^ 7)) :
    15000 * t ^ 2 * (twistedMoment N α 0) ^ 2
      < 2 * farMassN (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n) Delta := by
  have hfar := zetaFarMass_ge hN hα hDelta
  have hlogpos : 0 < Real.log N := by
    have h1 : (1 : ℝ) < (N : ℝ) := by nlinarith
    exact Real.log_pos h1
  have hL2 : 0 < (Real.log N) ^ 2 := by positivity
  have hS2 : 0 < (twistedMoment N α 0) ^ 2 := by positivity
  have hkey : 15000 * t ^ 2 * (twistedMoment N α 0) ^ 2
      < 2 * ((1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2 / (Real.log N) ^ 2) := by
    have hrw : 2 * ((1 / 10 ^ 7 : ℝ) * (twistedMoment N α 0) ^ 2 / (Real.log N) ^ 2)
        = (2 / 10 ^ 7 * (twistedMoment N α 0) ^ 2) / (Real.log N) ^ 2 := by ring
    rw [hrw, lt_div_iff₀ hL2]
    nlinarith [mul_lt_mul_of_pos_left ht hS2]
  linarith [hfar, hkey]

end RiemannAnalytic

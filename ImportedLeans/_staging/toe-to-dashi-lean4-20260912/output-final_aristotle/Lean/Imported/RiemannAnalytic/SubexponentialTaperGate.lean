import RiemannAnalytic.SourceCoefficient
import RiemannAnalytic.TaperAnalyticIncompatibility

/-!
# The gate is red up to the critical exponential rate

`SourceCoefficient.lean` proved the source-normalization gate red for every
taper whose transform decays at worst *polynomially* along the prime
frequencies `u = log n` (`taperedWeil_gate_fails_of_polyDecay`), and observed
that only an *exponentially* decaying transform could make the gate green.
That left a gap: a smooth compactly supported taper has a transform decaying
faster than any polynomial but (as `TaperAnalyticIncompatibility.lean` now
proves) never exponentially.  This module closes the gap quantitatively, by
locating the critical decay rate.

* `log_pow_le_mul_rpow` — the general form of the tool behind the verdict:
  `(log N)^k ≤ (k/δ)^k N^δ` for every `δ > 0`; the previous
  `log_pow_le_mul_sqrt` is the case `δ = 1/2`.
* `gate_fails_of_power_gain` — **master theorem**: if the gate quantity
  `C_src t² S²` retains *any* positive power `κN^δ` after an arbitrary
  polylogarithmic loss, the G14 contraction condition fails, subject only to
  the explicit constant comparison `c((A+4)/δ)^{A+4} ≤ 120000κ`.
* `taperedWeilMass_lower_of_expDecay` — an exponential lower bound
  `|φ̂(u)| ≥ κ_φ e^{-ru}` on the prime frequencies keeps the tapered Weil mass
  at `κ_φ N^{-r}` times the full Weil mass.
* `taperedWeilMass_lower_of_topWindow` and
  `taperedWeil_gate_fails_of_topWindow_expDecay` — the same verdict assuming the
  lower bound only on the **top** frequency window `[log N − log 4, log N]`,
  using the Chebyshev block bound `psi_block_lower`; no hypothesis on `α` is
  needed.
* `taperedWeil_gate_fails_of_subcritical_expDecay` — **the sharpened verdict**:
  for every taper whose transform stays above `κ_φ e^{-ru}` along
  `u = log n ∈ [0, log N]` with a *subcritical* rate `r < 1/2`, the gate fails.
  The critical rate `1/2` is exactly the archimedean normalization `n^{-1/2}`
  of the explicit formula; no smaller rate helps, and the two-sided Weil mass
  bound shows the true threshold is `1/2 + 2|α|`.

Combined with `compactTaper_fourier_not_expDecay`, the taper trichotomy is now
complete for this route: polynomial decay is red, subcritical exponential decay
is red, and supercritical exponential decay is unavailable to any compactly
supported taper — which is the class for which the source-side `L⁶` Gram floor
is proved.  Nothing here proves the Riemann Hypothesis.
-/

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ### Logarithms against an arbitrary power -/

/-- `(log N)^k ≤ (k/δ)^k N^δ` for every `k ≥ 1` and every `δ > 0`: a power of
`N`, however small the exponent, beats every power of `log N`. -/
theorem log_pow_le_mul_rpow (N : ℕ) {k : ℕ} (hk : 0 < k) {δ : ℝ} (hδ : 0 < δ) :
    (Real.log N) ^ k ≤ ((k : ℝ) / δ) ^ k * (N : ℝ) ^ δ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hε : (0 : ℝ) < δ / k := by positivity
  have h := Real.log_natCast_le_rpow_div N (ε := δ / k) hε
  have hnn : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hdiv : (N : ℝ) ^ (δ / k) / (δ / k) = ((k : ℝ) / δ) * (N : ℝ) ^ (δ / k) := by
    field_simp
  rw [hdiv] at h
  have hpow : (((k : ℝ) / δ) * (N : ℝ) ^ (δ / k)) ^ k = ((k : ℝ) / δ) ^ k * (N : ℝ) ^ δ := by
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (δ / k)) k,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    congr 2
    field_simp
  calc (Real.log N) ^ k ≤ (((k : ℝ) / δ) * (N : ℝ) ^ (δ / k)) ^ k := pow_le_pow_left₀ hnn h k
    _ = ((k : ℝ) / δ) ^ k * (N : ℝ) ^ δ := hpow

/-! ### The master gate theorem with an arbitrary power gain -/

/-- **Any surviving power of `N` defeats the gate.**  If, after an arbitrary
polylogarithmic loss `(log N)^A`, the gate quantity `C_src t² S²` is still at
least `κ N^δ` for some `δ > 0`, the contraction condition

```
120000 (log N)² · C_src t² S²  <  c (log N)⁶
```

is false, provided only `c((A+4)/δ)^{A+4} ≤ 120000κ`.  `gate_fails_of_polylog_loss`
is the case `δ = 1/2`. -/
theorem gate_fails_of_power_gain {N A : ℕ} {c t κ Csrc S δ : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hc : 0 < c) (hδ : 0 < δ)
    (hlow : κ * (N : ℝ) ^ δ ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2))
    (hthr : c * (((A : ℝ) + 4) / δ) ^ (A + 4) ≤ 120000 * κ) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) < c * (Real.log N) ^ 6) := by
  intro hgate
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  have hLA : (0 : ℝ) < (Real.log N) ^ A := pow_pos hLpos A
  have hL2 : (0 : ℝ) < (Real.log N) ^ 2 := pow_pos hLpos 2
  have hrp : (0 : ℝ) < (N : ℝ) ^ δ := Real.rpow_pos_of_pos hN0 δ
  have h1 : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A
      < c * (Real.log N) ^ 6 * (Real.log N) ^ A :=
    mul_lt_mul_of_pos_right hgate hLA
  have hLHS : 120000 * (Real.log N) ^ 2 * (κ * (N : ℝ) ^ δ)
      ≤ 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A := by
    have hrw : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) * (Real.log N) ^ A
        = 120000 * (Real.log N) ^ 2 * (Csrc * (Real.log N) ^ A * (t ^ 2 * S ^ 2)) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hlow (by positivity)
  have hRHS : c * (Real.log N) ^ 6 * (Real.log N) ^ A
      = c * (Real.log N) ^ (A + 4) * (Real.log N) ^ 2 := by
    rw [pow_add]; ring
  have hstep : 120000 * (Real.log N) ^ 2 * (κ * (N : ℝ) ^ δ)
      < c * (Real.log N) ^ (A + 4) * (Real.log N) ^ 2 := by
    rw [← hRHS]; linarith [hLHS, h1]
  have hcancel : 120000 * (κ * (N : ℝ) ^ δ) < c * (Real.log N) ^ (A + 4) := by
    have hrw : 120000 * (Real.log N) ^ 2 * (κ * (N : ℝ) ^ δ)
        = (120000 * (κ * (N : ℝ) ^ δ)) * (Real.log N) ^ 2 := by ring
    rw [hrw] at hstep
    exact lt_of_mul_lt_mul_right (by linarith [hstep]) hL2.le
  have hlogpow := log_pow_le_mul_rpow N (k := A + 4) (Nat.succ_pos _) hδ
  have hcast : (((A + 4 : ℕ) : ℝ) / δ) ^ (A + 4) = (((A : ℝ) + 4) / δ) ^ (A + 4) := by
    push_cast; ring_nf
  rw [hcast] at hlogpow
  have hchain : c * (Real.log N) ^ (A + 4)
      ≤ c * ((((A : ℝ) + 4) / δ) ^ (A + 4) * (N : ℝ) ^ δ) :=
    mul_le_mul_of_nonneg_left hlogpow hc.le
  have hfin : c * ((((A : ℝ) + 4) / δ) ^ (A + 4) * (N : ℝ) ^ δ)
      ≤ 120000 * κ * (N : ℝ) ^ δ := by
    have hrw : c * ((((A : ℝ) + 4) / δ) ^ (A + 4) * (N : ℝ) ^ δ)
        = (c * (((A : ℝ) + 4) / δ) ^ (A + 4)) * (N : ℝ) ^ δ := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hthr hrp.le
  linarith [hcancel, hchain, hfin]

/-! ### Exponentially decaying tapers below the critical rate -/

/-- **An exponentially decaying taper transform costs exactly `N^{-r}`.**  If
`|φ̂(u)| ≥ κ_φ e^{-ru}` along the prime frequencies `u = log n ∈ [0, log N]`,
the tapered Weil mass is the full Weil mass up to `κ_φ e^{-r log N} = κ_φ N^{-r}`. -/
theorem taperedWeilMass_lower_of_expDecay {phi : ℝ → ℝ} {N : ℕ} {α r κ : ℝ}
    (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hphi : ∀ u : ℝ, 0 ≤ u → u ≤ Real.log N → κ * Real.exp (-(r * u)) ≤ |phi u|) :
    κ * Real.exp (-(r * Real.log N)) * weilMass N α ≤ taperedWeilMass phi N α := by
  unfold taperedWeilMass weilMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogle : Real.log n ≤ Real.log N := Real.log_le_log hn0 (by exact_mod_cast hnN)
  have hmono : Real.exp (-(r * Real.log N)) ≤ Real.exp (-(r * Real.log n)) := by
    refine Real.exp_le_exp.mpr ?_
    have : r * Real.log n ≤ r * Real.log N := mul_le_mul_of_nonneg_left hlogle hr
    linarith
  have hstep : κ * Real.exp (-(r * Real.log N)) ≤ |phi (Real.log n)| :=
    le_trans (mul_le_mul_of_nonneg_left hmono hκ) (hphi _ hlogn hlogle)
  have hw : 0 ≤ weilWeight α n := weilWeight_nonneg α n
  calc κ * Real.exp (-(r * Real.log N)) * weilWeight α n
      ≤ |phi (Real.log n)| * weilWeight α n := mul_le_mul_of_nonneg_right hstep hw
    _ = weilWeight α n * |phi (Real.log n)| := by ring

/-- **Red for every subcritical exponential decay rate.**  If the source
coefficient loses at worst a fixed power of `log N`, and the taper transform
stays above `κ_φ e^{-ru}` on the prime frequencies with a rate `r < 1/2`, the
normalization gate fails.  The critical rate `1/2` is precisely the archimedean
normalization `n^{-1/2}` of the explicit formula. -/
theorem taperedWeil_gate_fails_of_subcritical_expDecay {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {phi : ℝ → ℝ} {α t c κ κphi Csrc r : ℝ}
    (hα : |α| < 1 / 2) (hc : 0 < c) (hκ : 0 < κ) (hκphi : 0 < κphi)
    (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hphi : ∀ u : ℝ, 0 ≤ u → u ≤ Real.log N → κphi * Real.exp (-(r * u)) ≤ |phi u|)
    (hthr : c * (((A : ℝ) + 4) / (1 - 2 * r)) ^ (A + 4)
      ≤ 120000 * (κ * κphi ^ 2 * t ^ 2 / 1024)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (taperedWeilMass phi N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set P : ℝ := taperedWeilMass phi N α with hP
  -- the Weil mass is at least `N^{1/2}/32`
  have hmassW := (weilMass_two_sided hN hα).1
  have hpow : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 + 2 * |α| : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith [abs_nonneg α])
  have hW : (N : ℝ) ^ (1 / 2 : ℝ) / 32 ≤ weilMass N α := by linarith [hmassW, hpow]
  -- the exponential loss is exactly `N^{-r}`
  have hexp : Real.exp (-(r * Real.log N)) = (N : ℝ) ^ (-r) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  have htap := taperedWeilMass_lower_of_expDecay (phi := phi) (N := N) (α := α)
    hκphi.le hr0 hphi
  rw [hexp] at htap
  have hrpos : (0 : ℝ) < (N : ℝ) ^ (-r) := Real.rpow_pos_of_pos hN0 (-r)
  have hlow1 : κphi * (N : ℝ) ^ (-r) * ((N : ℝ) ^ (1 / 2 : ℝ) / 32) ≤ P := by
    refine le_trans ?_ htap
    exact mul_le_mul_of_nonneg_left hW (by positivity)
  -- combine the two powers
  have hcomb : (N : ℝ) ^ (-r) * (N : ℝ) ^ (1 / 2 : ℝ) = (N : ℝ) ^ (1 / 2 - r : ℝ) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hlow2 : κphi / 32 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ P := by
    calc κphi / 32 * (N : ℝ) ^ (1 / 2 - r : ℝ)
        = κphi * (N : ℝ) ^ (-r) * ((N : ℝ) ^ (1 / 2 : ℝ) / 32) := by
          rw [← hcomb]; ring
      _ ≤ P := hlow1
  have hsq : ((N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 = (N : ℝ) ^ (1 - 2 * r : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 - r : ℝ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hPsq : κphi ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ) ≤ P ^ 2 := by
    have h0 : (0 : ℝ) ≤ κphi / 32 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
      have := Real.rpow_pos_of_pos hN0 (1 / 2 - r : ℝ)
      positivity
    have hmono : (κphi / 32 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 ≤ P ^ 2 := by
      nlinarith [hlow2, h0]
    calc κphi ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)
        = (κphi / 32 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 := by
          rw [mul_pow, hsq]; ring
      _ ≤ P ^ 2 := hmono
  refine gate_fails_of_power_gain (A := A) (δ := 1 - 2 * r) hN hc (by linarith) ?_ hthr
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h1 : κ * (κphi ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)) ≤ κ * P ^ 2 :=
    mul_le_mul_of_nonneg_left hPsq hκ.le
  have h2 : κ * P ^ 2 ≤ Csrc * (Real.log N) ^ A * P ^ 2 :=
    mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
  have h3 : κ * κphi ^ 2 * t ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)
      ≤ Csrc * (Real.log N) ^ A * (t ^ 2 * P ^ 2) := by
    have h4 : κ * (κphi ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)) * t ^ 2
        ≤ Csrc * (Real.log N) ^ A * P ^ 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) ht2
    calc κ * κphi ^ 2 * t ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)
        = κ * (κphi ^ 2 / 1024 * (N : ℝ) ^ (1 - 2 * r : ℝ)) * t ^ 2 := by ring
      _ ≤ Csrc * (Real.log N) ^ A * P ^ 2 * t ^ 2 := h4
      _ = Csrc * (Real.log N) ^ A * (t ^ 2 * P ^ 2) := by ring
  exact h3

/-! ### Only the top frequency window is needed -/

/-- **The top window carries the whole obstruction.**  The lower bound on the
taper transform is only ever used near the top frequency: if
`|φ̂(u)| ≥ κ e^{-ru}` merely for `u ∈ [log N − log 4, log N]`, the tapered Weil
mass is already at least `(κ/4) N^{1/2−r}`.  The prime input is the Chebyshev
block bound `psi_block_lower`: the primes of `(N/4, N]` carry mass `≥ N/4`. -/
theorem taperedWeilMass_lower_of_topWindow {phi : ℝ → ℝ} {N : ℕ} {α r κ : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hphi : ∀ u : ℝ, Real.log N - Real.log 4 ≤ u → u ≤ Real.log N →
        κ * Real.exp (-(r * u)) ≤ |phi u|) :
    κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ taperedWeilMass phi N α := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hsub : Finset.Ioc (N / 4) N ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (by omega), h2⟩
  have hsplit : (N : ℝ) ^ (-(1/2) - r : ℝ) = (N : ℝ) ^ (-(1/2) : ℝ) * (N : ℝ) ^ (-r) := by
    rw [← Real.rpow_add hN0, show (-(1/2) : ℝ) + (-r) = -(1/2) - r by ring]
  have hexpN : Real.exp (-(r * Real.log N)) = (N : ℝ) ^ (-r) := by
    rw [Real.rpow_def_of_pos hN0]; congr 1; ring
  have hterm : ∀ n ∈ Finset.Ioc (N / 4) N,
      Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) ≤ weilWeight α n * |phi (Real.log n)| := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h2
    have hquarter : (N : ℝ) / 4 ≤ (n : ℝ) := by
      have hnat : N < 4 * n := by omega
      have : (N : ℝ) < 4 * (n : ℝ) := by exact_mod_cast hnat
      linarith
    have hlogn : Real.log N - Real.log 4 ≤ Real.log n := by
      have h := Real.log_le_log (by positivity) hquarter
      rwa [Real.log_div (ne_of_gt hN0) (by norm_num)] at h
    have hlogle : Real.log n ≤ Real.log N := Real.log_le_log hn0 hnN
    have htap : κ * Real.exp (-(r * Real.log N)) ≤ |phi (Real.log n)| := by
      refine le_trans ?_ (hphi (Real.log n) hlogn hlogle)
      have hmono : Real.exp (-(r * Real.log N)) ≤ Real.exp (-(r * Real.log n)) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith [mul_le_mul_of_nonneg_left hlogle hr]
      exact mul_le_mul_of_nonneg_left hmono hκ
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    have hw : Λ n * (N : ℝ) ^ (-(1/2) : ℝ) ≤ weilWeight α n := by
      unfold weilWeight
      have hcosh : (1 : ℝ) ≤ Real.cosh (2 * α * Real.log n) := Real.one_le_cosh _
      have hrp : (N : ℝ) ^ (-(1/2) : ℝ) ≤ (n : ℝ) ^ (-(1/2) : ℝ) :=
        Real.rpow_le_rpow_of_nonpos hn0 hnN (by norm_num)
      have h3 : (0:ℝ) ≤ (n:ℝ) ^ (-(1/2) : ℝ) := Real.rpow_nonneg hn0.le _
      nlinarith [mul_le_mul_of_nonneg_left hrp hΛ, mul_nonneg hΛ h3]
    have h0 : (0:ℝ) ≤ Λ n * (N : ℝ) ^ (-(1/2) : ℝ) :=
      mul_nonneg hΛ (Real.rpow_nonneg hN0.le _)
    have h1' : (0:ℝ) ≤ κ * Real.exp (-(r * Real.log N)) := by positivity
    calc Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
        = (Λ n * (N : ℝ) ^ (-(1/2) : ℝ)) * (κ * Real.exp (-(r * Real.log N))) := by
          rw [hexpN, hsplit]; ring
      _ ≤ weilWeight α n * |phi (Real.log n)| :=
          mul_le_mul hw htap h1' (le_trans h0 hw)
  have hpsi : ∑ n ∈ Finset.Ioc (N / 4) N, Λ n
      = Chebyshev.psi (N : ℝ) - Chebyshev.psi ((N : ℝ) / 4) := by
    have hfl : ⌊(N : ℝ) / 4⌋₊ = N / 4 := by
      rw [show ((4:ℝ)) = ((4:ℕ):ℝ) by norm_num, Nat.floor_div_natCast]; simp
    rw [Chebyshev.psi, Chebyshev.psi, hfl, Nat.floor_natCast, eq_sub_iff_add_eq, add_comm]
    exact Finset.sum_Ioc_consecutive _ (by positivity) (Nat.div_le_self N 4)
  have hblock : (N : ℝ) / 4 ≤ ∑ n ∈ Finset.Ioc (N / 4) N, Λ n := by
    rw [hpsi]; exact psi_block_lower hN
  have hstep1 : ∑ n ∈ Finset.Ioc (N / 4) N, Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      ≤ taperedWeilMass phi N α := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    unfold taperedWeilMass
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n _ _ => mul_nonneg (weilWeight_nonneg α n) (abs_nonneg _))
  have hfactor : ∑ n ∈ Finset.Ioc (N / 4) N, Λ n * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      = (∑ n ∈ Finset.Ioc (N / 4) N, Λ n) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) := by
    rw [Finset.sum_mul]
  have hpos : (0:ℝ) ≤ κ * (N : ℝ) ^ (-(1/2) - r : ℝ) := by positivity
  have hlow : (N : ℝ) / 4 * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      ≤ (∑ n ∈ Finset.Ioc (N / 4) N, Λ n) * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ)) :=
    mul_le_mul_of_nonneg_right hblock hpos
  have hcomb : (N : ℝ) / 4 * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
      = κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
    have h1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
    calc (N : ℝ) / 4 * (κ * (N : ℝ) ^ (-(1/2) - r : ℝ))
        = κ / 4 * ((N : ℝ) ^ (1:ℝ) * (N : ℝ) ^ (-(1/2) - r : ℝ)) := by rw [← h1]; ring
      _ = κ / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
          rw [← Real.rpow_add hN0]; congr 2; ring
  rw [← hcomb]
  exact le_trans hlow (hfactor ▸ hstep1)

/-- **Red from the top window alone.**  The verdict of
`taperedWeil_gate_fails_of_subcritical_expDecay`, but assuming the subcritical
lower bound on the taper transform only on `[log N − log 4, log N]`.  Note that
no hypothesis on `α` is needed. -/
theorem taperedWeil_gate_fails_of_topWindow_expDecay {N A : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {phi : ℝ → ℝ} {α t c κ κphi Csrc r : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hκphi : 0 < κphi) (hr0 : 0 ≤ r) (hr : r < 1 / 2)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A)
    (hphi : ∀ u : ℝ, Real.log N - Real.log 4 ≤ u → u ≤ Real.log N →
        κphi * Real.exp (-(r * u)) ≤ |phi u|)
    (hthr : c * (((A : ℝ) + 4) / (1 - 2 * r)) ^ (A + 4)
      ≤ 120000 * (κ * κphi ^ 2 * t ^ 2 / 16)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (taperedWeilMass phi N α) ^ 2)
        < c * (Real.log N) ^ 6) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  set P : ℝ := taperedWeilMass phi N α with hP
  have hlow2 : κphi / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) ≤ P :=
    taperedWeilMass_lower_of_topWindow (α := α) hN hκphi.le hr0 hphi
  have hsq : ((N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 = (N : ℝ) ^ (1 - 2 * r : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ (1 / 2 - r : ℝ)) 2, ← Real.rpow_mul hN0.le]
    congr 1
    push_cast
    ring
  have hPsq : κphi ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ) ≤ P ^ 2 := by
    have h0 : (0 : ℝ) ≤ κphi / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ) := by
      have := Real.rpow_pos_of_pos hN0 (1 / 2 - r : ℝ)
      positivity
    have hmono : (κphi / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 ≤ P ^ 2 := by
      nlinarith [hlow2, h0]
    calc κphi ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)
        = (κphi / 4 * (N : ℝ) ^ (1 / 2 - r : ℝ)) ^ 2 := by rw [mul_pow, hsq]; ring
      _ ≤ P ^ 2 := hmono
  refine gate_fails_of_power_gain (A := A) (δ := 1 - 2 * r) hN hc (by linarith) ?_ hthr
  have ht2 : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have h1 : κ * (κphi ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)) ≤ κ * P ^ 2 :=
    mul_le_mul_of_nonneg_left hPsq hκ.le
  have h2 : κ * P ^ 2 ≤ Csrc * (Real.log N) ^ A * P ^ 2 :=
    mul_le_mul_of_nonneg_right hCsrc (sq_nonneg _)
  calc κ * κphi ^ 2 * t ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)
      = κ * (κphi ^ 2 / 16 * (N : ℝ) ^ (1 - 2 * r : ℝ)) * t ^ 2 := by ring
    _ ≤ Csrc * (Real.log N) ^ A * P ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right (le_trans h1 h2) ht2
    _ = Csrc * (Real.log N) ^ A * (t ^ 2 * P ^ 2) := by ring

/-! ### The verdict for the taper class of the source floor -/

/-- The modulus of the Fourier transform of a real taper, as a real-valued
function of the frequency — this is the function the prime side of the explicit
formula evaluates at the prime frequencies `u = log n`. -/
noncomputable def taperTransformAbs (psi : ℝ → ℝ) (u : ℝ) : ℝ :=
  ‖FourierTransform.fourier (fun x => (psi x : ℂ)) u‖

theorem taperTransformAbs_nonneg (psi : ℝ → ℝ) (u : ℝ) : 0 ≤ taperTransformAbs psi u :=
  norm_nonneg _

/-- **The go/no-go verdict for a compactly supported taper.**  For a compactly
supported continuous taper `ψ` which is somewhere nonzero:

* *no supercritical escape*: the transform of `ψ` admits **no** exponential
  bound `C e^{-a|ξ|}` at any rate `a > 0`, so the only regime in which the
  source-normalization gate could have been green is unavailable to the taper
  class for which the source-side `L⁶` Gram floor is proved;
* *every subcritical regime is red*: whenever the transform stays above
  `κ_φ e^{-ru}` on the **top** frequency window `[log N − log 4, log N]` with a
  rate `r < 1/2`, the contraction condition fails.

This is the formal statement of the taper dichotomy that the previous cycle's
report left as an assessment. -/
theorem compactTaper_gate_verdict {N A : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {psi : ℝ → ℝ} {R : ℝ} (hpsi : CompactTaper psi R) {x₀ : ℝ} (hx₀ : psi x₀ ≠ 0)
    {α t c κ Csrc : ℝ} (hc : 0 < c) (hκ : 0 < κ)
    (hCsrc : κ ≤ Csrc * (Real.log N) ^ A) :
    (¬ ∃ C a : ℝ, 0 < a ∧
        ∀ ξ, taperTransformAbs psi ξ ≤ C * Real.exp (-(a * |ξ|)))
      ∧ (∀ r κphi : ℝ, 0 ≤ r → r < 1 / 2 → 0 < κphi →
          (∀ u : ℝ, Real.log N - Real.log 4 ≤ u → u ≤ Real.log N →
            κphi * Real.exp (-(r * u)) ≤ taperTransformAbs psi u) →
          c * (((A : ℝ) + 4) / (1 - 2 * r)) ^ (A + 4)
              ≤ 120000 * (κ * κphi ^ 2 * t ^ 2 / 16) →
          ¬ (120000 * (Real.log N) ^ 2
              * (Csrc * t ^ 2 * (taperedWeilMass (taperTransformAbs psi) N α) ^ 2)
                < c * (Real.log N) ^ 6)) := by
  constructor
  · exact compactTaper_fourier_not_expDecay hpsi hx₀
  · intro r κphi hr0 hr hκphi hlow hthr
    refine taperedWeil_gate_fails_of_topWindow_expDecay hN hc hκ hκphi hr0 hr hCsrc
      ?_ hthr
    intro u hu huN
    rw [abs_of_nonneg (taperTransformAbs_nonneg psi u)]
    exact hlow u hu huN

end RiemannAnalytic

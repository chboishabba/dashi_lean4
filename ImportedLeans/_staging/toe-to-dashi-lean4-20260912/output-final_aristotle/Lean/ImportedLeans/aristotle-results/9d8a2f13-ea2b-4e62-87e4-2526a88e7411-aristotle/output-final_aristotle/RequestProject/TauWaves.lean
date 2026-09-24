/-
# Smoothing the two fibers of `modular-tau-2-and-3.svg` into waves, and their interference

The picture `visualization/modular-tau-2-and-3.svg` (specified in
`RequestProject/ModularGraph.lean`) plots the Deligne-normalised coefficients
`τ(n)/n^{11/2}` of `Δ = η^24` and colours the fiber of `2` (the points `n = 2^k`) and the fiber
of `3` (the points `n = 3^k`). Along a fiber the plotted points are *not* an arbitrary sequence:
by the Hecke recursion `τ(p^{k+2}) = τ(p) τ(p^{k+1}) - p^{11} τ(p^k)`, the normalised values

```
a_p(k) = τ(p^k) / p^{11k/2}
```

satisfy `a(k+2) = a(1) a(k+1) - a(k)`, the Chebyshev recursion. Writing
`a_p(1)/2 = cos θ_p` (legitimate because Deligne's bound makes `|a_p(1)| < 2`), the solution is

```
a_p(k) = sin((k+1) θ_p) / sin θ_p ,
```

so the discrete fiber is a *sampled sine wave*: the natural smoothing of the fiber of `p` is the
continuous wave `w_p(u) = sin((u+1) θ_p) / sin θ_p`, which passes exactly through every plotted
point of that fiber (`wave_eq_normTau_two`, `wave_eq_normTau_three`).

Two waves of different frequencies interfere. Over the square domain `(u, v)` — `u` the height
along the fiber of `2`, `v` the height along the fiber of `3` — this file defines the four
surfaces drawn in `visualization/modular-tau-waves-3d.svg`:

```
S₂(u,v) = w₂(u),  S₃(u,v) = w₃(v),  S₊(u,v) = w₂(u) + w₃(v),  S₋(u,v) = w₂(u) - w₃(v).
```

Proved here: the interpolation theorems, the recovery identities `S₊ ± S₋ = 2S₂, 2S₃`, the
periods `2π/θ_p`, the amplitude bounds, the nodal locus of the difference view, and the fact
that all four surfaces satisfy one and the same anisotropic Helmholtz equation
`θ₂^{-2} ∂²_u S + θ₃^{-2} ∂²_v S = -S` (`sumSurface_helmholtz`, `diffSurface_helmholtz`).
-/
import RequestProject.ModularGraph

namespace TauWaves

open RamanujanTau Real

set_option autoImplicit false

/-! ## The normalised coefficients along a fiber -/

/-- `p^{11/2}`, the Deligne normalisation of the fiber of `p`. -/
noncomputable def rt (p : ℕ) : ℝ := Real.sqrt ((p : ℝ) ^ 11)

theorem rt_nonneg (p : ℕ) : 0 ≤ rt p := Real.sqrt_nonneg _

theorem rt_sq (p : ℕ) : rt p ^ 2 = (p : ℝ) ^ 11 :=
  Real.sq_sqrt (by positivity)

theorem rt_pos {p : ℕ} (hp : 0 < p) : 0 < rt p := by
  have : (0 : ℝ) < (p : ℝ) ^ 11 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
    positivity
  exact Real.sqrt_pos.2 this

theorem rt_ne_zero {p : ℕ} (hp : 0 < p) : rt p ≠ 0 := (rt_pos hp).ne'

/-- The Deligne-normalised coefficient `τ(p^k)/p^{11k/2}` of the fiber of `p`: exactly the
quantity plotted vertically in `modular-tau-2-and-3.svg` at the point `n = p^k`. -/
noncomputable def normTau (p k : ℕ) : ℝ := (tau (p ^ k) : ℝ) / rt p ^ k

theorem normTau_zero (p : ℕ) : normTau p 0 = 1 := by
  simp [normTau, RamanujanTau.tau_one]

theorem normTau_one (p : ℕ) : normTau p 1 = (tau p : ℝ) / rt p := by
  simp [normTau]

/-- The square of the normalised coefficient is the quantity `plotValueSq` of the two-dimensional
picture: the smooth waves below live over the very same graph. -/
theorem normTau_sq_eq_plotValueSq {p k : ℕ} (hp : 0 < p) :
    normTau p k ^ 2 = (ModularGraph.plotValueSq (p ^ k) : ℝ) := by
  have hrt : rt p ≠ 0 := rt_ne_zero hp
  have hcast : ((p : ℝ)) ^ 11 = rt p ^ 2 := (rt_sq p).symm
  have hkey : (rt p ^ k) ^ 2 = (p : ℝ) ^ (11 * k) := by
    rw [← pow_mul, mul_comm k 2, pow_mul, rt_sq, ← pow_mul]
  rw [normTau, ModularGraph.plotValueSq]
  push_cast
  rw [div_pow, hkey, ← pow_mul, mul_comm k 11]

/-! ## The Satake angle -/

/-- The Satake parameter `cos θ_p = τ(p) / (2 p^{11/2})`: half the first normalised
coefficient. -/
noncomputable def satakeCos (p : ℕ) : ℝ := (tau p : ℝ) / (2 * rt p)

/-- The Satake angle `θ_p = arccos (τ(p) / 2p^{11/2})`, the angular frequency of the wave that
smooths the fiber of `p`. -/
noncomputable def theta (p : ℕ) : ℝ := Real.arccos (satakeCos p)

theorem cos_theta {p : ℕ} (h : |satakeCos p| ≤ 1) : Real.cos (theta p) = satakeCos p :=
  Real.cos_arccos (abs_le.1 h).1 (abs_le.1 h).2

theorem sin_theta_pos {p : ℕ} (h : |satakeCos p| < 1) : 0 < Real.sin (theta p) := by
  rw [theta, Real.sin_arccos]
  have : satakeCos p ^ 2 < 1 := by
    have := abs_lt.1 h
    nlinarith [this.1, this.2]
  exact Real.sqrt_pos.2 (by linarith)

/-- Deligne's bound at `p = 2`: `|τ(2)| < 2 · 2^{11/2}`. -/
theorem abs_satakeCos_two_lt_one : |satakeCos 2| < 1 := by
  have h48 : (48 : ℝ) < rt 2 * 2 := by
    have : (24 : ℝ) < rt 2 := by
      rw [rt, show ((2 : ℕ) : ℝ) ^ 11 = 2048 by norm_num]
      have : Real.sqrt 576 < Real.sqrt 2048 := by
        apply Real.sqrt_lt_sqrt <;> norm_num
      rwa [show (576 : ℝ) = 24 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
    linarith
  have hpos : (0 : ℝ) < 2 * rt 2 := by linarith
  rw [satakeCos, RamanujanTau.tau_two, abs_div, abs_of_pos hpos, div_lt_one hpos]
  simp only [Int.cast_neg, Int.cast_ofNat, abs_neg]
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24)]
  linarith

/-- Deligne's bound at `p = 3`: `|τ(3)| < 2 · 3^{11/2}`. -/
theorem abs_satakeCos_three_lt_one : |satakeCos 3| < 1 := by
  have h : (252 : ℝ) < rt 3 := by
    rw [rt, show ((3 : ℕ) : ℝ) ^ 11 = 177147 by norm_num]
    have : Real.sqrt 63504 < Real.sqrt 177147 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    rwa [show (63504 : ℝ) = 252 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
  have hpos : (0 : ℝ) < 2 * rt 3 := by linarith
  rw [satakeCos, RamanujanTau.tau_three, abs_div, abs_of_pos hpos, div_lt_one hpos]
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ ((252 : ℤ) : ℝ))]
  push_cast
  linarith

/-! ## The smooth wave -/

/-- The smoothing of the fiber of `p`: the wave `w_p(u) = sin((u+1)θ_p)/sin θ_p` of angular
frequency `θ_p`. It is the unique solution of the Chebyshev recursion in continuous form; at
integer heights `u = k` it reproduces the plotted point `τ(p^k)/p^{11k/2}`. -/
noncomputable def wave (p : ℕ) (u : ℝ) : ℝ :=
  Real.sin ((u + 1) * theta p) / Real.sin (theta p)

theorem wave_zero {p : ℕ} (h : |satakeCos p| < 1) : wave p 0 = 1 := by
  have hs := (sin_theta_pos h).ne'
  simp [wave, div_self hs]

theorem wave_one {p : ℕ} (h : |satakeCos p| < 1) : wave p 1 = 2 * satakeCos p := by
  have hs := (sin_theta_pos h).ne'
  have h2 : ((1 : ℝ) + 1) * theta p = 2 * theta p := by ring
  rw [wave, h2, Real.sin_two_mul, cos_theta h.le]
  field_simp

/-- The three-term recursion satisfied by the wave in the continuous variable:
`w(u+2) = 2cos θ · w(u+1) - w(u)`. -/
theorem wave_rec {p : ℕ} (h : |satakeCos p| < 1) (u : ℝ) :
    wave p (u + 2) = 2 * satakeCos p * wave p (u + 1) - wave p u := by
  have hs := (sin_theta_pos h).ne'
  have key : Real.sin ((u + 2 + 1) * theta p)
      = 2 * Real.cos (theta p) * Real.sin ((u + 1 + 1) * theta p)
        - Real.sin ((u + 1) * theta p) := by
    have e1 : (u + 2 + 1) * theta p = (u + 1 + 1) * theta p + theta p := by ring
    have e2 : (u + 1) * theta p = (u + 1 + 1) * theta p - theta p := by ring
    rw [e1, e2, Real.sin_add, Real.sin_sub]
    ring
  rw [wave, wave, wave, key, cos_theta h.le]
  field_simp

/-- The wave has period `2π/θ_p` in the height. -/
theorem wave_periodic {p : ℕ} (h : |satakeCos p| < 1) (u : ℝ) :
    wave p (u + 2 * π / theta p) = wave p u := by
  have hθ : theta p ≠ 0 := by
    intro h0
    have := sin_theta_pos h
    rw [h0, Real.sin_zero] at this
    exact lt_irrefl _ this
  have e : (u + 2 * π / theta p + 1) * theta p = (u + 1) * theta p + 2 * π := by
    field_simp
    ring
  rw [wave, wave, e, Real.sin_add_two_pi]

/-- The wave is bounded by `1/sin θ_p`: the amplitude of the fiber's wave. -/
theorem abs_wave_le {p : ℕ} (h : |satakeCos p| < 1) (u : ℝ) :
    |wave p u| ≤ 1 / Real.sin (theta p) := by
  have hs := sin_theta_pos h
  rw [wave, abs_div, abs_of_pos hs, div_le_div_iff_of_pos_right hs]
  exact Real.abs_sin_le_one _

/-! ## The wave interpolates the plotted points -/

/-- The normalised coefficients along the fiber of `p` obey the Chebyshev recursion
`a(k+2) = a(1) a(k+1) - a(k)`, an immediate consequence of the Hecke recursion. -/
theorem normTau_rec {p k : ℕ} (hp : 0 < p)
    (hrec : tau (p ^ (k + 2)) = tau p * tau (p ^ (k + 1)) - (p : ℤ) ^ 11 * tau (p ^ k)) :
    normTau p (k + 2) = normTau p 1 * normTau p (k + 1) - normTau p k := by
  have hrt : rt p ≠ 0 := rt_ne_zero hp
  have hsq : rt p ^ 2 = (p : ℝ) ^ 11 := rt_sq p
  have hcast : ((tau (p ^ (k + 2)) : ℤ) : ℝ)
      = (tau p : ℝ) * (tau (p ^ (k + 1)) : ℝ) - (p : ℝ) ^ 11 * (tau (p ^ k) : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hrec
  rw [normTau, normTau, normTau, normTau, hcast, ← hsq]
  field_simp
  ring_nf

/-- **The wave passes through the plotted points.** If the Hecke recursion is available along the
fiber of `p` up to height `K`, then the smooth wave `w_p` agrees at every integer height `k ≤ K`
with the plotted normalised coefficient `τ(p^k)/p^{11k/2}`. -/
theorem wave_eq_normTau {p K : ℕ} (hp : 0 < p) (h : |satakeCos p| < 1)
    (hrec : ∀ k, k + 2 ≤ K →
      tau (p ^ (k + 2)) = tau p * tau (p ^ (k + 1)) - (p : ℤ) ^ 11 * tau (p ^ k)) :
    ∀ k ≤ K, wave p (k : ℝ) = normTau p k := by
  have hrt : rt p ≠ 0 := rt_ne_zero hp
  have h1 : wave p (1 : ℝ) = normTau p 1 := by
    rw [wave_one h, normTau_one, satakeCos]
    field_simp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => intro _; rw [Nat.cast_zero, wave_zero h, normTau_zero]
    | 1 => intro _; simpa using h1
    | (j + 2) =>
      intro hk
      have hj1 : wave p ((j : ℝ) + 1) = normTau p (j + 1) := by
        have := ih (j + 1) (by omega) (by omega)
        push_cast at this ⊢
        exact this
      have hj0 : wave p (j : ℝ) = normTau p j := ih j (by omega) (by omega)
      have hcast : ((j : ℕ) : ℝ) + 2 = ((j + 2 : ℕ) : ℝ) := by push_cast; ring
      have := wave_rec h (j : ℝ)
      rw [hcast, hj1, hj0] at this
      rw [this, normTau_rec hp (hrec j (by omega)), normTau_one, satakeCos]
      field_simp

/-- The red curve of `modular-tau-2-and-3.svg`: the wave of frequency `θ₂` passes through all
nine plotted points `2^k ≤ 256` of the fiber of `2`. -/
theorem wave_eq_normTau_two : ∀ k : ℕ, k ≤ 8 → wave 2 (k : ℝ) = normTau 2 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_two_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 2) ?_ ?_
  · decide
  · have : (2 : ℕ) ^ (k + 2) ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-- The blue curve of `modular-tau-2-and-3.svg`: the wave of frequency `θ₃` passes through all
six plotted points `3^k ≤ 256` of the fiber of `3`. -/
theorem wave_eq_normTau_three : ∀ k : ℕ, k ≤ 5 → wave 3 (k : ℝ) = normTau 3 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_three_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 3) ?_ ?_
  · decide
  · have : (3 : ℕ) ^ (k + 2) ≤ 3 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-! ## The four surfaces -/

/-- View 1: the fiber of `2` as a surface, constant in `v`. -/
noncomputable def twoSurface (u _v : ℝ) : ℝ := wave 2 u

/-- View 2: the fiber of `3` as a surface, constant in `u`. -/
noncomputable def threeSurface (_u v : ℝ) : ℝ := wave 3 v

/-- View 3: constructive interference of the two fibers. -/
noncomputable def sumSurface (u v : ℝ) : ℝ := wave 2 u + wave 3 v

/-- View 4: destructive interference of the two fibers. -/
noncomputable def diffSurface (u v : ℝ) : ℝ := wave 2 u - wave 3 v

/-- The two interference views recover the fiber of `2`. -/
theorem sum_add_diff (u v : ℝ) : sumSurface u v + diffSurface u v = 2 * twoSurface u v := by
  simp [sumSurface, diffSurface, twoSurface]; ring

/-- The two interference views recover the fiber of `3`. -/
theorem sum_sub_diff (u v : ℝ) : sumSurface u v - diffSurface u v = 2 * threeSurface u v := by
  simp [sumSurface, diffSurface, threeSurface]; ring

/-- The interference surfaces are doubly periodic: a lattice of periods `2π/θ₂` and `2π/θ₃`. -/
theorem sumSurface_periodic (u v : ℝ) :
    sumSurface (u + 2 * π / theta 2) (v + 2 * π / theta 3) = sumSurface u v := by
  rw [sumSurface, sumSurface, wave_periodic abs_satakeCos_two_lt_one,
    wave_periodic abs_satakeCos_three_lt_one]

theorem diffSurface_periodic (u v : ℝ) :
    diffSurface (u + 2 * π / theta 2) (v + 2 * π / theta 3) = diffSurface u v := by
  rw [diffSurface, diffSurface, wave_periodic abs_satakeCos_two_lt_one,
    wave_periodic abs_satakeCos_three_lt_one]

/-- The height of the interference views never exceeds the sum of the two amplitudes. -/
theorem abs_sumSurface_le (u v : ℝ) :
    |sumSurface u v| ≤ 1 / Real.sin (theta 2) + 1 / Real.sin (theta 3) :=
  (abs_add_le _ _).trans (add_le_add (abs_wave_le abs_satakeCos_two_lt_one u)
    (abs_wave_le abs_satakeCos_three_lt_one v))

theorem abs_diffSurface_le (u v : ℝ) :
    |diffSurface u v| ≤ 1 / Real.sin (theta 2) + 1 / Real.sin (theta 3) :=
  (abs_sub _ _).trans (add_le_add (abs_wave_le abs_satakeCos_two_lt_one u)
    (abs_wave_le abs_satakeCos_three_lt_one v))

/-- The nodal set of the difference view — the curves along which the two fibers cancel
exactly — is where the two waves take the same value. -/
theorem diffSurface_eq_zero_iff (u v : ℝ) : diffSurface u v = 0 ↔ wave 2 u = wave 3 v := by
  rw [diffSurface, sub_eq_zero]

/-- At integer heights the difference view is the difference of two *plotted* points of
`modular-tau-2-and-3.svg`. -/
theorem diffSurface_natCast {j k : ℕ} (hj : j ≤ 8) (hk : k ≤ 5) :
    diffSurface (j : ℝ) (k : ℝ) = normTau 2 j - normTau 3 k := by
  rw [diffSurface, wave_eq_normTau_two j hj, wave_eq_normTau_three k hk]

theorem sumSurface_natCast {j k : ℕ} (hj : j ≤ 8) (hk : k ≤ 5) :
    sumSurface (j : ℝ) (k : ℝ) = normTau 2 j + normTau 3 k := by
  rw [sumSurface, wave_eq_normTau_two j hj, wave_eq_normTau_three k hk]

/-! ## All four views solve the same wave equation -/

theorem hasDerivAt_wave (p : ℕ) (u : ℝ) :
    HasDerivAt (wave p)
      (theta p * Real.cos ((u + 1) * theta p) / Real.sin (theta p)) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u + 1) * theta p) (theta p) u := by
    simpa using ((hasDerivAt_id u).add_const (1 : ℝ)).mul_const (theta p)
  have h2 := (Real.hasDerivAt_sin ((u + 1) * theta p)).comp u h1
  simpa [wave, mul_comm, mul_div_assoc] using h2.div_const (Real.sin (theta p))

/-- The derivative of the wave, as a function. -/
noncomputable def waveDeriv (p : ℕ) (u : ℝ) : ℝ :=
  theta p * Real.cos ((u + 1) * theta p) / Real.sin (theta p)

theorem deriv_wave (p : ℕ) (u : ℝ) : deriv (wave p) u = waveDeriv p u :=
  (hasDerivAt_wave p u).deriv

theorem hasDerivAt_waveDeriv (p : ℕ) (u : ℝ) :
    HasDerivAt (waveDeriv p) (-(theta p ^ 2) * wave p u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u + 1) * theta p) (theta p) u := by
    simpa using ((hasDerivAt_id u).add_const (1 : ℝ)).mul_const (theta p)
  have h2 := (Real.hasDerivAt_cos ((u + 1) * theta p)).comp u h1
  have h3 := (h2.const_mul (theta p)).div_const (Real.sin (theta p))
  refine (show HasDerivAt (waveDeriv p) _ u from h3).congr_deriv ?_
  rw [wave]
  ring

theorem deriv_deriv_wave (p : ℕ) (u : ℝ) :
    deriv (deriv (wave p)) u = -(theta p ^ 2) * wave p u := by
  have : deriv (wave p) = waveDeriv p := funext fun x => deriv_wave p x
  rw [this]
  exact (hasDerivAt_waveDeriv p u).deriv

theorem theta_two_ne_zero : theta 2 ≠ 0 := by
  intro h0
  have := sin_theta_pos abs_satakeCos_two_lt_one
  rw [h0, Real.sin_zero] at this
  exact lt_irrefl _ this

theorem theta_three_ne_zero : theta 3 ≠ 0 := by
  intro h0
  have := sin_theta_pos abs_satakeCos_three_lt_one
  rw [h0, Real.sin_zero] at this
  exact lt_irrefl _ this

/-- **The interference view is a standing wave.** The constructive view satisfies the
anisotropic Helmholtz equation `θ₂^{-2} ∂²_u S + θ₃^{-2} ∂²_v S = -S`. -/
theorem sumSurface_helmholtz (u v : ℝ) :
    deriv (deriv (fun x => sumSurface x v)) u / theta 2 ^ 2
      + deriv (deriv (fun y => sumSurface u y)) v / theta 3 ^ 2
      = -sumSurface u v := by
  have e1 : (fun x => sumSurface x v) = fun x => wave 2 x + wave 3 v := rfl
  have e2 : (fun y => sumSurface u y) = fun y => wave 2 u + wave 3 y := rfl
  have d1 : deriv (deriv (fun x => sumSurface x v)) u = -(theta 2 ^ 2) * wave 2 u := by
    rw [e1]
    have : deriv (fun x => wave 2 x + wave 3 v) = deriv (wave 2) := by
      funext x
      exact deriv_add_const _
    rw [this, deriv_deriv_wave]
  have d2 : deriv (deriv (fun y => sumSurface u y)) v = -(theta 3 ^ 2) * wave 3 v := by
    rw [e2]
    have : deriv (fun y => wave 2 u + wave 3 y) = deriv (wave 3) := by
      funext y
      exact deriv_const_add _
    rw [this, deriv_deriv_wave]
  have h2 := theta_two_ne_zero
  have h3 := theta_three_ne_zero
  rw [d1, d2, sumSurface]
  field_simp
  ring

/-- The destructive view satisfies the same equation: the four panels are four solutions of one
wave equation. -/
theorem diffSurface_helmholtz (u v : ℝ) :
    deriv (deriv (fun x => diffSurface x v)) u / theta 2 ^ 2
      + deriv (deriv (fun y => diffSurface u y)) v / theta 3 ^ 2
      = -diffSurface u v := by
  have d1 : deriv (deriv (fun x => diffSurface x v)) u = -(theta 2 ^ 2) * wave 2 u := by
    have e1 : (fun x => diffSurface x v) = fun x => wave 2 x + (-wave 3 v) := by
      funext x; simp [diffSurface, sub_eq_add_neg]
    rw [e1]
    have : deriv (fun x => wave 2 x + (-wave 3 v)) = deriv (wave 2) := by
      funext x
      exact deriv_add_const _
    rw [this, deriv_deriv_wave]
  have d2 : deriv (deriv (fun y => diffSurface u y)) v = (theta 3 ^ 2) * wave 3 v := by
    have e2 : (fun y => diffSurface u y) = fun y => wave 2 u + (-(wave 3 y)) := by
      funext y; simp [diffSurface, sub_eq_add_neg]
    rw [e2]
    have h1 : deriv (fun y => wave 2 u + (-(wave 3 y))) = fun y => -(waveDeriv 3 y) := by
      funext y
      rw [deriv_const_add]
      simpa [waveDeriv] using ((hasDerivAt_wave 3 y).neg).deriv
    rw [h1]
    have h2 : HasDerivAt (fun y => -(waveDeriv 3 y)) (theta 3 ^ 2 * wave 3 v) v := by
      simpa using (hasDerivAt_waveDeriv 3 v).neg
    exact h2.deriv
  have h2 := theta_two_ne_zero
  have h3 := theta_three_ne_zero
  rw [d1, d2, diffSurface]
  field_simp
  ring

/-- The two pure views are the interference views' averages, and they solve the same equation
with the other variable's term absent. -/
theorem twoSurface_helmholtz (u v : ℝ) :
    deriv (deriv (fun x => twoSurface x v)) u / theta 2 ^ 2
      + deriv (deriv (fun y => twoSurface u y)) v / theta 3 ^ 2
      = -twoSurface u v := by
  have d1 : deriv (deriv (fun x => twoSurface x v)) u = -(theta 2 ^ 2) * wave 2 u :=
    deriv_deriv_wave 2 u
  have d2 : deriv (deriv (fun y => twoSurface u y)) v = 0 := by
    simp [twoSurface]
  have h2 := theta_two_ne_zero
  rw [d1, d2, zero_div, add_zero, twoSurface]
  field_simp

theorem threeSurface_helmholtz (u v : ℝ) :
    deriv (deriv (fun x => threeSurface x v)) u / theta 2 ^ 2
      + deriv (deriv (fun y => threeSurface u y)) v / theta 3 ^ 2
      = -threeSurface u v := by
  have d1 : deriv (deriv (fun x => threeSurface x v)) u = 0 := by simp [threeSurface]
  have d2 : deriv (deriv (fun y => threeSurface u y)) v = -(theta 3 ^ 2) * wave 3 v :=
    deriv_deriv_wave 3 v
  have h3 := theta_three_ne_zero
  rw [d1, d2, zero_div, zero_add, threeSurface]
  field_simp

end TauWaves

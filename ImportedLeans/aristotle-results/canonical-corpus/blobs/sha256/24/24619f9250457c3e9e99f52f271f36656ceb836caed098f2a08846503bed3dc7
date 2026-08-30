import Mathlib
import RequestProject.DeltaGraph

/-!
# The vertical walls: why the phase portrait stands straight up over `x = 0, ±1/2, ±1`

The domain picture of `Δ` (`paper/delta_domain.svg`, and every plate derived from it) has a
visible feature that the periodicity `Δ(z+1) = Δ(z)` alone does not explain: right above the
cusps `x = 0, ±1/2, ±1` the colour boundaries and the brightness bands run *exactly* vertically.
This file proves that this is forced, and that it is forced by two things only:

* the coefficients of the `q`-expansion are **real**, and
* the expansion has **period one**.

Nothing else about `Δ` is used. So the statements are made for an arbitrary real coefficient
sequence `c : ℕ → ℝ` and the truncated expansion

`F c N (z) = ∑_{n=1}^{N} c(n) q(z)ⁿ`,  `q(z) = e^{2πiz}`,

of which `DeltaGraph.deltaApprox` is the case `c = τ` (`deltaApprox_eq_F`).

## The theory, in five steps

1. **Reflection.** `qParam_neg_conj`, `F_neg_conj`: real coefficients give
   `F(-z̄) = conj F(z)` — Schwarz reflection across the imaginary axis. Combined with period one
   (`F_int_add`) this becomes one mirror per half-integer: `F_mirror`, `F(k - z̄) = conj F(z)`
   for every `k : ℤ`. The fixed line of `z ↦ k - z̄` is `x = k/2` (`mirror_fixed_iff`): the walls
   are the lines `x = 0, ±1/2, ±1, …`, and no others (`qParam_im_eq_zero_iff`).

2. **On a wall the function is real.** `qParam_wall` says `q(k/2 + iy) = (-1)^k e^{-2πy}` is
   real, so `F_wall_ofReal`, `F_wall_im`: `F` is real on each wall, and the phase is locked:
   `arg_F_wall` gives `arg F ∈ {0, π}` at every wall point, with `arg_F_wall_eq_zero_iff` and
   `arg_F_wall_eq_pi_iff` saying which.

3. **The phase cannot drift.** `phase_locked_of_ne_zero`: on a segment of a wall on which `F`
   does not vanish the phase is *constant* — a colour boundary can only meet a wall at a zero,
   never by slanting through it. (Intermediate value theorem: a change of phase on a wall is a
   change of sign of a real continuous function.)

4. **The magnitude has no horizontal gradient on a wall.** `normSq_mirror` makes
   `x ↦ |F(x+iy)|²` an even function about `x = k/2`; `deriv_normSq_wall`, `deriv_norm_wall` and
   `fderiv_normSq_wall_horizontal` then give `∂ₓ|F|² = 0` and `∂ₓ|F| = 0` there.

5. **Hence the contours are perpendicular.** `grad_normSq_wall_vertical`: the gradient of `|F|²`
   at a wall point is a vertical vector `(0, ∂_y)`. Since the level curves of `|F|` are
   orthogonal to the gradient, they cross the wall horizontally, i.e. at exactly `90°`
   (`grad_normSq_wall_inner_horizontal`).

## For `Δ` itself

`deltaApprox_wall_pos` and `deltaApprox_wall_neg`: high enough up (`y ≥ 5` is more than enough
for the plotted `N = 30`) the even walls `x = 0, ±1` carry phase exactly `0` and the odd walls
`x = ±1/2` carry phase exactly `π` — the two colours that meet at the cusps in the picture.
-/

namespace VerticalWalls

open Complex DeltaGraph

noncomputable section

/-! ## The truncated expansion with real coefficients -/

/-- `F c N (z) = ∑_{n=1}^{N} c(n) q(z)ⁿ` with `q = e^{2πiz}`: the function actually plotted, for
an arbitrary *real* coefficient sequence. -/
def F (c : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (c (n + 1) : ℂ) * qParam z ^ (n + 1)

/-- The same sum with a real argument in place of `q`. -/
def Fr (c : ℕ → ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range N, c (n + 1) * r ^ (n + 1)

/-- The plotted approximation of `Δ` is the case `c = τ`. -/
theorem deltaApprox_eq_F (N : ℕ) (z : ℂ) :
    deltaApprox N z = F (fun n => (tau n : ℝ)) N z := by
  simp [deltaApprox, F]

/-- Where `q` is real, `F` is the real polynomial `Fr` in it. -/
theorem F_ofReal {c : ℕ → ℝ} {N : ℕ} {z : ℂ} {r : ℝ} (h : qParam z = (r : ℂ)) :
    F c N z = (Fr c N r : ℂ) := by
  simp [F, Fr, h]

/-! ## Step 1: reflection -/

/-- `q(-z̄) = conj q(z)`. -/
theorem qParam_neg_conj (z : ℂ) :
    qParam (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (qParam z) := by
  rw [qParam, qParam, ← Complex.exp_conj]
  congr 1
  simp [Complex.ext_iff]

/-- `q(z + k) = q(z)` for every integer `k`. -/
theorem qParam_int_add (z : ℂ) (k : ℤ) : qParam (z + k) = qParam z := by
  have h : (2 : ℂ) * Real.pi * Complex.I * (z + k)
      = 2 * Real.pi * Complex.I * z + (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [qParam, qParam, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Schwarz reflection across the imaginary axis.** Because the coefficients are real,
`F(-z̄) = conj F(z)`. -/
theorem F_neg_conj (c : ℕ → ℝ) (N : ℕ) (z : ℂ) :
    F c N (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (F c N z) := by
  simp only [F, map_sum, map_mul, map_pow, qParam_neg_conj, Complex.conj_ofReal]

/-- **Period one**, in integer form. -/
theorem F_int_add (c : ℕ → ℝ) (N : ℕ) (z : ℂ) (k : ℤ) : F c N (z + k) = F c N z := by
  simp [F, qParam_int_add]

/-- **One mirror for every half-integer.** For every `k : ℤ`, reflection in the vertical line
`x = k/2` conjugates `F`. This is reflection (step 1) composed with `k` translations. -/
theorem F_mirror (c : ℕ → ℝ) (N : ℕ) (z : ℂ) (k : ℤ) :
    F c N ((k : ℂ) - (starRingEnd ℂ) z) = (starRingEnd ℂ) (F c N z) := by
  have h : (k : ℂ) - (starRingEnd ℂ) z = -(starRingEnd ℂ) z + (k : ℂ) := by ring
  rw [h, F_int_add, F_neg_conj]

/-- The mirror `z ↦ k - z̄` fixes exactly the vertical line `x = k/2`. -/
theorem mirror_fixed_iff (z : ℂ) (k : ℤ) :
    (k : ℂ) - (starRingEnd ℂ) z = z ↔ z.re = (k : ℝ) / 2 := by
  simp [Complex.ext_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The walls, and nothing else.** `q(z)` is real exactly on the vertical lines
`x ∈ (1/2)ℤ`, i.e. `x = 0, ±1/2, ±1, …`. -/
theorem qParam_im_eq_zero_iff (z : ℂ) :
    (qParam z).im = 0 ↔ ∃ k : ℤ, z.re = (k : ℝ) / 2 := by
  have him : (2 * Real.pi * Complex.I * z).im = 2 * Real.pi * z.re := by
    simp [Complex.mul_re, Complex.mul_im]
  have hq : (qParam z).im
      = Real.exp ((2 * Real.pi * Complex.I * z).re) * Real.sin (2 * Real.pi * z.re) := by
    rw [qParam, Complex.exp_im, him]
  rw [hq, mul_eq_zero]
  have hpos : Real.exp ((2 * Real.pi * Complex.I * z).re) ≠ 0 := Real.exp_ne_zero _
  simp only [hpos, false_or]
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hn ⊢
    nlinarith [hn]
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [hn]; ring⟩

/-! ## Step 2: on a wall the function is real -/

/-- The point `k/2 + iy` of the wall `x = k/2`. -/
def wallPt (k : ℤ) (y : ℝ) : ℂ := ((k : ℝ) / 2 : ℝ) + (y : ℝ) * Complex.I

@[simp] theorem wallPt_re (k : ℤ) (y : ℝ) : (wallPt k y).re = (k : ℝ) / 2 := by
  simp [wallPt]

@[simp] theorem wallPt_im (k : ℤ) (y : ℝ) : (wallPt k y).im = y := by
  simp [wallPt]

/-- **On a wall the nome is real**: `q(k/2 + iy) = (-1)^k e^{-2πy}`. -/
theorem qParam_wall (k : ℤ) (y : ℝ) :
    qParam (wallPt k y) = (((-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y)) : ℝ) : ℂ) := by
  have h : (2 : ℂ) * Real.pi * Complex.I * wallPt k y
      = (k : ℂ) * (Real.pi * Complex.I) + ((-(2 * Real.pi * y) : ℝ) : ℂ) := by
    simp [wallPt]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [qParam, h, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I,
    ← Complex.ofReal_exp]
  push_cast
  ring

/-- **`F` is real on every wall.** -/
theorem F_wall_ofReal (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    F c N (wallPt k y) = ((Fr c N ((-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y))) : ℝ) : ℂ) :=
  F_ofReal (qParam_wall k y)

/-- The imaginary part of `F` vanishes identically on every wall. -/
theorem F_wall_im (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) : (F c N (wallPt k y)).im = 0 := by
  rw [F_wall_ofReal]; simp

/-- **The phase is locked to `0` or `π` all the way up a wall.** -/
theorem arg_F_wall (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    (F c N (wallPt k y)).arg = 0 ∨ (F c N (wallPt k y)).arg = Real.pi := by
  rcases le_or_gt 0 (F c N (wallPt k y)).re with h | h
  · exact Or.inl (Complex.arg_eq_zero_iff.2 ⟨h, F_wall_im c N k y⟩)
  · exact Or.inr (Complex.arg_eq_pi_iff.2 ⟨h, F_wall_im c N k y⟩)

theorem arg_F_wall_eq_zero_iff (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    (F c N (wallPt k y)).arg = 0 ↔ 0 ≤ (F c N (wallPt k y)).re :=
  ⟨fun h => (Complex.arg_eq_zero_iff.1 h).1,
   fun h => Complex.arg_eq_zero_iff.2 ⟨h, F_wall_im c N k y⟩⟩

theorem arg_F_wall_eq_pi_iff (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    (F c N (wallPt k y)).arg = Real.pi ↔ (F c N (wallPt k y)).re < 0 :=
  ⟨fun h => (Complex.arg_eq_pi_iff.1 h).1,
   fun h => Complex.arg_eq_pi_iff.2 ⟨h, F_wall_im c N k y⟩⟩

/-! ## Step 3: the phase cannot drift along a wall -/

/-- Along a wall, `F` is a continuous *real* function of the height. -/
theorem continuous_F_wall_re (c : ℕ → ℝ) (N : ℕ) (k : ℤ) :
    Continuous fun y : ℝ => (F c N (wallPt k y)).re := by
  have : (fun y : ℝ => (F c N (wallPt k y)).re)
      = fun y : ℝ => Fr c N ((-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y))) := by
    funext y; rw [F_wall_ofReal]; simp
  rw [this]
  unfold Fr
  fun_prop

/-- **No drift.** If `F` has no zero on a segment of a wall then its phase is constant on that
segment: the colour cannot change without passing through a zero, so a colour boundary meets a
wall vertically or not at all. -/
theorem phase_locked_of_ne_zero (c : ℕ → ℝ) (N : ℕ) (k : ℤ) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Set.Icc a b, F c N (wallPt k y) ≠ 0) :
    (F c N (wallPt k a)).arg = (F c N (wallPt k b)).arg := by
  set g : ℝ → ℝ := fun y => (F c N (wallPt k y)).re with hg
  have hne : ∀ y ∈ Set.Icc a b, g y ≠ 0 := by
    intro y hy hzero
    exact h y hy (Complex.ext hzero (F_wall_im c N k y))
  have hcont : ContinuousOn g (Set.Icc a b) := (continuous_F_wall_re c N k).continuousOn
  have hsame : (0 < g a ∧ 0 < g b) ∨ (g a < 0 ∧ g b < 0) := by
    rcases lt_trichotomy (g a) 0 with ha | ha | ha
    · rcases lt_trichotomy (g b) 0 with hb | hb | hb
      · exact Or.inr ⟨ha, hb⟩
      · exact absurd hb (hne b ⟨hab, le_refl b⟩)
      · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc hab hcont
          (Set.mem_Icc.2 ⟨le_of_lt ha, le_of_lt hb⟩)
        exact absurd hy0 (hne y hy)
    · exact absurd ha (hne a ⟨le_refl a, hab⟩)
    · rcases lt_trichotomy (g b) 0 with hb | hb | hb
      · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' hab hcont
          (Set.mem_Icc.2 ⟨le_of_lt hb, le_of_lt ha⟩)
        exact absurd hy0 (hne y hy)
      · exact absurd hb (hne b ⟨hab, le_refl b⟩)
      · exact Or.inl ⟨ha, hb⟩
  rcases hsame with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [(arg_F_wall_eq_zero_iff c N k a).2 ha.le, (arg_F_wall_eq_zero_iff c N k b).2 hb.le]
  · rw [(arg_F_wall_eq_pi_iff c N k a).2 ha, (arg_F_wall_eq_pi_iff c N k b).2 hb]

/-! ## Step 4: the magnitude has no horizontal gradient on a wall -/

/-- The reflection identity written out on a horizontal slice: the picture at height `y` is
symmetric about `x = k/2`. -/
theorem F_mirror_slice (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (x y : ℝ) :
    F c N (((k : ℝ) - x : ℝ) + (y : ℝ) * Complex.I)
      = (starRingEnd ℂ) (F c N ((x : ℝ) + (y : ℝ) * Complex.I)) := by
  have h : ((((k : ℝ) - x : ℝ) : ℂ) + (y : ℝ) * Complex.I)
      = (k : ℂ) - (starRingEnd ℂ) (((x : ℝ) : ℂ) + (y : ℝ) * Complex.I) := by
    simp [Complex.ext_iff]
  rw [h, F_mirror]

/-- `|F|` is an even function of `x` about each wall. -/
theorem norm_F_mirror_slice (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (x y : ℝ) :
    ‖F c N (((k : ℝ) - x : ℝ) + (y : ℝ) * Complex.I)‖
      = ‖F c N ((x : ℝ) + (y : ℝ) * Complex.I)‖ := by
  rw [F_mirror_slice]; simp

/-- The squared magnitude on a horizontal slice, as a real function of `x`. -/
def sqAbs (c : ℕ → ℝ) (N : ℕ) (y : ℝ) (x : ℝ) : ℝ :=
  Complex.normSq (F c N ((x : ℝ) + (y : ℝ) * Complex.I))

theorem sqAbs_mirror (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) (x : ℝ) :
    sqAbs c N y (2 * ((k : ℝ) / 2) - x) = sqAbs c N y x := by
  have h : 2 * ((k : ℝ) / 2) - x = (k : ℝ) - x := by ring
  rw [sqAbs, sqAbs, h, F_mirror_slice, Complex.normSq_conj]

theorem sqAbs_wall (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    sqAbs c N y ((k : ℝ) / 2) = Complex.normSq (F c N (wallPt k y)) := by
  rfl

theorem differentiable_F (c : ℕ → ℝ) (N : ℕ) : Differentiable ℂ (F c N) := by
  unfold F qParam
  fun_prop

theorem differentiable_slice (c : ℕ → ℝ) (N : ℕ) (y : ℝ) :
    Differentiable ℝ fun x : ℝ => F c N ((x : ℝ) + (y : ℝ) * Complex.I) := by
  have h1 : Differentiable ℝ fun x : ℝ => ((x : ℝ) : ℂ) + (y : ℝ) * Complex.I :=
    (Complex.ofRealCLM.differentiable).add (differentiable_const _)
  exact ((differentiable_F c N).restrictScalars ℝ).comp h1

theorem differentiable_sqAbs (c : ℕ → ℝ) (N : ℕ) (y : ℝ) : Differentiable ℝ (sqAbs c N y) := by
  have hc := differentiable_slice c N y
  have hre := Complex.reCLM.differentiable.comp hc
  have him := Complex.imCLM.differentiable.comp hc
  have := (hre.mul hre).add (him.mul him)
  simpa only [sqAbs, Complex.normSq_apply, Function.comp] using this

/-- Derivative of a function with a mirror symmetry about `a` vanishes at `a`. -/
theorem deriv_eq_zero_of_mirror {f : ℝ → ℝ} {a : ℝ} (hf : DifferentiableAt ℝ f a)
    (h : ∀ x : ℝ, f (2 * a - x) = f x) : deriv f a = 0 := by
  set d := deriv f a with hd
  have h1 : HasDerivAt f d a := hf.hasDerivAt
  have hσ : HasDerivAt (fun x : ℝ => 2 * a - x) (-1) a := by
    simpa using (hasDerivAt_const a (2 * a)).sub (hasDerivAt_id a)
  have h1' : HasDerivAt f d (2 * a - a) := by
    rw [show 2 * a - a = a by ring]; exact h1
  have h2 : HasDerivAt (fun x : ℝ => f (2 * a - x)) (d * -1) a := by
    simpa [Function.comp] using HasDerivAt.comp a h1' hσ
  have h3 : HasDerivAt f (d * -1) a := by simpa [h] using h2
  have := h1.unique h3
  linarith

/-- **No horizontal gradient of `|F|²` on a wall.** -/
theorem deriv_sqAbs_wall (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    deriv (sqAbs c N y) ((k : ℝ) / 2) = 0 :=
  deriv_eq_zero_of_mirror (differentiable_sqAbs c N y _) (sqAbs_mirror c N k y)

/-- **No horizontal gradient of `|F|` itself on a wall**, wherever `F` does not vanish. -/
theorem deriv_norm_wall (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ)
    (h : F c N (wallPt k y) ≠ 0) :
    deriv (fun x : ℝ => ‖F c N ((x : ℝ) + (y : ℝ) * Complex.I)‖) ((k : ℝ) / 2) = 0 := by
  have hne : sqAbs c N y ((k : ℝ) / 2) ≠ 0 := by
    rw [sqAbs_wall]
    simpa using h
  have hd : HasDerivAt (sqAbs c N y) 0 ((k : ℝ) / 2) := by
    have := (differentiable_sqAbs c N y ((k : ℝ) / 2)).hasDerivAt
    rwa [deriv_sqAbs_wall] at this
  have hsqrt := hd.sqrt hne
  have hfun : (fun x : ℝ => Real.sqrt (sqAbs c N y x))
      = fun x : ℝ => ‖F c N ((x : ℝ) + (y : ℝ) * Complex.I)‖ := by
    funext x; rw [sqAbs, Complex.norm_eq_sqrt_sq_add_sq, Complex.normSq_apply]; ring_nf
  rw [hfun] at hsqrt
  simpa using hsqrt.deriv

/-! ## Step 5: perpendicular contours -/

/-- The squared magnitude as a function on the plane `ℝ × ℝ`. -/
def sqAbs2 (c : ℕ → ℝ) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  Complex.normSq (F c N ((p.1 : ℝ) + (p.2 : ℝ) * Complex.I))

theorem differentiable_sqAbs2 (c : ℕ → ℝ) (N : ℕ) : Differentiable ℝ (sqAbs2 c N) := by
  have h1 : Differentiable ℝ fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) + (p.2 : ℝ) * Complex.I :=
    (Complex.ofRealCLM.differentiable.comp (differentiable_fst)).add
      ((Complex.ofRealCLM.differentiable.comp (differentiable_snd)).mul (differentiable_const _))
  have hc := ((differentiable_F c N).restrictScalars ℝ).comp h1
  have hre := Complex.reCLM.differentiable.comp hc
  have him := Complex.imCLM.differentiable.comp hc
  have := (hre.mul hre).add (him.mul him)
  simpa only [sqAbs2, Complex.normSq_apply, Function.comp] using this

/-- **The horizontal directional derivative of `|F|²` vanishes on a wall.** This is the precise
form of "the horizontal gradient drops to zero on the lines `x = 0, ±1/2, ±1`". -/
theorem fderiv_sqAbs2_wall_horizontal (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (1, 0) = 0 := by
  have hd : Differentiable ℝ (sqAbs2 c N) := differentiable_sqAbs2 c N
  have hslice : HasDerivAt (fun x : ℝ => sqAbs2 c N (x, y))
      (fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (1, 0)) ((k : ℝ) / 2) := by
    have hcurve : HasDerivAt (fun x : ℝ => (x, y)) ((1, 0) : ℝ × ℝ) ((k : ℝ) / 2) :=
      (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
    have hf : HasFDerivAt (sqAbs2 c N) (fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y))
        ((k : ℝ) / 2, y) := (hd _).hasFDerivAt
    exact hf.comp_hasDerivAt ((k : ℝ) / 2) hcurve
  have heq : (fun x : ℝ => sqAbs2 c N (x, y)) = sqAbs c N y := by
    funext x; simp [sqAbs, sqAbs2]
  rw [heq] at hslice
  have : deriv (sqAbs c N y) ((k : ℝ) / 2) = 0 := deriv_sqAbs_wall c N k y
  rw [← hslice.deriv, this]

/-- **The gradient of `|F|²` at a wall point is vertical.** Its horizontal component is zero, so
it points straight up or straight down along the wall — and the level curve of `|F|` through the
point, being orthogonal to the gradient, is horizontal there: it crosses the wall at `90°`. -/
theorem grad_sqAbs2_wall_vertical (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ) :
    ∃ v : ℝ, ∀ h : ℝ × ℝ, fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) h = v * h.2 := by
  refine ⟨fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (0, 1), fun h => ?_⟩
  have hsplit : h = h.1 • ((1, 0) : ℝ × ℝ) + h.2 • ((0, 1) : ℝ × ℝ) := by
    simp
  rw [hsplit, map_add, map_smul, map_smul, fderiv_sqAbs2_wall_horizontal]
  simp [mul_comm]

/-- **The contours cross the wall at a right angle.** Any differentiable curve through a wall
point that stays on a level set of `|F|` has *horizontal* velocity there, provided the gradient
does not vanish; the wall itself has vertical direction `(0,1)`, so the two meet at `90°`
(`contour_perp_wall`). -/
theorem contour_tangent_horizontal (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ)
    (γ : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (hγ : HasDerivAt γ v 0) (h0 : γ 0 = ((k : ℝ) / 2, y))
    (hlevel : ∀ t, sqAbs2 c N (γ t) = sqAbs2 c N ((k : ℝ) / 2, y))
    (hgrad : fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (0, 1) ≠ 0) :
    v.2 = 0 := by
  have hcomp : HasDerivAt (fun t => sqAbs2 c N (γ t))
      (fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) v) 0 := by
    have h := ((differentiable_sqAbs2 c N) (γ 0)).hasFDerivAt.comp_hasDerivAt 0 hγ
    rw [h0] at h
    exact h
  have hconst : HasDerivAt (fun t => sqAbs2 c N (γ t)) 0 0 := by
    simpa [hlevel] using (hasDerivAt_const (0 : ℝ) (sqAbs2 c N ((k : ℝ) / 2, y)))
  have hzero : fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) v = 0 := hcomp.unique hconst
  obtain ⟨w, hw⟩ := grad_sqAbs2_wall_vertical c N k y
  have hw1 : w = fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (0, 1) := by simpa using (hw (0, 1)).symm
  rw [hw v] at hzero
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd (hw1 ▸ h) hgrad
  · exact h

/-- The right angle, spelled out as a vanishing dot product: the velocity of a contour at a wall
point is orthogonal to the direction `(0,1)` of the wall. -/
theorem contour_perp_wall (c : ℕ → ℝ) (N : ℕ) (k : ℤ) (y : ℝ)
    (γ : ℝ → ℝ × ℝ) (v : ℝ × ℝ) (hγ : HasDerivAt γ v 0) (h0 : γ 0 = ((k : ℝ) / 2, y))
    (hlevel : ∀ t, sqAbs2 c N (γ t) = sqAbs2 c N ((k : ℝ) / 2, y))
    (hgrad : fderiv ℝ (sqAbs2 c N) ((k : ℝ) / 2, y) (0, 1) ≠ 0) :
    v.1 * 0 + v.2 * 1 = 0 := by
  rw [contour_tangent_horizontal c N k y γ v hγ h0 hlevel hgrad]; ring

/-! ## The two colours at the cusps of `Δ` -/

/-- A crude but sufficient tail bound: past the first term, `Fr` is within `N M r²` of its
leading term `c(1) r`. -/
theorem abs_Fr_sub_lead_le {c : ℕ → ℝ} {N : ℕ} {M r : ℝ} (hN : 1 ≤ N) (hr1 : |r| ≤ 1)
    (hM : ∀ n, n ≤ N → |c n| ≤ M) :
    |Fr c N r - c 1 * r| ≤ (N : ℝ) * M * r ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 1 (by omega))
  have hsum : Fr c (m + 1) r = (∑ i ∈ Finset.range m, c (i + 2) * r ^ (i + 2)) + c 1 * r := by
    rw [Fr, Finset.sum_range_succ']
    norm_num
  rw [hsum, add_sub_cancel_right]
  have hstep : ∀ i ∈ Finset.range m, |c (i + 2) * r ^ (i + 2)| ≤ M * r ^ 2 := by
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [abs_mul, abs_pow]
    have h1 : |c (i + 2)| ≤ M := hM _ (by omega)
    have h2 : |r| ^ (i + 2) ≤ |r| ^ 2 := pow_le_pow_of_le_one (abs_nonneg r) hr1 (by omega)
    have h3 : (0 : ℝ) ≤ |r| ^ (i + 2) := by positivity
    have h4 : |r| ^ 2 = r ^ 2 := sq_abs r
    nlinarith [abs_nonneg (c (i + 2))]
  calc |∑ i ∈ Finset.range m, c (i + 2) * r ^ (i + 2)|
      ≤ ∑ i ∈ Finset.range m, |c (i + 2) * r ^ (i + 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range m, M * r ^ 2 := Finset.sum_le_sum hstep
    _ = (m : ℝ) * (M * r ^ 2) := by rw [Finset.sum_const, Finset.card_range]; ring
    _ ≤ ((m : ℝ) + 1) * M * r ^ 2 := by nlinarith [sq_nonneg r]
    _ = ((m + 1 : ℕ) : ℝ) * M * r ^ 2 := by push_cast; ring

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
/-- A crude bound on the thirty plotted coefficients of `Δ`. -/
theorem abs_tau_le {n : ℕ} (hn : n ≤ 30) : |(tau n : ℝ)| ≤ 2 * 10 ^ 9 := by
  have h : ∀ m ∈ Finset.range 31, |tau m| ≤ 2 * 10 ^ 9 := by decide
  have h2 := h n (Finset.mem_range.2 (by omega))
  have hcast : |(tau n : ℝ)| = ((|tau n| : ℤ) : ℝ) := by push_cast; ring
  rw [hcast]
  exact_mod_cast h2

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
theorem tau_one : tau 1 = 1 := by decide

/-- `|q| = e^{-2πy} ≤ 10^{-11}` at height `y ≥ 5`: high enough for the leading term of the
thirty-term expansion to dominate all the others. -/
theorem exp_le_of_five_le {y : ℝ} (hy : 5 ≤ y) : Real.exp (-(2 * Real.pi * y)) ≤ 1 / 10 ^ 11 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have h31 : (31 : ℝ) ≤ 2 * Real.pi * y := by nlinarith
  have h1 : Real.exp (-(2 * Real.pi * y)) ≤ Real.exp (-31) := Real.exp_le_exp.2 (by linarith)
  have he : (2.7 : ℝ) < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have h2 : (2.7 : ℝ) ^ (31 : ℕ) < Real.exp 31 := by
    calc (2.7 : ℝ) ^ (31 : ℕ) < (Real.exp 1) ^ (31 : ℕ) :=
          pow_lt_pow_left₀ he (by norm_num) (by norm_num)
      _ = Real.exp 31 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (10 : ℝ) ^ 11 ≤ (2.7 : ℝ) ^ (31 : ℕ) := by norm_num
  have h4 : Real.exp (-31 : ℝ) = (Real.exp 31)⁻¹ := Real.exp_neg 31
  have h6 : (Real.exp 31)⁻¹ ≤ ((10 : ℝ) ^ 11)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
  rw [h4] at h1
  rw [one_div]
  linarith

/-- On the wall `x = k/2` at height `y`, the plotted approximation of `Δ` equals the real
polynomial `Fr` evaluated at `q = (-1)^k e^{-2πy}`. -/
theorem deltaApprox_wall_re (k : ℤ) (y : ℝ) :
    (deltaApprox 30 (wallPt k y)).re
      = Fr (fun n => (tau n : ℝ)) 30 ((-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y))) := by
  rw [deltaApprox_eq_F, F_wall_ofReal, Complex.ofReal_re]

/-- **Positive on the even walls.** For `y ≥ 5` the plotted approximation of `Δ` is real and
strictly positive on the walls `x = 0, ±1, ±2, …`: the phase there is exactly `0`. -/
theorem deltaApprox_wall_pos {y : ℝ} (hy : 5 ≤ y) {k : ℤ} (hk : Even k) :
    0 < (deltaApprox 30 (wallPt k y)).re := by
  have hr0 : 0 < Real.exp (-(2 * Real.pi * y)) := Real.exp_pos _
  have hrle : Real.exp (-(2 * Real.pi * y)) ≤ 1 / 10 ^ 11 := exp_le_of_five_le hy
  have hrval : (-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y)) = Real.exp (-(2 * Real.pi * y)) := by
    rw [hk.neg_one_zpow, one_mul]
  set r := Real.exp (-(2 * Real.pi * y)) with hrdef
  have habs : |r| ≤ 1 := by rw [abs_of_pos hr0]; linarith
  have hb := abs_Fr_sub_lead_le (c := fun n => (tau n : ℝ)) (N := 30) (M := 2 * 10 ^ 9) (r := r)
    (by norm_num) habs (fun n hn => abs_tau_le hn)
  have hlead : ((tau 1 : ℤ) : ℝ) * r = r := by rw [tau_one]; norm_num
  simp only [hlead] at hb
  obtain ⟨hlo, -⟩ := abs_le.1 hb
  rw [deltaApprox_wall_re, hrval]
  push_cast at hlo
  have hkey : (30 : ℝ) * (2 * 10 ^ 9) * r ^ 2 ≤ (6 / 10) * r := by nlinarith
  linarith

/-- **Negative on the odd walls.** For `y ≥ 5` the plotted approximation of `Δ` is real and
strictly negative on the walls `x = ±1/2, ±3/2, …`: the phase there is exactly `π`. -/
theorem deltaApprox_wall_neg {y : ℝ} (hy : 5 ≤ y) {k : ℤ} (hk : Odd k) :
    (deltaApprox 30 (wallPt k y)).re < 0 := by
  have hr0 : 0 < Real.exp (-(2 * Real.pi * y)) := Real.exp_pos _
  have hrle : Real.exp (-(2 * Real.pi * y)) ≤ 1 / 10 ^ 11 := exp_le_of_five_le hy
  have hrval : (-1 : ℝ) ^ k * Real.exp (-(2 * Real.pi * y)) = -Real.exp (-(2 * Real.pi * y)) := by
    rw [hk.neg_one_zpow]; ring
  set r := Real.exp (-(2 * Real.pi * y)) with hrdef
  have habs : |(-r)| ≤ 1 := by rw [abs_neg, abs_of_pos hr0]; linarith
  have hb := abs_Fr_sub_lead_le (c := fun n => (tau n : ℝ)) (N := 30) (M := 2 * 10 ^ 9) (r := -r)
    (by norm_num) habs (fun n hn => abs_tau_le hn)
  have hlead : ((tau 1 : ℤ) : ℝ) * (-r) = -r := by rw [tau_one]; norm_num
  simp only [hlead] at hb
  obtain ⟨-, hhi⟩ := abs_le.1 hb
  rw [deltaApprox_wall_re, hrval]
  push_cast at hhi
  have hsq : (-r) ^ 2 = r ^ 2 := by ring
  rw [hsq] at hhi
  have hkey : (30 : ℝ) * (2 * 10 ^ 9) * r ^ 2 ≤ (6 / 10) * r := by nlinarith
  linarith


/-- The colour of the even walls: argument exactly `0`. -/
theorem arg_deltaApprox_wall_even {y : ℝ} (hy : 5 ≤ y) {k : ℤ} (hk : Even k) :
    (deltaApprox 30 (wallPt k y)).arg = 0 := by
  rw [deltaApprox_eq_F]
  exact (arg_F_wall_eq_zero_iff _ 30 k y).2 (by
    have := deltaApprox_wall_pos hy hk
    rw [deltaApprox_eq_F] at this
    linarith)

/-- The colour of the odd walls: argument exactly `π`, half a turn from the even ones. -/
theorem arg_deltaApprox_wall_odd {y : ℝ} (hy : 5 ≤ y) {k : ℤ} (hk : Odd k) :
    (deltaApprox 30 (wallPt k y)).arg = Real.pi := by
  rw [deltaApprox_eq_F]
  exact (arg_F_wall_eq_pi_iff _ 30 k y).2 (by
    have := deltaApprox_wall_neg hy hk
    rw [deltaApprox_eq_F] at this
    linarith)

end


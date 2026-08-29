import Mathlib
import RequestProject.ArchimedesSpin
import RequestProject.DeltaModular

/-!
# Archimedes' polygons, spinning on the portrait of `Δ`

This file is the theory behind the animated plate: the regular `n`-gons of
`RequestProject/Archimedes369.lean`, inscribed in the unit circle, are set *spinning* and laid
on top of the phase portrait of the modular discriminant `Δ` of
`RequestProject/DeltaModular.lean`.

The frame of the animation is the rotation angle `t`. The `k`-th vertex at time `t` is

`v_n(t,k) = exp(i(π/2 + t + 2πk/n))`,

so `t = 0` is the static polygon of `RequestProject/ArchimedesSpin.lean`, anchored at `i`.

What is proved here.

* `spinVertex_zero`, `norm_spinVertex` — at `t = 0` this is the old vertex, and every vertex of
  every frame rides the arc `|z| = 1`, which is exactly the mirror of the portrait.
* `spinVertexSet_rot`, `spinVertexSet_eq_iff` — the animation closes up after a rotation by
  `2π/n`, and not before: the loop of the plate is one `n`-th of a turn.
* `chord_eq`, `perimeter_eq`, `hexagon_chord` — the moving polygon is rigid: every edge has
  length `2 sin(π/n)`, so its perimeter is `2·lower n`, Archimedes' lower bound for `2π`; for
  the hexagon every edge is exactly the radius `1`.
* `spinVertexSet_subset_of_dvd` — `3 ∣ 6 ∣ 12` and `3 ∣ 9`: the nested rings of the plate really
  are nested, at every instant of the animation.
* `S_image_spinVertexSet`, `S_stable_iff` — the modular involution `S : z ↦ −1/z` turns the
  frame `t` into the frame `−t`, so the spinning polygon is `S`-symmetric exactly at the
  instants `t = πk/n`: twice per loop.
* `Delta_spinVertex_phase`, `norm_Delta_S_pair` — on each vertex the phase lock of
  `DeltaModular.Delta_arc_phase` holds, and the two vertices exchanged by `S` carry the same
  `‖Δ‖`; for the twelve-gon (`Delta_spinVertex_twelve_phase`) the locking factor is
  `e^{12it}`, the *same* for all twelve vertices — the whole ring turns its phase in unison,
  and returns to its starting lock after the loop `t ↦ t + π/6`.
-/

noncomputable section

open Real Complex

open scoped Real

namespace ArchimedesDelta

variable {n : ℕ}

/-- The angle of the `k`-th vertex of the regular `n`-gon at time `t` of the animation: the
polygon of `Archimedes369.vertexAngle`, rotated by `t`. -/
def spinAngle (n : ℕ) (t : ℝ) (k : ℤ) : ℝ := Archimedes369.vertexAngle n k + t

/-- The `k`-th vertex of the spinning regular `n`-gon at time `t`. -/
def spinVertex (n : ℕ) (t : ℝ) (k : ℤ) : ℂ :=
  Complex.exp ((spinAngle n t k : ℂ) * Complex.I)

/-- The whole vertex ring at time `t`. -/
def spinVertexSet (n : ℕ) (t : ℝ) : Set ℂ := Set.range (spinVertex n t)

lemma spinAngle_def (n : ℕ) (t : ℝ) (k : ℤ) :
    spinAngle n t k = π / 2 + t + 2 * π * k / n := by
  unfold spinAngle Archimedes369.vertexAngle; ring

/-- At `t = 0` the spinning polygon is the static one of `ArchimedesSpin`. -/
@[simp] theorem spinVertex_zero (n : ℕ) (k : ℤ) :
    spinVertex n 0 k = Archimedes369.vertex n k := by
  unfold spinVertex Archimedes369.vertex spinAngle
  norm_num

/-- Every vertex of every frame lies on the unit circle — the arc across which the portrait of
`Δ` is mirrored. -/
@[simp] theorem norm_spinVertex (n : ℕ) (t : ℝ) (k : ℤ) : ‖spinVertex n t k‖ = 1 := by
  unfold spinVertex
  rw [Complex.norm_exp]
  simp

theorem spinVertex_ne_zero (n : ℕ) (t : ℝ) (k : ℤ) : spinVertex n t k ≠ 0 :=
  Complex.exp_ne_zero _

/-! ### The loop of the animation -/

/-- Two vertices coincide exactly when their angles differ by a whole number of turns. -/
lemma spinVertex_eq_iff (n : ℕ) (s t : ℝ) (j k : ℤ) :
    spinVertex n s j = spinVertex n t k ↔
      ∃ m : ℤ, spinAngle n s j = spinAngle n t k + m * (2 * π) := by
  unfold spinVertex
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have hI : (Complex.I) ≠ 0 := Complex.I_ne_zero
    have hc : ((spinAngle n s j : ℂ)) = ((spinAngle n t k : ℂ)) + (m : ℂ) * (2 * π) := by
      apply mul_right_cancel₀ hI
      rw [hm]; ring
    exact_mod_cast hc
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [hm]; push_cast; ring⟩

/-- Rotating the frame by `2πk/n` is the same as shifting the vertex index by `k`. -/
lemma spinVertex_shift (hn : 0 < n) (t : ℝ) (j k : ℤ) :
    spinVertex n (t + 2 * π * k / n) j = spinVertex n t (j + k) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold spinVertex
  congr 2
  rw [spinAngle_def, spinAngle_def]
  push_cast
  field_simp
  ring

/-- Rotating by `2π/n` maps the ring to itself: the animation loops after one `n`-th of a
turn. -/
theorem spinVertexSet_rot (hn : 0 < n) (t : ℝ) :
    spinVertexSet n (t + 2 * π / n) = spinVertexSet n t := by
  have h : t + 2 * π / n = t + 2 * π * ((1 : ℤ) : ℝ) / n := by norm_num
  rw [h]
  ext z
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j + 1, by rw [spinVertex_shift hn t j 1]⟩
  · rintro ⟨j, rfl⟩
    refine ⟨j - 1, ?_⟩
    rw [spinVertex_shift hn t (j - 1) 1]
    congr 1
    omega

/-- Two frames show the same ring exactly when they differ by a multiple of `2π/n`: the loop of
the animation is `2π/n` and nothing shorter. -/
theorem spinVertexSet_eq_iff (hn : 0 < n) (s t : ℝ) :
    spinVertexSet n s = spinVertexSet n t ↔ ∃ k : ℤ, s = t + 2 * π * k / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h
    have hmem : spinVertex n s 0 ∈ spinVertexSet n t := by
      rw [← h]; exact ⟨0, rfl⟩
    obtain ⟨j, hj⟩ := hmem
    rw [spinVertex_eq_iff] at hj
    obtain ⟨m, hm⟩ := hj
    rw [spinAngle_def, spinAngle_def] at hm
    refine ⟨j - m * n, ?_⟩
    have h0 : 2 * π * ((0 : ℤ) : ℝ) / n = 0 := by norm_num
    rw [h0] at hm
    have hs : s = t + 2 * π * j / n - m * (2 * π) := by linarith
    have hsplit : 2 * π * ((j - m * n : ℤ) : ℝ) / n = 2 * π * j / n - m * (2 * π) := by
      push_cast
      field_simp
    rw [hs, hsplit]
    ring
  · rintro ⟨k, rfl⟩
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j + k, by rw [spinVertex_shift hn t j k]⟩
    · rintro ⟨j, rfl⟩
      refine ⟨j - k, ?_⟩
      rw [spinVertex_shift hn t (j - k) k]
      congr 1
      omega

/-! ### The polygon is rigid -/

/-- The length of the chord subtending the angle `a` on the unit circle. -/
lemma norm_exp_sub_one (a : ℝ) (h : 0 ≤ Real.sin (a / 2)) :
    ‖Complex.exp ((a : ℂ) * Complex.I) - 1‖ = 2 * Real.sin (a / 2) := by
  have hre : (Complex.exp ((a : ℂ) * Complex.I) - 1).re = Real.cos a - 1 := by
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((a : ℂ) * Complex.I) - 1).im = Real.sin a := by
    simp [Complex.exp_ofReal_mul_I_im]
  have hcos : Real.cos a = 1 - 2 * Real.sin (a / 2) ^ 2 := by
    have hc := Real.cos_two_mul' (a / 2)
    rw [show 2 * (a / 2) = a by ring] at hc
    nlinarith [Real.sin_sq_add_cos_sq (a / 2)]
  have hsin : Real.sin a = 2 * Real.sin (a / 2) * Real.cos (a / 2) := by
    have hs := Real.sin_two_mul (a / 2)
    rw [show 2 * (a / 2) = a by ring] at hs
    linarith
  have hsq : ‖Complex.exp ((a : ℂ) * Complex.I) - 1‖ ^ 2 = (2 * Real.sin (a / 2)) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him, hcos, hsin]
    nlinarith [Real.sin_sq_add_cos_sq (a / 2)]
  nlinarith [hsq, norm_nonneg (Complex.exp ((a : ℂ) * Complex.I) - 1), h]

/-- Every edge of the moving polygon has length `2 sin(π/n)`. -/
theorem chord_eq (hn : 3 ≤ n) (t : ℝ) (k : ℤ) :
    ‖spinVertex n t (k + 1) - spinVertex n t k‖ = 2 * Real.sin (π / n) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  have hstep : spinAngle n t (k + 1) = spinAngle n t k + 2 * π / n := by
    rw [spinAngle_def, spinAngle_def]
    push_cast
    field_simp
    ring
  have hfac : spinVertex n t (k + 1) - spinVertex n t k
      = spinVertex n t k * (Complex.exp (((2 * π / n : ℝ) : ℂ) * Complex.I) - 1) := by
    unfold spinVertex
    rw [hstep]
    push_cast
    rw [mul_sub, mul_one, ← Complex.exp_add]
    ring_nf
  have harg : (2 * π / n) / 2 = π / n := by ring
  rw [hfac, norm_mul, norm_spinVertex, one_mul,
    norm_exp_sub_one (2 * π / n) (by rw [harg]; exact le_of_lt (Archimedes369.sin_pi_div_pos hn)),
    harg]

/-- Hence its perimeter is `2·lower n`, Archimedes' inscribed lower bound for `2π`. -/
theorem perimeter_eq (hn : 3 ≤ n) (t : ℝ) (k : ℤ) :
    (n : ℝ) * ‖spinVertex n t (k + 1) - spinVertex n t k‖ = 2 * Archimedes369.lower n := by
  rw [chord_eq hn t k, Archimedes369.lower]
  ring

/-- The spinning hexagon: every edge is exactly the radius. -/
theorem hexagon_chord (t : ℝ) (k : ℤ) :
    ‖spinVertex 6 t (k + 1) - spinVertex 6 t k‖ = 1 := by
  rw [chord_eq (by norm_num) t k]
  norm_num [Real.sin_pi_div_six]

/-! ### The nested rings `3 ∣ 6 ∣ 12`, `3 ∣ 9` -/

/-- If `m ∣ n` then the `m`-gon's vertices are among the `n`-gon's, at every instant: the rings
of the plate stay nested as they turn. -/
theorem spinVertexSet_subset_of_dvd {m : ℕ} (hn : 0 < n) (h : m ∣ n) (t : ℝ) :
    spinVertexSet m t ⊆ spinVertexSet n t := by
  obtain ⟨d, rfl⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm] at hn
    · exact hm
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · simp [hd] at hn
    · exact hd
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rintro z ⟨j, rfl⟩
  refine ⟨j * d, ?_⟩
  have hang : spinAngle (m * d) t (j * d) = spinAngle m t j := by
    rw [spinAngle_def, spinAngle_def]
    push_cast
    field_simp
  unfold spinVertex
  rw [hang]

/-! ### The modular involution runs the animation backwards -/

/-- `S : z ↦ −1/z` sends the frame `t` to the frame `−t`, vertex `k` to vertex `−k`. -/
theorem S_spinVertex (n : ℕ) (t : ℝ) (k : ℤ) :
    -(spinVertex n t k)⁻¹ = spinVertex n (-t) (-k) := by
  have hangle : π - spinAngle n t k = spinAngle n (-t) (-k) := by
    rw [spinAngle_def, spinAngle_def]; push_cast; ring
  unfold spinVertex
  rw [Archimedes369.neg_inv_circle (spinAngle n t k), hangle]

/-- The image of the ring under the modular involution is the ring of the reversed frame. -/
theorem S_image_spinVertexSet (n : ℕ) (t : ℝ) :
    (fun z : ℂ => -z⁻¹) '' spinVertexSet n t = spinVertexSet n (-t) := by
  ext z
  constructor
  · rintro ⟨w, ⟨k, rfl⟩, rfl⟩
    exact ⟨-k, (S_spinVertex n t k).symm⟩
  · rintro ⟨k, rfl⟩
    refine ⟨spinVertex n t (-k), ⟨-k, rfl⟩, ?_⟩
    show -(spinVertex n t (-k))⁻¹ = spinVertex n (-t) k
    rw [S_spinVertex]
    simp

/-- **The symmetric instants.** The spinning ring is stable under the modular involution
exactly at the times `t = πk/n` — twice in each loop `2π/n` of the animation. -/
theorem S_stable_iff (hn : 0 < n) (t : ℝ) :
    (fun z : ℂ => -z⁻¹) '' spinVertexSet n t = spinVertexSet n t ↔
      ∃ k : ℤ, t = π * k / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [S_image_spinVertexSet, spinVertexSet_eq_iff hn]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    push_cast
    field_simp at hk ⊢
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    rw [hk]
    push_cast
    field_simp
    ring

/-! ### The phase lock along the ring -/

/-- Every vertex that lies in the upper half plane sits on the arc `|z| = 1`, so the phase of
`Δ` there is locked to the vertex angle. -/
theorem Delta_spinVertex_phase (n : ℕ) (t : ℝ) (k : ℤ)
    (h : 0 < (spinVertex n t k).im) :
    spinVertex n t k ^ 12 * DeltaModular.Delta (spinVertex n t k) ^ 2
      = ((‖DeltaModular.Delta (spinVertex n t k)‖ : ℝ) : ℂ) ^ 2 :=
  DeltaModular.Delta_arc_phase h (norm_spinVertex n t k)

/-- For the twelve-gon the locking factor is `e^{12it}`: it does not depend on the vertex, so
all twelve vertices turn their phase in unison as the plate spins. -/
theorem spinVertex_twelve_pow (t : ℝ) (k : ℤ) :
    spinVertex 12 t k ^ 12 = Complex.exp (((12 * t : ℝ) : ℂ) * Complex.I) := by
  unfold spinVertex
  rw [← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨3 + k, ?_⟩
  rw [spinAngle_def]
  push_cast
  ring

/-- The twelve-gon's phase lock, driven by the frame angle alone. -/
theorem Delta_spinVertex_twelve_phase (t : ℝ) (k : ℤ)
    (h : 0 < (spinVertex 12 t k).im) :
    Complex.exp (((12 * t : ℝ) : ℂ) * Complex.I) * DeltaModular.Delta (spinVertex 12 t k) ^ 2
      = ((‖DeltaModular.Delta (spinVertex 12 t k)‖ : ℝ) : ℂ) ^ 2 := by
  rw [← spinVertex_twelve_pow t k]
  exact Delta_spinVertex_phase 12 t k h

/-- The two vertices exchanged by `S` carry the same `‖Δ‖`: the animation is mirror-symmetric
in the modulus of the form it is drawn on. -/
theorem norm_Delta_S_pair (n : ℕ) (t : ℝ) (k : ℤ) (h : 0 < (spinVertex n t k).im) :
    ‖DeltaModular.Delta (spinVertex n (-t) (-k))‖
      = ‖DeltaModular.Delta (spinVertex n t k)‖ := by
  rw [← S_spinVertex n t k, DeltaModular.Delta_neg_inv' h, norm_mul, norm_pow, norm_spinVertex]
  ring

end ArchimedesDelta

/-
# Bridging the two geometries: `T_j` on the upper half-plane and on the `s`-plane

`RequestProject/ZetaMoonshine.lean` builds a moonshine module for `ζ`: the group is `Z/24`,
the graded piece `Vₙ` is one-dimensional, and the element `j` acts on it by the scalar
`tr(j | Vₙ) = e^{2πi jn/24}`.  Its McKay–Thompson series is taken there in the *Dirichlet*
grading variable,

```
T_j(s) = ∑_{n ≥ 1} tr(j | Vₙ) n^{-s},     T_0 = ζ.
```

This file writes the *same* module in the *modular* grading variable `q = e^{2πiτ}`,

```
T_j(τ) = ∑_{n ≥ 1} tr(j | Vₙ) qⁿ = ∑_{n ≥ 1} e^{2πi jn/24} qⁿ,
```

so that the two pictures drawn in `visualization/moonshine-domain-coloring.svg` and
`visualization/moonshine-trajectories.svg` — a domain-coloured phase map on the upper
half-plane `ℍ` and a trajectory plot on the critical line `s = 1/2 + it` — are two views of
one and the same object.  The results proved here are exactly the structural claims those two
pictures make:

* `mtQ_eq_shift`: **the character twist is a horizontal translation**,
  `T_j(τ) = T_0(τ + j/24)`.  On the phase map this is the statement that the twenty-four
  twists are the twenty-four translates of one picture by `1/24`, i.e. the fundamental strip
  is partitioned into 24 vertical strips.
* `mtQ_period_one`, `mtQ_period_24`: `T_j(τ + 1) = T_j(τ)`, and `T_{j+24} = T_j`, so the phase
  map really is periodic horizontally and the 24 strips close up.
* `mtQ_eq_div` : the closed form `T_j(τ) = w/(1 − w)` with `w = e^{2πi(τ + j/24)}`, valid on
  all of `ℍ`; this is the function the renderer evaluates.
* `norm_mtQ_le`, `norm_mtQ_sub_leading_le`: as `Im τ → ∞` the series collapses onto its
  leading term `w`, whose phase is `2π(Re τ + j/24)` — the colour gradient at the top of the
  picture.
* `mtQ_twelve_eq_neg`: the order-two twist `j = 12` is the sign flip `∑ (−1)ⁿ qⁿ`, the
  `q`-side of the Dirichlet eta function.
* On the `s`-side, `mtSeries_twelve` : `T_12(s) = (2^{1−s} − 1) ζ(s)`, and
  `altPartial_eq` : the exact finite-truncation identity behind the plotted trajectory,
  `∑_{n ≤ 2M} (−1)ⁿ n^{-s} = 2^{1−s} ∑_{m ≤ M} m^{-s} − ∑_{n ≤ 2M} n^{-s}`.
-/
import Mathlib
import RequestProject.ZetaMoonshine

open Complex Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MoonshineBridge

open ZetaMoonshine

/-! ## The modular grading variable -/

/-- `q = e^{2πiτ}`, the grading variable of the modular side of moonshine. -/
noncomputable def qParam (τ : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * τ)

theorem qParam_add (τ σ : ℂ) : qParam (τ + σ) = qParam τ * qParam σ := by
  rw [qParam, qParam, qParam, ← Complex.exp_add]
  ring_nf

@[simp] theorem norm_qParam (τ : ℂ) : ‖qParam τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [qParam, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_qParam_lt_one {τ : ℂ} (h : 0 < τ.im) : ‖qParam τ‖ < 1 := by
  rw [norm_qParam]
  have : -(2 * Real.pi * τ.im) < 0 := by
    have := Real.pi_pos
    nlinarith
  simpa using Real.exp_lt_one_iff.mpr this

theorem qParam_ne_zero (τ : ℂ) : qParam τ ≠ 0 := Complex.exp_ne_zero _

/-- `q` is invariant under `τ ↦ τ + 1`: the horizontal periodicity of the phase map. -/
@[simp] theorem qParam_add_one (τ : ℂ) : qParam (τ + 1) = qParam τ := by
  have h1 : qParam 1 = 1 := by rw [qParam, mul_one, Complex.exp_two_pi_mul_I]
  rw [qParam_add, h1, mul_one]

/-! ## The graded traces of the ζ-moonshine module, explicitly -/

/-- The scalar by which the group element `j` acts on `Vₙ` is `e^{2πi jn/24}`. -/
theorem gradedTrace_natCast (j n : ℕ) :
    gradedTrace ((j : ZMod 24)) n = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j * n) / 24) := by
  have h : ((j : ZMod 24)) * ((n : ℕ) : ZMod 24) = (((j * n : ℕ) : ℤ) : ZMod 24) := by
    push_cast; ring
  rw [gradedTrace, irrep, h, ZMod.stdAddChar_coe]
  push_cast
  norm_num

/-! ## The McKay–Thompson series in the modular variable -/

/-- `T_j(τ) = ∑_{n ≥ 1} tr(j | Vₙ) qⁿ`: the McKay–Thompson series of the ζ-moonshine module
written in the modular grading variable `q = e^{2πiτ}`. -/
noncomputable def mtQ (j : ℕ) (τ : ℂ) : ℂ :=
  ∑' n : ℕ, gradedTrace ((j : ZMod 24)) (n + 1) * qParam τ ^ (n + 1)

/-- A single term of the twisted series is a term of the untwisted series translated
horizontally by `j/24`. -/
theorem term_eq (j n : ℕ) (τ : ℂ) :
    gradedTrace ((j : ZMod 24)) n * qParam τ ^ n = qParam (τ + (j : ℂ) / 24) ^ n := by
  rw [gradedTrace_natCast, qParam, qParam, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  ring

/-- **The character twist is a horizontal translation.**  `T_j(τ) = T_0(τ + j/24)`: on the
upper half-plane the twenty-four McKay–Thompson series of the ζ-moonshine module are the
twenty-four translates of one function by multiples of `1/24`, which is why the phase map of
the fundamental strip splits into twenty-four vertical strips. -/
theorem mtQ_eq_shift (j : ℕ) (τ : ℂ) : mtQ j τ = mtQ 0 (τ + (j : ℂ) / 24) := by
  rw [mtQ, mtQ]
  refine tsum_congr fun n => ?_
  rw [term_eq j (n + 1) τ]
  simp

/-- `T_j` has period one in `τ`. -/
theorem mtQ_period_one (j : ℕ) (τ : ℂ) : mtQ j (τ + 1) = mtQ j τ := by
  simp [mtQ]

/-- Shifting the group element by the order of the group changes nothing: the twenty-four
strips close up. -/
theorem mtQ_period_24 (j : ℕ) (τ : ℂ) : mtQ (j + 24) τ = mtQ j τ := by
  have h24 : ((24 : ℕ) : ZMod 24) = 0 := by decide
  have h : ((j + 24 : ℕ) : ZMod 24) = ((j : ℕ) : ZMod 24) := by
    rw [Nat.cast_add, h24, add_zero]
  rw [mtQ, mtQ, h]

/-- **The closed form the renderer evaluates.**  On the upper half-plane
`T_j(τ) = w/(1 − w)` with `w = e^{2πi(τ + j/24)}`. -/
theorem mtQ_eq_div {τ : ℂ} (j : ℕ) (hτ : 0 < τ.im) :
    mtQ j τ = qParam (τ + (j : ℂ) / 24) / (1 - qParam (τ + (j : ℂ) / 24)) := by
  set w := qParam (τ + (j : ℂ) / 24) with hw
  have him : (τ + (j : ℂ) / 24).im = τ.im := by
    simp [Complex.add_im]
  have hlt : ‖w‖ < 1 := by
    rw [hw]
    exact norm_qParam_lt_one (by rw [him]; exact hτ)
  have hsum : ∑' n : ℕ, w ^ (n + 1) = w * (1 - w)⁻¹ := by
    have : ∑' n : ℕ, w * w ^ n = w * ∑' n : ℕ, w ^ n := tsum_mul_left
    simpa [pow_succ, mul_comm, tsum_geometric_of_norm_lt_one hlt] using this
  calc mtQ j τ = ∑' n : ℕ, w ^ (n + 1) := by
        refine tsum_congr fun n => ?_
        rw [term_eq j (n + 1) τ]
    _ = w * (1 - w)⁻¹ := hsum
    _ = w / (1 - w) := (div_eq_mul_inv _ _).symm

/-! ## The behaviour high in the upper half-plane -/

/-- The whole series is bounded by the geometric bound `|q|/(1 − |q|)`; in particular it tends
to `0` as `Im τ → ∞`, which is why the phase map fades at the top. -/
theorem norm_mtQ_le {τ : ℂ} (j : ℕ) (hτ : 0 < τ.im) :
    ‖mtQ j τ‖ ≤ Real.exp (-(2 * Real.pi * τ.im)) / (1 - Real.exp (-(2 * Real.pi * τ.im))) := by
  set w := qParam (τ + (j : ℂ) / 24) with hw
  have him : (τ + (j : ℂ) / 24).im = τ.im := by
    simp [Complex.add_im]
  have hnorm : ‖w‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hw, norm_qParam, him]
  have hlt : ‖w‖ < 1 := by rw [hw]; exact norm_qParam_lt_one (by rw [him]; exact hτ)
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this] at hlt
    simp at hlt
  have h1 : ‖(1 : ℂ) - w‖ ≥ 1 - ‖w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    simpa using this
  rw [mtQ_eq_div j hτ, norm_div, ← hnorm]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (by linarith [hnorm ▸ hlt]) h1

/-- **The leading term dictates the colour.**  `T_j(τ)` differs from its leading term
`w = e^{2πi(τ + j/24)}` by at most `|w|²/(1 − |w|)`, so high in the upper half-plane the phase
of `T_j` is that of `w`, namely `2π(Re τ + j/24)`. -/
theorem norm_mtQ_sub_leading_le {τ : ℂ} (j : ℕ) (hτ : 0 < τ.im) :
    ‖mtQ j τ - qParam (τ + (j : ℂ) / 24)‖ ≤
      ‖qParam (τ + (j : ℂ) / 24)‖ ^ 2 / (1 - ‖qParam (τ + (j : ℂ) / 24)‖) := by
  set w := qParam (τ + (j : ℂ) / 24) with hw
  have him : (τ + (j : ℂ) / 24).im = τ.im := by
    simp [Complex.add_im]
  have hlt : ‖w‖ < 1 := by rw [hw]; exact norm_qParam_lt_one (by rw [him]; exact hτ)
  have hne : (1 : ℂ) - w ≠ 0 := by
    intro h
    have : w = 1 := by linear_combination -h
    rw [this] at hlt
    simp at hlt
  have hval : mtQ j τ - w = w ^ 2 / (1 - w) := by
    rw [mtQ_eq_div j hτ, ← hw]
    field_simp
    ring
  have h1 : (1 : ℝ) - ‖w‖ ≤ ‖(1 : ℂ) - w‖ := by
    have := norm_sub_norm_le (1 : ℂ) w
    simpa using this
  rw [hval, norm_div, norm_pow]
  exact div_le_div_of_nonneg_left (by positivity) (by linarith) h1

/-! ## The domain colouring

The phase map paints the point `τ` with the hue `arg(T_j(τ))` and the brightness `|T_j(τ)|`.
The two functions below are the exact colour coordinates the renderer uses. -/

/-- The hue of a complex number: its argument, normalised to `(-1/2, 1/2]`, i.e. a position on
the colour wheel. -/
noncomputable def hue (z : ℂ) : ℝ := Complex.arg z / (2 * Real.pi)

/-- The brightness attached to a modulus `m ≥ 0`: `m/(1 + m) ∈ [0, 1)`. -/
noncomputable def brightnessR (m : ℝ) : ℝ := m / (1 + m)

/-- The brightness of a complex number: `|z|/(1 + |z|) ∈ [0, 1)`, an increasing function of the
modulus, `0` at a zero and tending to `1` at a pole. -/
noncomputable def brightness (z : ℂ) : ℝ := brightnessR ‖z‖

theorem hue_mem_Ioc (z : ℂ) : hue z ∈ Set.Ioc (-(1 : ℝ) / 2) (1 / 2) := by
  have hpi := Real.pi_pos
  constructor
  · rw [hue, lt_div_iff₀ (by positivity)]
    nlinarith [Complex.neg_pi_lt_arg z]
  · rw [hue, div_le_iff₀ (by positivity)]
    nlinarith [Complex.arg_le_pi z]

theorem brightness_mem_Ico (z : ℂ) : brightness z ∈ Set.Ico (0 : ℝ) 1 := by
  have h := norm_nonneg z
  constructor
  · rw [brightness, brightnessR]
    positivity
  · rw [brightness, brightnessR, div_lt_one (by positivity)]
    linarith

/-- Brightness is strictly monotone in the modulus, so the brightness contours of the picture
are exactly the level curves of `|T_j|`. -/
theorem brightness_lt_brightness {z w : ℂ} (h : ‖z‖ < ‖w‖) : brightness z < brightness w := by
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  rw [brightness, brightness, brightnessR, brightnessR,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem brightnessR_strictMonoOn : StrictMonoOn brightnessR (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  rw [brightnessR, brightnessR, div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- The renderer compresses the modulus by a cube root before turning it into brightness; this
is still strictly increasing in `|T_j|`, so the brightness contours are unchanged as curves. -/
theorem brightnessR_cbrt_strictMonoOn :
    StrictMonoOn (fun m : ℝ => brightnessR (m ^ ((1 : ℝ) / 3))) (Set.Ici (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  exact brightnessR_strictMonoOn (Set.mem_Ici.2 (Real.rpow_nonneg ha _))
    (Set.mem_Ici.2 (Real.rpow_nonneg hb _))
    (Real.rpow_lt_rpow ha hab (by norm_num))

/-- The colour at `τ` in the `j`-th picture is the colour at `τ + j/24` in the `0`-th: the
twenty-four phase maps are one map read off twenty-four vertical strips. -/
theorem hue_mtQ_eq_shift (j : ℕ) (τ : ℂ) : hue (mtQ j τ) = hue (mtQ 0 (τ + (j : ℂ) / 24)) := by
  rw [mtQ_eq_shift j τ]

theorem brightness_mtQ_eq_shift (j : ℕ) (τ : ℂ) :
    brightness (mtQ j τ) = brightness (mtQ 0 (τ + (j : ℂ) / 24)) := by
  rw [mtQ_eq_shift j τ]

/-- The picture is periodic horizontally with period one. -/
theorem hue_mtQ_period_one (j : ℕ) (τ : ℂ) : hue (mtQ j (τ + 1)) = hue (mtQ j τ) := by
  rw [mtQ_period_one]

/-- The polar form of `q`: modulus `e^{-2π Im τ}`, phase `2π Re τ`.  Together with
`norm_mtQ_sub_leading_le` this is the colour gradient at the top of the picture: the hue there
runs once around the wheel as `Re τ` crosses a period. -/
theorem qParam_eq_polar (τ : ℂ) :
    qParam τ = (Real.exp (-(2 * Real.pi * τ.im)) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (τ.re : ℂ)) := by
  rw [qParam, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im]

/-- **The twenty-four strips are genuinely twenty-four different pictures.**  At a fixed point
of the upper half-plane the values `T_0(τ), …, T_23(τ)` are pairwise distinct. -/
theorem mtQ_injOn {τ : ℂ} (hτ : 0 < τ.im) {i j : ℕ} (hi : i < 24) (hj : j < 24)
    (h : mtQ i τ = mtQ j τ) : i = j := by
  have him : ∀ k : ℕ, (τ + (k : ℂ) / 24).im = τ.im := by
    intro k; simp [Complex.add_im]
  have hnorm : ∀ k : ℕ, ‖qParam (τ + (k : ℂ) / 24)‖ < 1 := fun k =>
    norm_qParam_lt_one (by rw [him k]; exact hτ)
  have hwi : ∀ k : ℕ, qParam (τ + (k : ℂ) / 24) = gradedTrace ((k : ZMod 24)) 1 * qParam τ := by
    intro k
    simpa using (term_eq k 1 τ).symm
  have hinj : ∀ z w : ℂ, ‖z‖ < 1 → ‖w‖ < 1 → z / (1 - z) = w / (1 - w) → z = w := by
    intro z w hz hw hzw
    have hz1 : (1 : ℂ) - z ≠ 0 := fun hc => by
      rw [show z = 1 by linear_combination -hc] at hz; simp at hz
    have hw1 : (1 : ℂ) - w ≠ 0 := fun hc => by
      rw [show w = 1 by linear_combination -hc] at hw; simp at hw
    field_simp at hzw
    linear_combination hzw
  have hval := hinj _ _ (hnorm i) (hnorm j)
    (by rw [← mtQ_eq_div i hτ, ← mtQ_eq_div j hτ]; exact h)
  rw [hwi i, hwi j] at hval
  have hchar : gradedTrace ((i : ZMod 24)) 1 = gradedTrace ((j : ZMod 24)) 1 :=
    mul_right_cancel₀ (qParam_ne_zero τ) hval
  have hstd : ZMod.stdAddChar ((i : ZMod 24)) = ZMod.stdAddChar ((j : ZMod 24)) := by
    simpa [gradedTrace, irrep] using hchar
  have hij := ZMod.injective_stdAddChar hstd
  have hv := congrArg ZMod.val hij
  rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at hv

/-! ## The order-two twist: the sign flip on both sides -/

/-- The element `12` of the group acts by `−1` on `V₁`. -/
theorem stdAddChar_twelve : (ZMod.stdAddChar (12 : ZMod 24)) = -1 := by
  have h2 : (ZMod.stdAddChar (12 : ZMod 24)) ^ 2 = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, show (2 : ℕ) • (12 : ZMod 24) = 0 by decide]
    exact AddChar.map_zero_eq_one _
  have hne : (ZMod.stdAddChar (12 : ZMod 24)) ≠ 1 := by
    intro h
    have h0 : ZMod.stdAddChar (12 : ZMod 24) = ZMod.stdAddChar (0 : ZMod 24) := by
      rw [h, AddChar.map_zero_eq_one]
    exact absurd (ZMod.injective_stdAddChar h0) (by decide)
  have hfac :
      ((ZMod.stdAddChar (12 : ZMod 24)) - 1) * ((ZMod.stdAddChar (12 : ZMod 24)) + 1) = 0 := by
    linear_combination h2
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- The order-two element of the moonshine group acts on `Vₙ` by `(−1)ⁿ`. -/
theorem gradedTrace_twelve (n : ℕ) : gradedTrace (12 : ZMod 24) n = (-1) ^ n := by
  rw [gradedTrace, irrep, show (12 : ZMod 24) * (n : ZMod 24) = n • (12 : ZMod 24) by
    rw [nsmul_eq_mul]; ring, AddChar.map_nsmul_eq_pow, stdAddChar_twelve]

/-- On the modular side the order-two twist is the sign flip `∑ (−1)ⁿ qⁿ`. -/
theorem mtQ_twelve_eq_neg (τ : ℂ) : mtQ 12 τ = ∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * qParam τ ^ (n + 1) := by
  rw [mtQ]
  refine tsum_congr fun n => ?_
  rw [show ((12 : ℕ) : ZMod 24) = (12 : ZMod 24) by decide, gradedTrace_twelve]

/-- On the modular side, `T_12(τ) = T_0(τ + 1/2)`: the half-period translation. -/
theorem mtQ_twelve_eq_half_shift (τ : ℂ) : mtQ 12 τ = mtQ 0 (τ + 1 / 2) := by
  rw [mtQ_eq_shift 12 τ]
  norm_num

/-- **The Dirichlet-side counterpart.**  The McKay–Thompson series of the order-two element in
the `s`-grading is `T_12(s) = ∑ (−1)ⁿ n^{-s} = (2^{1−s} − 1) ζ(s)`, i.e. (minus) the Dirichlet
eta function — the second trajectory of the plot. -/
theorem mtSeries_twelve {s : ℂ} (hs : 1 < s.re) :
    mtSeries (12 : ZMod 24) s = ((2 : ℂ) ^ (1 - s) - 1) * riemannZeta s := by
  have hcoeff : gradedTrace (12 : ZMod 24) = gradedTrace (1 : ZMod 2) := by
    funext n
    rw [gradedTrace_twelve, gradedTrace_one_two]
  rw [mtSeries, hcoeff, ← mtSeries]
  exact mtSeries_one_two hs

/-- **Where the order-two factor vanishes.**  `2^{1-s} = 1` exactly at the points
`s = 1 + 2πik/log 2` of the line `Re s = 1`, spaced `2π/log 2 = 9.0647…` apart; these are the
extra zeros that the twisted series `T_12 = (2^{1-s} − 1)ζ` has and `ζ` has not, and they are
what is marked on the phase map of `T_12`. -/
theorem two_cpow_one_sub_eq_one (k : ℤ) :
    (2 : ℂ) ^ (1 - (1 + 2 * (Real.pi : ℂ) * Complex.I * k / (Real.log 2 : ℂ))) = 1 := by
  have hlog : (Real.log 2 : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hclog : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
  rw [Complex.cpow_def_of_ne_zero (by norm_num), hclog]
  have hz : (Real.log 2 : ℂ) * (1 - (1 + 2 * (Real.pi : ℂ) * Complex.I * k / (Real.log 2 : ℂ)))
      = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp
    push_cast
    ring
  rw [hz, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]

/-! ## The truncated series that the trajectory plot draws -/

/-- `∑_{n = 1}^{K} n^{-s}`, the truncated zeta function, on the complex `s`-plane. -/
noncomputable def zetaPartialC (K : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 K, (n : ℂ) ^ (-s)

/-- `∑_{n = 1}^{K} (−1)ⁿ n^{-s}`, the truncated order-two twist. -/
noncomputable def altPartialC (K : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 K, (-1 : ℂ) ^ n * (n : ℂ) ^ (-s)

private theorem two_cpow_aux (k : ℕ) (s : ℂ) :
    (2 : ℂ) ^ (1 - s) * ((k : ℂ) ^ (-s)) = 2 * (((2 * k : ℕ) : ℂ) ^ (-s)) := by
  have hcast : ((2 * k : ℕ) : ℂ) ^ (-s) = (2 : ℂ) ^ (-s) * (k : ℂ) ^ (-s) := by
    have h := Complex.mul_cpow_ofReal_nonneg (a := (2 : ℝ)) (b := (k : ℝ))
      (by positivity) (by positivity) (-s)
    push_cast at h ⊢
    exact h
  have hpow : (2 : ℂ) ^ (1 - s) = 2 * (2 : ℂ) ^ (-s) := by
    rw [show (1 : ℂ) - s = 1 + (-s) by ring,
      Complex.cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  rw [hcast, hpow]
  ring

/-- **The exact identity behind the plotted trajectory.**  At every truncation length `2M`,
`∑_{n ≤ 2M} (−1)ⁿ n^{-s} = 2^{1−s} ∑_{m ≤ M} m^{-s} − ∑_{n ≤ 2M} n^{-s}`; letting `M → ∞` on
the half-plane `Re s > 1` this is `mtSeries_twelve`. -/
theorem altPartial_eq (M : ℕ) (s : ℂ) :
    altPartialC (2 * M) s = (2 : ℂ) ^ (1 - s) * zetaPartialC M s - zetaPartialC (2 * M) s := by
  induction M with
  | zero => simp [altPartialC, zetaPartialC]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by ring]
    have e1 : altPartialC ((2 * m + 1) + 1) s
        = altPartialC (2 * m) s + (-1 : ℂ) ^ (2 * m + 1) * ((2 * m + 1 : ℕ) : ℂ) ^ (-s)
          + (-1 : ℂ) ^ ((2 * m + 1) + 1) * (((2 * m + 1) + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [altPartialC, altPartialC, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have e2 : zetaPartialC ((2 * m + 1) + 1) s
        = zetaPartialC (2 * m) s + ((2 * m + 1 : ℕ) : ℂ) ^ (-s)
          + (((2 * m + 1) + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [zetaPartialC, zetaPartialC, Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
    have e3 : zetaPartialC (m + 1) s = zetaPartialC m s + ((m + 1 : ℕ) : ℂ) ^ (-s) := by
      rw [zetaPartialC, zetaPartialC, Finset.sum_Icc_succ_top (by omega)]
    have hsign1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hsign2 : (-1 : ℂ) ^ ((2 * m + 1) + 1) = 1 := by
      rw [pow_succ, hsign1]
      ring
    have hkey := two_cpow_aux (m + 1) s
    have hnum : ((2 * (m + 1) : ℕ) : ℂ) = (((2 * m + 1) + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [hnum] at hkey
    rw [e1, e2, e3, hsign1, hsign2, ih]
    rw [mul_add, hkey]
    ring

end MoonshineBridge

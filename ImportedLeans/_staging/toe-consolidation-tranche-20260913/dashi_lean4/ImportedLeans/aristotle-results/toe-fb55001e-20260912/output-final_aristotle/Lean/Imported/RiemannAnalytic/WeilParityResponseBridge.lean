/-
# The literal parity-response bridge for the compactly supported test family

The zero-side geometry of this development (`EvenTaylorDeterminant.lean`,
`OddTaylorDeterminant.lean`, `PoleQuotientTransversality.lean`) is phrased in
terms of the two parity responses of a compactly supported taper `φ` at a
*height* `y` and an observation radius `r`,

  `A_y(r) = ∫₀ᴸ φ(u) cosh (y u) cos (r u) du`   (`evenResponse`),
  `B_y(r) = ∫₀ᴸ φ(u) sinh (y u) sin (r u) du`   (`oddResponse`).

The Weil explicit formula, by contrast, evaluates a *test function* `h` at the
two pole points `± i/2` and at the (possibly off-line) zeros `ρ`, `1 − ρ̄`.
This module is the literal identification of the two languages, for the actual
compactly supported test family: `h` is the Fourier–Laplace transform

  `h(z) = ∫₋ᴸᴸ g(u) e^{i z u} du`     (`weilTransform`)

of the symmetric extension of the taper in each parity channel,

  `g_even(u) = φ(|u|) cos (r u)`,   `g_odd(u) = φ(|u|) sin (r u)`.

The normalisation factors are **not** normalised away: they are exposed in the
statements.

* `weilTransform_pair_cosh`, `weilTransform_pair_sinh` — the exact pairing
  identities.  Writing a zero as `ρ = 1/2 + α + i t`, so that its Weil argument
  is `γ_ρ = t − i α` and that of the reflected zero `1 − ρ̄` is `t + i α`, the
  sum and difference of the two evaluations are the `cosh`- and `sinh`-weighted
  transforms.  This is precisely where the hyperbolic kernels analysed on the
  zero side come from: `e^{αu} + e^{−αu} = 2 cosh(αu)`,
  `e^{αu} − e^{−αu} = 2 sinh(αu)`.

* `weilPoleEven_eq`, `weilPoleOdd_eq` — the pole evaluations at `± i/2`:

    `h_even(i/2) + h_even(−i/2) = 4 · evenResponse L φ (1/2) r`,
    `h_odd (i/2) − h_odd (−i/2) = −4 · oddResponse  L φ (1/2) r`,

  together with the vanishing of the opposite parity combinations.

* `weilZeroEven_eq`, `weilZeroOdd_eq` — the paired zero evaluations at height
  `α` (real part offset of `ρ`), with the same explicit constants `c_e = 4`,
  `c_o = 4`.

The theorems here are exact identities about the literal test family; they do
not use, and do not assert, the Weil explicit formula itself.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.EvenTaylorDeterminant
import RiemannAnalytic.OddTaylorDeterminant

open MeasureTheory Set

namespace RiemannAnalytic
namespace WeilParityResponseBridge

open EvenTaylorDeterminant OddTaylorDeterminant

/-! ## The symmetric test family and its transform -/

/-- The even-channel symmetric extension of the taper: `g(u) = φ(|u|) cos (r u)`. -/
noncomputable def symEvenTaper (φ : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u => φ |u| * Real.cos (r * u)

/-- The odd-channel symmetric extension of the taper: `g(u) = φ(|u|) sin (r u)`. -/
noncomputable def symOddTaper (φ : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u => φ |u| * Real.sin (r * u)

/-- The Weil test function attached to a compactly supported profile `g`:
`h(z) = ∫₋ᴸᴸ g(u) e^{i z u} du`. -/
noncomputable def weilTransform (L : ℝ) (g : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ u in (-L)..L, (g u : ℂ) * Complex.exp (Complex.I * z * u)

theorem symEvenTaper_even (φ : ℝ → ℝ) (r u : ℝ) :
    symEvenTaper φ r (-u) = symEvenTaper φ r u := by
  simp [symEvenTaper, abs_neg, Real.cos_neg, mul_neg]

theorem symOddTaper_odd (φ : ℝ → ℝ) (r u : ℝ) :
    symOddTaper φ r (-u) = -symOddTaper φ r u := by
  simp [symOddTaper, abs_neg, mul_neg, Real.sin_neg]

/-! ## Integrability -/

/-- A measurable function bounded on `Ioc a b` is integrable there. -/
theorem integrableOn_Ioc_of_bounded {a b C : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ u ∈ Ioc a b, |f u| ≤ C) : IntegrableOn f (Ioc a b) volume := by
  have hfin : (volume (Ioc a b)) ≠ ⊤ := by simp [Real.volume_Ioc]
  refine Integrable.mono' (g := fun _ => C) ?_ hf.aestronglyMeasurable ?_
  · exact integrableOn_const (μ := volume) (s := Ioc a b) hfin (by simp)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simpa [Real.norm_eq_abs] using hb u hu

variable {L Cφ : ℝ} {φ : ℝ → ℝ}

/-- The symmetric extension of a bounded measurable taper, multiplied by any
continuous factor, is interval integrable on `[-L, L]`. -/
theorem intervalIntegrable_symMul (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L)
    {k : ℝ → ℝ} (hk : Continuous k) :
    IntervalIntegrable (fun u => φ |u| * k u) volume (-L) L := by
  obtain ⟨Ck, hCk⟩ :=
    (isCompact_Icc (a := -L) (b := L)).exists_bound_of_continuousOn hk.continuousOn
  have hCk0 : 0 ≤ Ck := le_trans (norm_nonneg _) (hCk (-L) ⟨le_rfl, by linarith⟩)
  have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hφb 0 ⟨le_rfl, hL.le⟩)
  have hmeas : Measurable fun u : ℝ => φ |u| * k u :=
    (hφmeas.comp measurable_norm).mul hk.measurable
  constructor
  · refine integrableOn_Ioc_of_bounded (C := Cφ * Ck) hmeas ?_
    intro u hu
    have hu1 : |u| ≤ L := abs_le.2 ⟨le_of_lt hu.1, hu.2⟩
    have hu2 : -L ≤ u := le_of_lt hu.1
    have h1 : abs (φ |u|) ≤ Cφ := hφb |u| ⟨abs_nonneg u, hu1⟩
    have h2 : |k u| ≤ Ck := by
      simpa [Real.norm_eq_abs] using hCk u ⟨hu2, hu.2⟩
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hCφ0
  · have hemp : Ioc L (-L) = (∅ : Set ℝ) := by
      apply Ioc_eq_empty
      push_neg
      linarith
    rw [IntegrableOn, hemp]
    simp

/-- Integrability of the transform integrand. -/
theorem intervalIntegrable_transform {g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume (-L) L) (z : ℂ) :
    IntervalIntegrable (fun u : ℝ => (g u : ℂ) * Complex.exp (Complex.I * z * u))
      volume (-L) L := by
  have hgc : IntervalIntegrable (fun u : ℝ => (g u : ℂ)) volume (-L) L :=
    ⟨hg.1.ofReal, hg.2.ofReal⟩
  refine hgc.mul_continuousOn ?_
  fun_prop

/-! ## The exact pairing identities -/

/-- **Pairing identity, even combination.**  For a zero `ρ = 1/2 + α + i t`,
whose Weil argument is `t − i α`, and the reflected zero `1 − ρ̄`, with argument
`t + i α`, the *sum* of the two evaluations is the `cosh`-weighted transform. -/
theorem weilTransform_pair_cosh {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-L) L)
    (t α : ℝ) :
    weilTransform L g ((t : ℂ) + Complex.I * α) + weilTransform L g ((t : ℂ) - Complex.I * α)
      = ∫ u in (-L)..L, ((2 * g u * Real.cosh (α * u) : ℝ) : ℂ)
          * Complex.exp (Complex.I * t * u) := by
  rw [weilTransform, weilTransform,
    ← intervalIntegral.integral_add (intervalIntegrable_transform hg _)
      (intervalIntegrable_transform hg _)]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  have hc : ((Real.cosh (α * u) : ℝ) : ℂ)
      = (Complex.exp ((α : ℂ) * u) + Complex.exp (-((α : ℂ) * u))) / 2 := by
    rw [Complex.ofReal_cosh, Complex.cosh]
    push_cast
    ring
  have e1 : Complex.I * ((t : ℂ) + Complex.I * α) * u
      = Complex.I * t * u + (-((α : ℂ) * u)) := by
    have h := Complex.I_mul_I
    linear_combination (α : ℂ) * u * h
  have e2 : Complex.I * ((t : ℂ) - Complex.I * α) * u
      = Complex.I * t * u + ((α : ℂ) * u) := by
    have h := Complex.I_mul_I
    linear_combination (-(α : ℂ) * u) * h
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  push_cast [hc]
  ring

/-- **Pairing identity, odd combination.**  The *difference* of the two paired
evaluations is the `sinh`-weighted transform. -/
theorem weilTransform_pair_sinh {g : ℝ → ℝ} (hg : IntervalIntegrable g volume (-L) L)
    (t α : ℝ) :
    weilTransform L g ((t : ℂ) - Complex.I * α) - weilTransform L g ((t : ℂ) + Complex.I * α)
      = ∫ u in (-L)..L, ((2 * g u * Real.sinh (α * u) : ℝ) : ℂ)
          * Complex.exp (Complex.I * t * u) := by
  rw [weilTransform, weilTransform,
    ← intervalIntegral.integral_sub (intervalIntegrable_transform hg _)
      (intervalIntegrable_transform hg _)]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  have hs : ((Real.sinh (α * u) : ℝ) : ℂ)
      = (Complex.exp ((α : ℂ) * u) - Complex.exp (-((α : ℂ) * u))) / 2 := by
    rw [Complex.ofReal_sinh, Complex.sinh]
    push_cast
    ring
  have e1 : Complex.I * ((t : ℂ) + Complex.I * α) * u
      = Complex.I * t * u + (-((α : ℂ) * u)) := by
    have h := Complex.I_mul_I
    linear_combination (α : ℂ) * u * h
  have e2 : Complex.I * ((t : ℂ) - Complex.I * α) * u
      = Complex.I * t * u + ((α : ℂ) * u) := by
    have h := Complex.I_mul_I
    linear_combination (-(α : ℂ) * u) * h
  rw [e1, e2, Complex.exp_add, Complex.exp_add]
  push_cast [hs]
  ring

/-! ## Folding the symmetric interval -/

/-- A symmetric integral of an even function is twice the half-line integral. -/
theorem integral_symm_even {f : ℝ → ℝ} (hL : 0 < L) (heven : ∀ x, f (-x) = f x)
    (hint : IntervalIntegrable f volume (-L) L) :
    ∫ x in (-L)..L, f x = 2 * ∫ x in (0 : ℝ)..L, f x := by
  have h1 : IntervalIntegrable f volume (-L) 0 := hint.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable f volume 0 L := hint.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hneg : ∫ x in (0 : ℝ)..L, f (-x) = ∫ x in (-L)..(0 : ℝ), f x := by
    simp [intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) f]
  have hfe : ∫ x in (0 : ℝ)..L, f (-x) = ∫ x in (0 : ℝ)..L, f x := by
    simp only [heven]
  rw [← hadd, ← hneg, hfe]
  ring

/-- A symmetric integral of an odd function vanishes. -/
theorem integral_symm_odd {f : ℝ → ℝ} (hL : 0 < L) (hodd : ∀ x, f (-x) = -f x)
    (hint : IntervalIntegrable f volume (-L) L) :
    ∫ x in (-L)..L, f x = 0 := by
  have h1 : IntervalIntegrable f volume (-L) 0 := hint.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc le_rfl (by linarith))
  have h2 : IntervalIntegrable f volume 0 L := hint.mono_set (by
    rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)]
    exact Set.Icc_subset_Icc (by linarith) le_rfl)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
  have hneg : ∫ x in (0 : ℝ)..L, f (-x) = ∫ x in (-L)..(0 : ℝ), f x := by
    simp [intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) f]
  have hfo : ∫ x in (0 : ℝ)..L, f (-x) = -∫ x in (0 : ℝ)..L, f x := by
    simp only [hodd, intervalIntegral.integral_neg]
  rw [← hadd, ← hneg, hfo]
  ring

/-! ## The half-line integrals are the parity responses -/

theorem half_integral_even (hL : 0 < L) (φ : ℝ → ℝ) (r α : ℝ) :
    ∫ u in (0 : ℝ)..L, symEvenTaper φ r u * Real.cosh (α * u)
      = evenResponse L φ α r := by
  rw [intervalIntegral.integral_of_le hL.le, evenResponse]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  simp only [symEvenTaper, abs_of_pos hu.1]
  ring

theorem half_integral_odd (hL : 0 < L) (φ : ℝ → ℝ) (r α : ℝ) :
    ∫ u in (0 : ℝ)..L, symOddTaper φ r u * Real.sinh (α * u)
      = oddResponse L φ α r := by
  rw [intervalIntegral.integral_of_le hL.le, oddResponse]
  refine setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
  simp only [symOddTaper, abs_of_pos hu.1]
  ring

/-! ## The bridge -/

/-- Interval integrability of a parity channel weighted by a hyperbolic factor. -/
theorem intervalIntegrable_channel (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L)
    {s c : ℝ → ℝ} (hs : Continuous s) (hc : Continuous c) :
    IntervalIntegrable (fun u => φ |u| * s u * c u) volume (-L) L := by
  have hfun : (fun u => φ |u| * s u * c u) = fun u => φ |u| * (s u * c u) := by
    funext u; ring
  rw [hfun]
  exact intervalIntegrable_symMul hφmeas hφb hL (hs.mul hc)

/-- **Even-channel bridge.**  Writing a zero as `ρ = 1/2 + α + i t`, its Weil
argument is `t − i α` and that of the reflected zero `1 − ρ̄` is `t + i α`.  At
`t = 0` the *sum* of the two evaluations of the even-channel test function is
literally `4 · evenResponse L φ α r`: the constant `c_e = 4` is exposed, not
normalised away. -/
theorem weilZeroEven_eq (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (r α : ℝ) :
    weilTransform L (symEvenTaper φ r) (Complex.I * α)
        + weilTransform L (symEvenTaper φ r) (-(Complex.I * α))
      = 4 * (evenResponse L φ α r : ℂ) := by
  have hg : IntervalIntegrable (symEvenTaper φ r) volume (-L) L :=
    intervalIntegrable_symMul hφmeas hφb hL (by fun_prop)
  have hint : IntervalIntegrable
      (fun u => symEvenTaper φ r u * Real.cosh (α * u)) volume (-L) L :=
    intervalIntegrable_channel hφmeas hφb hL (s := fun u => Real.cos (r * u))
      (c := fun u => Real.cosh (α * u)) (by fun_prop) (by fun_prop)
  have hpair := weilTransform_pair_cosh (L := L) hg 0 α
  simp only [Complex.ofReal_zero, zero_add, zero_sub] at hpair
  rw [hpair]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal]
  have h2 : ∫ u in (-L)..L, 2 * symEvenTaper φ r u * Real.cosh (α * u)
      = 2 * ∫ u in (-L)..L, symEvenTaper φ r u * Real.cosh (α * u) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have hsym : ∫ u in (-L)..L, symEvenTaper φ r u * Real.cosh (α * u)
      = 2 * ∫ u in (0 : ℝ)..L, symEvenTaper φ r u * Real.cosh (α * u) := by
    refine integral_symm_even hL (fun x => ?_) hint
    show symEvenTaper φ r (-x) * Real.cosh (α * -x)
      = symEvenTaper φ r x * Real.cosh (α * x)
    rw [symEvenTaper_even, mul_neg, Real.cosh_neg]
  rw [h2, hsym, half_integral_even hL]
  push_cast
  ring

/-- **Odd-channel bridge.**  With the same convention, the *difference* of the
two paired evaluations of the odd-channel test function is literally
`4 · oddResponse L φ α r`: the constant `c_o = 4` is exposed. -/
theorem weilZeroOdd_eq (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (r α : ℝ) :
    weilTransform L (symOddTaper φ r) (-(Complex.I * α))
        - weilTransform L (symOddTaper φ r) (Complex.I * α)
      = 4 * (oddResponse L φ α r : ℂ) := by
  have hg : IntervalIntegrable (symOddTaper φ r) volume (-L) L :=
    intervalIntegrable_symMul hφmeas hφb hL (by fun_prop)
  have hint : IntervalIntegrable
      (fun u => symOddTaper φ r u * Real.sinh (α * u)) volume (-L) L :=
    intervalIntegrable_channel hφmeas hφb hL (s := fun u => Real.sin (r * u))
      (c := fun u => Real.sinh (α * u)) (by fun_prop) (by fun_prop)
  have hpair := weilTransform_pair_sinh (L := L) hg 0 α
  simp only [Complex.ofReal_zero, zero_add, zero_sub] at hpair
  rw [hpair]
  simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal]
  have h2 : ∫ u in (-L)..L, 2 * symOddTaper φ r u * Real.sinh (α * u)
      = 2 * ∫ u in (-L)..L, symOddTaper φ r u * Real.sinh (α * u) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun u _ => by ring)
  have hsym : ∫ u in (-L)..L, symOddTaper φ r u * Real.sinh (α * u)
      = 2 * ∫ u in (0 : ℝ)..L, symOddTaper φ r u * Real.sinh (α * u) := by
    refine integral_symm_even hL (fun x => ?_) hint
    show symOddTaper φ r (-x) * Real.sinh (α * -x)
      = symOddTaper φ r x * Real.sinh (α * x)
    rw [symOddTaper_odd, mul_neg, Real.sinh_neg]
    ring
  rw [h2, hsym, half_integral_odd hL]
  push_cast
  ring

/-- **Even pole evaluation.**  `h_even(i/2) + h_even(−i/2) = 4 · A_{1/2}(r)`:
the two pole points of the Weil formula produce exactly the even response at the
pole height `1/2`. -/
theorem weilPoleEven_eq (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (r : ℝ) :
    weilTransform L (symEvenTaper φ r) (Complex.I / 2)
        + weilTransform L (symEvenTaper φ r) (-(Complex.I / 2))
      = 4 * (evenResponse L φ (1 / 2) r : ℂ) := by
  have h := weilZeroEven_eq hφmeas hφb hL r (1 / 2)
  have hI : Complex.I * (((1 : ℝ) / 2 : ℝ) : ℂ) = Complex.I / 2 := by
    push_cast; ring
  rw [hI] at h
  exact h

/-- **Odd pole evaluation.**  `h_odd(i/2) − h_odd(−i/2) = −4 · B_{1/2}(r)`: the
antisymmetric pole combination produces exactly the odd response at the pole
height `1/2`, with the sign the convention actually carries. -/
theorem weilPoleOdd_eq (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (r : ℝ) :
    weilTransform L (symOddTaper φ r) (Complex.I / 2)
        - weilTransform L (symOddTaper φ r) (-(Complex.I / 2))
      = -(4 * (oddResponse L φ (1 / 2) r : ℂ)) := by
  have h := weilZeroOdd_eq hφmeas hφb hL r (1 / 2)
  have hI : Complex.I * (((1 : ℝ) / 2 : ℝ) : ℂ) = Complex.I / 2 := by
    push_cast; ring
  rw [hI] at h
  linear_combination -h

/-- **The cross-parity combinations vanish identically.**  The even channel has
no antisymmetric part and the odd channel no symmetric part, so the two parity
channels of the test family are exactly separated. -/
theorem weilParity_cross_vanishes (hφmeas : Measurable φ)
    (hφb : ∀ u ∈ Icc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (r α : ℝ) :
    weilTransform L (symEvenTaper φ r) (-(Complex.I * α))
        - weilTransform L (symEvenTaper φ r) (Complex.I * α) = 0 ∧
    weilTransform L (symOddTaper φ r) (Complex.I * α)
        + weilTransform L (symOddTaper φ r) (-(Complex.I * α)) = 0 := by
  constructor
  · have hg : IntervalIntegrable (symEvenTaper φ r) volume (-L) L :=
      intervalIntegrable_symMul hφmeas hφb hL (by fun_prop)
    have hint : IntervalIntegrable
        (fun u => 2 * symEvenTaper φ r u * Real.sinh (α * u)) volume (-L) L := by
      have hfun : (fun u => 2 * symEvenTaper φ r u * Real.sinh (α * u))
          = fun u => φ |u| * (2 * Real.cos (r * u)) * Real.sinh (α * u) := by
        funext u
        simp only [symEvenTaper]
        ring
      rw [hfun]
      exact intervalIntegrable_channel hφmeas hφb hL (by fun_prop) (by fun_prop)
    have hpair := weilTransform_pair_sinh (L := L) hg 0 α
    simp only [Complex.ofReal_zero, zero_add, zero_sub] at hpair
    rw [hpair]
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_ofReal]
    have hzero : ∫ u in (-L)..L, 2 * symEvenTaper φ r u * Real.sinh (α * u) = 0 := by
      refine integral_symm_odd hL (fun x => ?_) hint
      show 2 * symEvenTaper φ r (-x) * Real.sinh (α * -x)
        = -(2 * symEvenTaper φ r x * Real.sinh (α * x))
      simp only [symEvenTaper_even, mul_neg, Real.sinh_neg]
    rw [hzero]
    norm_num
  · have hg : IntervalIntegrable (symOddTaper φ r) volume (-L) L :=
      intervalIntegrable_symMul hφmeas hφb hL (by fun_prop)
    have hint : IntervalIntegrable
        (fun u => 2 * symOddTaper φ r u * Real.cosh (α * u)) volume (-L) L := by
      have hfun : (fun u => 2 * symOddTaper φ r u * Real.cosh (α * u))
          = fun u => φ |u| * (2 * Real.sin (r * u)) * Real.cosh (α * u) := by
        funext u
        simp only [symOddTaper]
        ring
      rw [hfun]
      exact intervalIntegrable_channel hφmeas hφb hL (by fun_prop) (by fun_prop)
    have hpair := weilTransform_pair_cosh (L := L) hg 0 α
    simp only [Complex.ofReal_zero, zero_add, zero_sub] at hpair
    rw [hpair]
    simp only [mul_zero, zero_mul, Complex.exp_zero, mul_one]
    rw [intervalIntegral.integral_ofReal]
    have hzero : ∫ u in (-L)..L, 2 * symOddTaper φ r u * Real.cosh (α * u) = 0 := by
      refine integral_symm_odd hL (fun x => ?_) hint
      show 2 * symOddTaper φ r (-x) * Real.cosh (α * -x)
        = -(2 * symOddTaper φ r x * Real.cosh (α * x))
      simp only [symOddTaper_odd, mul_neg, Real.cosh_neg]
      ring
    rw [hzero]
    norm_num

end WeilParityResponseBridge
end RiemannAnalytic

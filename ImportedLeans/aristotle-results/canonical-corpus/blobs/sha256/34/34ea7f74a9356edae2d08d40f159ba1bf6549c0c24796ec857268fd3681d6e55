/-
# G21 — the decision: literal witnesses on both sides

This module closes the G21 experiment with the two literal computations that the
design asked for, and states the resulting decision.

## Prime side (lemmas 4–5): a literal nonvanishing pair-kernel witness

With the arithmetic frequencies `λ_n = log n`, the amplitudes
`a_n = Λ(n)/√n` and the three samples

```
x = (0, π/log 2, 2π/log 2),
```

the mode vectors of the prime powers `2` and `4` are exactly `(1,−1,1)` and
`(1,1,1)` (`modeVector_two`, `modeVector_four`), so the exterior minor is the
*exact* number

```
D(2,4) = 2 (m(x₃) − m(x₁)),
```

with `m` the literal pole profile of `ExteriorGate.lean`
(`augDet3_modeVector_two_four`).  Because `|m(2π/log 2)| < m(0)` for every
`L ≥ 1` (`poleProfile_abs_lt_zero_freq`), this minor is nonzero, hence
`primePairKernel_two_four_ne_zero`, hence — by the certificates of
`ExteriorPairKernel.lean` — the surviving prime pair kernel is genuinely
nonseparable and of rank `> 1`
(`primePairKernel_nonseparable`, `primePairKernel_not_rankOne`), with the
explicit four-point rectangle defect `−2K(2,4) ≠ 0`.

So the *prime* side of the G21 architecture does deliver the object the design
asked for.

## Zero side (lemma 3): the gate is red

The literal truncated single-zero response is
`Z_ρ(x) = ∫_0^L e^{(ρ−1/2+ix)u} du = (e^{(ρ−1/2+ix)L} − 1)/(ρ−1/2+ix)`
(`zeroResponse_eq_integral`), and its contrastive-derivative channel is the
honest `x`-derivative (`hasDerivAt_zeroResponse`).  The resulting augmented
determinant is **holomorphic in ρ** (`differentiableOn_zeroSideObservable`), so
by `no_criticalLine_separation` it cannot vanish for the on-line zeros of a disc
and be nonzero for an off-line zero of that disc
(`zeroSideObservable_no_criticalLine_separation`).

Together with `singleMode_gate_no_floor` (the exterior observable annihilates
every single-mode response exactly, whatever its amplitude), the verdict on the
G21 make-or-break ordering `2 → 3 → 4 → 5` is: step 2 succeeds exactly, step 3
fails, and steps 4–5, although they do produce a literal nonseparable kernel,
cannot be converted into a zero-detection gate by this observable.
-/
import RiemannAnalytic.ExteriorGate

open Complex Filter ArithmeticFunction

namespace RiemannAnalytic

noncomputable section

/-! ## Literal prime-side data -/

/-- The literal arithmetic frequencies `λ_n = log n`. -/
def primeLogFreq (n : ℕ) : ℝ := Real.log n

/-- The literal Weil amplitudes `a_n = Λ(n)/√n`. -/
def vonMangoldtAmp (n : ℕ) : ℂ := (Λ n : ℂ) / (Real.sqrt n : ℂ)

/-- The three observation samples `x = (0, π/log 2, 2π/log 2)`. -/
def gridSamples : Fin 3 → ℝ := ![0, Real.pi / Real.log 2, 2 * Real.pi / Real.log 2]

theorem log_two_ne_zero : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))

theorem gridSamples_one_mul : gridSamples 1 * Real.log 2 = Real.pi := by
  simp [gridSamples]
  field_simp

theorem gridSamples_two_mul : gridSamples 2 * Real.log 2 = 2 * Real.pi := by
  simp [gridSamples]
  field_simp

theorem primeLogFreq_four : primeLogFreq 4 = 2 * primeLogFreq 2 := by
  simp only [primeLogFreq]
  rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

theorem modeVector_two : modeVector gridSamples (primeLogFreq 2) = ![1, -1, 1] := by
  have hlog : primeLogFreq 2 = Real.log 2 := by simp [primeLogFreq]
  funext j
  fin_cases j
  · simp [modeVector, gridSamples]
  · show Complex.exp (Complex.I * ((gridSamples 1 : ℂ) * ((primeLogFreq 2 : ℝ) : ℂ))) = _
    rw [hlog, ← Complex.ofReal_mul, gridSamples_one_mul]
    rw [show Complex.I * (Real.pi : ℂ) = (Real.pi : ℂ) * Complex.I by ring, Complex.exp_pi_mul_I]
    simp
  · show Complex.exp (Complex.I * ((gridSamples 2 : ℂ) * ((primeLogFreq 2 : ℝ) : ℂ))) = _
    rw [hlog, ← Complex.ofReal_mul, gridSamples_two_mul]
    push_cast
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = (2 * Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_two_pi_mul_I]

theorem modeVector_four : modeVector gridSamples (primeLogFreq 4) = ![1, 1, 1] := by
  have hlog : primeLogFreq 2 = Real.log 2 := by simp [primeLogFreq]
  funext j
  fin_cases j
  · simp [modeVector, gridSamples]
  · show Complex.exp (Complex.I * ((gridSamples 1 : ℂ) * ((primeLogFreq 4 : ℝ) : ℂ))) = _
    rw [primeLogFreq_four, hlog, ← Complex.ofReal_mul, ← mul_assoc,
      mul_comm (gridSamples 1) 2, mul_assoc, gridSamples_one_mul]
    push_cast
    rw [show Complex.I * (2 * (Real.pi : ℂ)) = (2 * Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_two_pi_mul_I]
  · show Complex.exp (Complex.I * ((gridSamples 2 : ℂ) * ((primeLogFreq 4 : ℝ) : ℂ))) = _
    rw [primeLogFreq_four, hlog, ← Complex.ofReal_mul, ← mul_assoc,
      mul_comm (gridSamples 2) 2, mul_assoc, gridSamples_two_mul]
    push_cast
    rw [show Complex.I * (2 * (2 * (Real.pi : ℂ)))
        = (2 * Real.pi : ℂ) * Complex.I + (2 * Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_add, Complex.exp_two_pi_mul_I]
    simp

/-- The exterior minor of the two prime-power modes `2` and `4` at the three
samples is exactly `2(m(x₃) − m(x₁))`. -/
theorem augDet3_modeVector_two_four (m : Fin 3 → ℂ) :
    augDet3 (modeVector gridSamples (primeLogFreq 2)) (modeVector gridSamples (primeLogFreq 4)) m
      = 2 * (m 2 - m 0) := by
  rw [modeVector_two, modeVector_four, augDet3_eq]
  simp
  ring

/-! ## The pole profile at the literal samples -/

/-- Crude but exact envelope for the pole profile. -/
theorem poleProfile_abs_le (L x : ℝ) :
    |poleProfile L x| ≤ (Real.exp (L / 2) * (1 / 2 + |x|) + 1 / 2) / (1 / 4 + x ^ 2) := by
  have hden : (0 : ℝ) < 1 / 4 + x ^ 2 := by positivity
  rw [poleProfile_closedForm, abs_div, abs_of_pos hden]
  refine div_le_div_of_nonneg_right ?_ hden.le
  · have hc : |Real.cos (x * L)| ≤ 1 := Real.abs_cos_le_one _
    have hs : |Real.sin (x * L)| ≤ 1 := Real.abs_sin_le_one _
    have hA : 0 < Real.exp (L / 2) := Real.exp_pos _
    calc |Real.exp (L / 2) * ((1 / 2) * Real.cos (x * L) + x * Real.sin (x * L)) - 1 / 2|
        ≤ |Real.exp (L / 2) * ((1 / 2) * Real.cos (x * L) + x * Real.sin (x * L))| + |(1:ℝ) / 2| :=
          abs_sub _ _
      _ ≤ Real.exp (L / 2) * (1 / 2 + |x|) + 1 / 2 := by
          rw [abs_mul, abs_of_pos hA]
          have : |(1 / 2) * Real.cos (x * L) + x * Real.sin (x * L)| ≤ 1 / 2 + |x| := by
            calc |(1 / 2) * Real.cos (x * L) + x * Real.sin (x * L)|
                ≤ |(1 / 2) * Real.cos (x * L)| + |x * Real.sin (x * L)| := abs_add_le _ _
              _ ≤ 1 / 2 + |x| := by
                  rw [abs_mul, abs_mul]
                  have h1 : |(1:ℝ) / 2| * |Real.cos (x * L)| ≤ 1 / 2 := by
                    rw [show |(1:ℝ)/2| = 1/2 by norm_num]
                    nlinarith [abs_nonneg (Real.cos (x * L))]
                  have h2 : |x| * |Real.sin (x * L)| ≤ |x| := by
                    nlinarith [abs_nonneg x, abs_nonneg (Real.sin (x * L))]
                  linarith
          have hnn : (0:ℝ) ≤ Real.exp (L / 2) := hA.le
          have := mul_le_mul_of_nonneg_left this hnn
          rw [show |(1:ℝ)/2| = 1/2 by norm_num]
          linarith

/-- For a window of size at least `e` and any frequency at least `9`, the pole
profile is strictly smaller in modulus than its zero-frequency value. -/
theorem poleProfile_abs_lt_zero_freq {L x : ℝ} (hL : 1 ≤ L) (hx : 9 ≤ x) :
    |poleProfile L x| < poleProfile L 0 := by
  have hA : (3 : ℝ) / 2 ≤ Real.exp (L / 2) := by
    have h1 : 1 + L / 2 ≤ Real.exp (L / 2) := by
      have := Real.add_one_le_exp (L / 2)
      linarith
    linarith
  have hden : (0 : ℝ) < 1 / 4 + x ^ 2 := by positivity
  have hxpos : (0 : ℝ) < x := by linarith
  have habs : |x| = x := abs_of_pos hxpos
  have hbound := poleProfile_abs_le L x
  rw [habs] at hbound
  have hzero : poleProfile L 0 = 2 * (Real.exp (L / 2) - 1) := poleProfile_zero_freq L
  have hkey : (Real.exp (L / 2) * (1 / 2 + x) + 1 / 2) / (1 / 4 + x ^ 2)
      < 2 * (Real.exp (L / 2) - 1) := by
    rw [div_lt_iff₀ hden]
    nlinarith [hA, hx, sq_nonneg x, sq_nonneg (x - 9)]
  rw [hzero]
  linarith

/-- The literal pole-profile row at the three samples. -/
def poleProfileRow (L : ℝ) : Fin 3 → ℂ := fun j => ((poleProfile L (gridSamples j) : ℝ) : ℂ)

theorem gridSamples_two_ge_nine : (9 : ℝ) ≤ gridSamples 2 := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlog : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have : gridSamples 2 = 2 * Real.pi / Real.log 2 := by simp [gridSamples]
  rw [this, le_div_iff₀ hlogpos]
  nlinarith

/-- The exterior minor of the prime powers `2` and `4` against the literal pole
profile row is nonzero. -/
theorem augDet3_modeVector_two_four_ne_zero {L : ℝ} (hL : 1 ≤ L) :
    augDet3 (modeVector gridSamples (primeLogFreq 2)) (modeVector gridSamples (primeLogFreq 4))
      (poleProfileRow L) ≠ 0 := by
  rw [augDet3_modeVector_two_four]
  have hlt : |poleProfile L (gridSamples 2)| < poleProfile L 0 :=
    poleProfile_abs_lt_zero_freq hL gridSamples_two_ge_nine
  have h0 : gridSamples 0 = 0 := by simp [gridSamples]
  have hne : poleProfile L (gridSamples 2) ≠ poleProfile L (gridSamples 0) := by
    rw [h0]
    intro h
    rw [h] at hlt
    exact absurd hlt (not_lt.mpr (le_abs_self _))
  simp only [poleProfileRow]
  intro h
  apply hne
  have h2 : ((poleProfile L (gridSamples 2) : ℝ) : ℂ) = ((poleProfile L (gridSamples 0) : ℝ) : ℂ) := by
    linear_combination h / 2
  exact_mod_cast h2

/-! ## The literal prime pair kernel is nonzero, nonseparable and of rank > 1 -/

/-- The literal prime pair kernel of the G21 architecture. -/
def primePairKernel (L : ℝ) (r t : ℕ) : ℂ :=
  pairKernel vonMangoldtAmp primeLogFreq
    (fun r t => augDet3 (modeVector gridSamples (primeLogFreq r))
      (modeVector gridSamples (primeLogFreq t)) (poleProfileRow L)) r t

theorem primePairKernel_diag (L : ℝ) (n : ℕ) : primePairKernel L n n = 0 :=
  pairKernel_diag _ _ _ n

theorem primePairKernel_symm (L : ℝ) (r t : ℕ) :
    primePairKernel L t r = primePairKernel L r t := by
  refine pairKernel_symm ?_ r t
  intro r' t'
  exact augDet3_antisymm _ _ _

theorem vonMangoldtAmp_two_ne_zero : vonMangoldtAmp 2 ≠ 0 := by
  have hΛ : Λ 2 = Real.log 2 := by
    simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  simp only [vonMangoldtAmp, hΛ]
  refine div_ne_zero ?_ ?_
  · exact_mod_cast (ne_of_gt hpos)
  · have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    simp only [ne_eq, Complex.ofReal_eq_zero]
    push_cast
    exact ne_of_gt this

theorem vonMangoldtAmp_four_ne_zero : vonMangoldtAmp 4 ≠ 0 := by
  have hΛ : Λ 4 = Real.log 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num)]
    simp [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  simp only [vonMangoldtAmp, hΛ]
  refine div_ne_zero ?_ ?_
  · exact_mod_cast (ne_of_gt hpos)
  · have : (0 : ℝ) < Real.sqrt 4 := Real.sqrt_pos.mpr (by norm_num)
    simp only [ne_eq, Complex.ofReal_eq_zero]
    push_cast
    exact ne_of_gt this

/-- **The literal nonvanishing witness.**  At the prime powers `2` and `4` the
surviving pair kernel is nonzero. -/
theorem primePairKernel_two_four_ne_zero {L : ℝ} (hL : 1 ≤ L) : primePairKernel L 2 4 ≠ 0 := by
  have hfreq : (primeLogFreq 4 : ℂ) - (primeLogFreq 2 : ℂ) ≠ 0 := by
    have h : primeLogFreq 4 - primeLogFreq 2 = Real.log 2 := by
      rw [primeLogFreq_four]; simp [primeLogFreq]; ring
    intro hz
    have : ((primeLogFreq 4 - primeLogFreq 2 : ℝ) : ℂ) = 0 := by push_cast; linear_combination hz
    rw [h] at this
    exact log_two_ne_zero (by exact_mod_cast this)
  simp only [primePairKernel, pairKernel]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero vonMangoldtAmp_two_ne_zero
    vonMangoldtAmp_four_ne_zero) hfreq) (augDet3_modeVector_two_four_ne_zero hL)

/-- **`NonseparablePrimePairKernel`, literally.** -/
theorem primePairKernel_nonseparable {L : ℝ} (hL : 1 ≤ L) :
    ¬ ∃ Lft Rgt : ℕ → ℂ, ∀ r t, primePairKernel L r t = Lft r + Rgt t :=
  not_separable_of_ne_zero (primePairKernel_symm L) (primePairKernel_diag L)
    (primePairKernel_two_four_ne_zero hL)

/-- **`PrimePairRankGreaterThanOne`, literally.** -/
theorem primePairKernel_not_rankOne {L : ℝ} (hL : 1 ≤ L) :
    ¬ ∃ A Bc : ℕ → ℂ, ∀ r t, primePairKernel L r t = A r * Bc t :=
  not_rankOne_of_ne_zero (primePairKernel_symm L) (primePairKernel_diag L)
    (primePairKernel_two_four_ne_zero hL)

/-- The explicit four-point rectangle defect of the literal kernel is `−2K(2,4) ≠ 0`. -/
theorem primePairKernel_rectangleDefect {L : ℝ} (hL : 1 ≤ L) :
    primePairKernel L 2 2 + primePairKernel L 4 4 - primePairKernel L 2 4
        - primePairKernel L 4 2 = -2 * primePairKernel L 2 4
      ∧ primePairKernel L 2 4 ≠ 0 :=
  ⟨rectangleDefect_eq (primePairKernel_symm L) (primePairKernel_diag L) 2 4,
    primePairKernel_two_four_ne_zero hL⟩

/-! ## The literal zero-side response and the red gate -/

/-- The frequency `w = ρ − 1/2 + i x` of a zero `ρ` at observation sample `x`. -/
def zeroFreq (rho : ℂ) (x : ℝ) : ℂ := rho - 1 / 2 + Complex.I * (x : ℂ)

/-- The literal truncated single-zero response
`Z_ρ(x) = ∫_0^L e^{(ρ−1/2+ix)u} du`. -/
def zeroResponse (L : ℝ) (rho : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (zeroFreq rho x * (L : ℂ)) - 1) / zeroFreq rho x

theorem zeroResponse_eq_integral {L : ℝ} {rho : ℂ} {x : ℝ} (h : zeroFreq rho x ≠ 0) :
    zeroResponse L rho x = ∫ u in (0:ℝ)..L, Complex.exp (zeroFreq rho x * (u : ℂ)) := by
  rw [integral_exp_mul_complex h]
  simp [zeroResponse]

/-- The contrastive-derivative channel of the literal zero response. -/
def zeroResponseDeriv (L : ℝ) (rho : ℂ) (x : ℝ) : ℂ :=
  Complex.I * ((L : ℂ) * Complex.exp (zeroFreq rho x * (L : ℂ)) * zeroFreq rho x
    - (Complex.exp (zeroFreq rho x * (L : ℂ)) - 1)) / (zeroFreq rho x) ^ 2

/-- Channel two of the zero side really is the `x`-derivative of channel one. -/
theorem hasDerivAt_zeroResponse {L : ℝ} {rho : ℂ} {x : ℝ} (h : zeroFreq rho x ≠ 0) :
    HasDerivAt (fun y : ℝ => zeroResponse L rho y) (zeroResponseDeriv L rho x) x := by
  have hw : HasDerivAt (fun y : ℝ => zeroFreq rho y) Complex.I x := by
    have h0 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
    have := (h0.const_mul Complex.I).const_add (rho - 1 / 2)
    simpa [zeroFreq] using this
  have hexp : HasDerivAt (fun y : ℝ => Complex.exp (zeroFreq rho y * (L : ℂ)))
      (Complex.exp (zeroFreq rho x * (L : ℂ)) * (Complex.I * (L : ℂ))) x := by
    have := (hw.mul_const ((L : ℂ))).cexp
    simpa using this
  have hnum : HasDerivAt (fun y : ℝ => Complex.exp (zeroFreq rho y * (L : ℂ)) - 1)
      (Complex.exp (zeroFreq rho x * (L : ℂ)) * (Complex.I * (L : ℂ))) x := by
    simpa using hexp.sub_const 1
  have hdiv := hnum.div hw h
  refine hdiv.congr_deriv ?_
  simp only [zeroResponseDeriv]
  field_simp

/-- Both zero-side channels are holomorphic in the zero parameter wherever the
frequency does not vanish. -/
theorem differentiableOn_zeroResponse (L x : ℝ) {U : Set ℂ}
    (hU : ∀ z ∈ U, zeroFreq z x ≠ 0) :
    DifferentiableOn ℂ (fun rho => zeroResponse L rho x) U := by
  have hw : DifferentiableOn ℂ (fun rho : ℂ => zeroFreq rho x) U := by
    simp only [zeroFreq]
    fun_prop
  have hnum : DifferentiableOn ℂ
      (fun rho : ℂ => Complex.exp (zeroFreq rho x * (L : ℂ)) - 1) U := by
    exact ((hw.mul_const ((L : ℂ))).cexp).sub_const 1
  exact hnum.div hw hU

theorem differentiableOn_zeroResponseDeriv (L x : ℝ) {U : Set ℂ}
    (hU : ∀ z ∈ U, zeroFreq z x ≠ 0) :
    DifferentiableOn ℂ (fun rho => zeroResponseDeriv L rho x) U := by
  have hw : DifferentiableOn ℂ (fun rho : ℂ => zeroFreq rho x) U := by
    simp only [zeroFreq]
    fun_prop
  have hnum : DifferentiableOn ℂ
      (fun rho : ℂ => Complex.I * ((L : ℂ) * Complex.exp (zeroFreq rho x * (L : ℂ))
        * zeroFreq rho x - (Complex.exp (zeroFreq rho x * (L : ℂ)) - 1))) U := by
    have hexp : DifferentiableOn ℂ
        (fun rho : ℂ => Complex.exp (zeroFreq rho x * (L : ℂ))) U := (hw.mul_const ((L : ℂ))).cexp
    exact (((hexp.const_mul ((L : ℂ))).mul hw).sub (hexp.sub_const 1)).const_mul Complex.I
  have hden : ∀ z ∈ U, (zeroFreq z x) ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (hU z hz)
  exact hnum.div (hw.pow 2) hden

/-- The literal zero-side exterior observable. -/
def zeroSideObservable (L : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ) (rho : ℂ) : ℂ :=
  augDet3 (fun j => zeroResponse L rho (x j)) (fun j => zeroResponseDeriv L rho (x j)) m

theorem differentiableOn_zeroSideObservable (L : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ) {U : Set ℂ}
    (hU : ∀ z ∈ U, ∀ j, zeroFreq z (x j) ≠ 0) :
    DifferentiableOn ℂ (zeroSideObservable L x m) U := by
  refine differentiableOn_augDet3_of_rows _ _ m ?_ ?_
  · intro j
    exact differentiableOn_zeroResponse L (x j) (fun z hz => hU z hz j)
  · intro j
    exact differentiableOn_zeroResponseDeriv L (x j) (fun z hz => hU z hz j)

/-- **G21 lemma 3 is red for the literal truncated zero response.**  The
augmented determinant of the literal single-zero two-channel response is
holomorphic in `ρ`, so it cannot vanish for the on-line zero parameters of a
disc centred on the critical line and be nonzero for an off-line parameter of
that disc: the observable has no critical-line gate. -/
theorem zeroSideObservable_no_criticalLine_separation (L : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ)
    {rho0 : ℂ} {r : ℝ} (hr : 0 < r) (hre : rho0.re = 1 / 2)
    (hU : ∀ z ∈ Metric.ball rho0 r, ∀ j, zeroFreq z (x j) ≠ 0) :
    ¬ ((∀ z ∈ Metric.ball rho0 r, z.re = 1 / 2 → zeroSideObservable L x m z = 0)
        ∧ ∃ z ∈ Metric.ball rho0 r, z.re ≠ 1 / 2 ∧ zeroSideObservable L x m z ≠ 0) :=
  no_criticalLine_separation hr (differentiableOn_zeroSideObservable L x m hU) hre

/-! ### The same verdict for the repaired four-sample architecture -/

/-- Determinants of holomorphic matrix families are holomorphic. -/
theorem differentiableOn_det {n : ℕ} {U : Set ℂ} (M : ℂ → Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ i j, DifferentiableOn ℂ (fun z => M z i j) U) :
    DifferentiableOn ℂ (fun z => (M z).det) U := by
  have heq : (fun z => (M z).det)
      = ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))),
          fun z => (Equiv.Perm.sign σ : ℂ) * ∏ i ∈ Finset.univ, M z (σ i) i := by
    funext z
    rw [Finset.sum_apply]
    exact Matrix.det_apply' (M z)
  rw [heq]
  refine DifferentiableOn.sum (fun σ _ => ?_)
  have hprod : DifferentiableOn ℂ
      (fun z => ∏ i ∈ (Finset.univ : Finset (Fin n)), M z (σ i) i) U := by
    have hp := DifferentiableOn.finset_prod (u := (Finset.univ : Finset (Fin n)))
      (f := fun i => fun z => M z (σ i) i) (s := U) (fun i _ => h (σ i) i)
    refine hp.congr ?_
    intro z _
    rw [Finset.prod_apply]
  exact hprod.const_mul _

theorem differentiableOn_augDet4_of_rows {U : Set ℂ} (u w : ℂ → (Fin 4 → ℂ)) (p q : Fin 4 → ℂ)
    (hu : ∀ j, DifferentiableOn ℂ (fun z => u z j) U)
    (hw : ∀ j, DifferentiableOn ℂ (fun z => w z j) U) :
    DifferentiableOn ℂ (fun z => augDet4 (u z) (w z) p q) U := by
  refine differentiableOn_det (fun z => Matrix.of ![u z, w z, p, q]) ?_
  intro i j
  fin_cases i <;> simp only [Matrix.of_apply]
  · exact hu j
  · exact hw j
  · exact differentiableOn_const (p j)
  · exact differentiableOn_const (q j)

/-- The literal zero-side exterior observable of the repaired architecture: four
samples, and both pole profiles `p = m`, `q = m′` adjoined as nuisance rows. -/
def zeroSideObservable4 (L : ℝ) (x : Fin 4 → ℝ) (p q : Fin 4 → ℂ) (rho : ℂ) : ℂ :=
  augDet4 (fun j => zeroResponse L rho (x j)) (fun j => zeroResponseDeriv L rho (x j)) p q

/-- **Lemma 3 stays red in the repaired four-sample architecture.** -/
theorem zeroSideObservable4_no_criticalLine_separation (L : ℝ) (x : Fin 4 → ℝ) (p q : Fin 4 → ℂ)
    {rho0 : ℂ} {r : ℝ} (hr : 0 < r) (hre : rho0.re = 1 / 2)
    (hU : ∀ z ∈ Metric.ball rho0 r, ∀ j, zeroFreq z (x j) ≠ 0) :
    ¬ ((∀ z ∈ Metric.ball rho0 r, z.re = 1 / 2 → zeroSideObservable4 L x p q z = 0)
        ∧ ∃ z ∈ Metric.ball rho0 r, z.re ≠ 1 / 2 ∧ zeroSideObservable4 L x p q z ≠ 0) := by
  refine no_criticalLine_separation hr ?_ hre
  refine differentiableOn_augDet4_of_rows _ _ p q ?_ ?_
  · intro j
    exact differentiableOn_zeroResponse L (x j) (fun z hz => hU z hz j)
  · intro j
    exact differentiableOn_zeroResponseDeriv L (x j) (fun z hz => hU z hz j)

/-- **The zero side is diagonal-free as well.**  For a zero-mode family
`Z(x) = ∑_ρ a_ρ e^{ixγ_ρ}` with its contrastive-derivative channel, the exterior
observable is a sum over pairs of *distinct* zeros: every self-energy term
`ρ = ρ'` — which is where a positivity-based detector keeps the whole off-line
signal — is annihilated by the same mechanism that kills the pole. -/
theorem zeroSide_pairKernel_no_diagonal {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (amp : ι → ℂ) (gam : ι → ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ) :
    augDet3 (∑ r ∈ s, amp r • modeVector x (gam r))
        (∑ t ∈ s, (Complex.I * (gam t : ℂ) * amp t) • modeVector x (gam t)) m
      = Complex.I * ∑ z ∈ (s ×ˢ s).filter (fun z => z.1 < z.2),
          pairKernel amp gam
            (fun r t => augDet3 (modeVector x (gam r)) (modeVector x (gam t)) m) z.1 z.2 :=
  augDet3_channelPair_eq_pairKernel s amp gam x m

/-! ## The G21 decision -/

/-- **`twoChannelGateDecision`.**  The three verified facts that decide the
experiment: (i) the pole-quotiented exterior observable annihilates the common
mode and all mixed terms *exactly*; (ii) it also annihilates every single-mode
(single-zero) response exactly, whatever its amplitude; (iii) consequently no
`c·height^p·|α|^q` floor for an off-line zero can be established from it. -/
theorem twoChannelGateDecision (l : ℝ) (x : Fin 3 → ℝ) (m : Fin 3 → ℂ)
    {cc height : ℝ} (hc : 0 < cc) (hheight : 0 < height) (p q : ℕ) :
    (∀ (c₁ c₂ : ℂ) (E₁ E₂ : Fin 3 → ℂ),
        augDet3 (fun j => c₁ * m j + E₁ j) (fun j => c₂ * m j + E₂ j) m = augDet3 E₁ E₂ m)
      ∧ (∀ a : ℂ,
        augDet3 (a • modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l) m = 0)
      ∧ ¬ ∀ (alpha : ℝ) (a : ℂ), alpha ≠ 0 →
          cc * height ^ p * |alpha| ^ q
            ≤ ‖augDet3 (a • modeVector x l) ((Complex.I * (l : ℂ) * a) • modeVector x l) m‖ :=
  ⟨fun c₁ c₂ E₁ E₂ => augDet3_pole_annihilation c₁ c₂ m E₁ E₂,
    fun a => augDet3_singleMode_annihilated a l x m,
    singleMode_gate_no_floor l x m hc hheight p q⟩

end

end RiemannAnalytic

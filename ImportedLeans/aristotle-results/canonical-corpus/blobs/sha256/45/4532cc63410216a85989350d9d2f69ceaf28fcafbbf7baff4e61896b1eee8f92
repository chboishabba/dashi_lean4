import Mathlib
import RequestProject.Tesla369
import RequestProject.DeltaGraph

/-!
# 3, 6, 9 and the Riemann zeta function

`Tesla369` fixed the trinity: the digital root of a positive integer lies in `{3, 6, 9}` exactly
when the integer is a multiple of three (`Tesla369.digitalRoot_mem_trinity_iff`).  The
coefficient files then read that trinity off the `q`-expansions of `Δ` and of the moonshine
hauptmoduls.  The Riemann zeta function is the opposite case: **all** of its Dirichlet
coefficients are `1`, so nothing at all can be read off them.  The trinity sits instead in the
*indices*, and there it is exact.

## Main results

* `tsum_trinity` — the part of `ζ(s)` carried by the trinity indices (those `n > 0` whose digital
  root is `3`, `6` or `9`) is exactly `3^{-s} ζ(s)`: the trinity is a perfect self-similar copy
  of the whole, scaled by `3^{-s}`.  At `s = 2` (`tsum_trinity_two`) it is `π²/54`.
* `tsum_nontrinity` — everything else is `(1 - 3^{-s}) ζ(s)`, i.e. exactly Euler's factor at the
  prime three, removed.
* `trinity_density` — at `s = 1` the scaling factor `3^{-s}` is `1/3`: one index in three.
* `riemannZeta_six`, and the digital roots of the denominators of `ζ(2), ζ(4), ζ(6)`
  (`digitalRoot_zeta_even_denominators` : `6, 9, 9`).
* `riemannZeta_neg_one`, `riemannZeta_neg_three`, `riemannZeta_neg_five` and
  `eisenstein_constants_from_zeta` — the three constants that build the modular forms of this
  project are the first three odd negative zeta values:
  `24 = -2/ζ(-1)`, `240 = 2/ζ(-3)`, `504 = -2/ζ(-5)`, with digital roots `6, 6, 9`
  (`digitalRoot_eisenstein_constants`).  The `24` is the exponent in `Δ = q ∏(1-qⁿ)²⁴`, the `240`
  is the multiplier of `E₄` used in `Moonshine369.E4`, and `504` is the multiplier of `E₆`.
* `zeta_neg_five_eq_neg_inv_tau_three` — a coincidence worth recording: the denominator of
  `ζ(-5)` is `252 = τ(3)`, the third coefficient of `Δ`.
* `riemannZeta_neg_six` — the trivial zero at `-6`.
-/

namespace Zeta369

open Complex Tesla369

/-! ## The trinity indices -/

/-- The **trinity indices**: the positive integers whose digital root is `3`, `6` or `9`. -/
def trinityIdx : Set ℕ := {n | 0 < n ∧ digitalRoot n ∈ trinity}

/-- The trinity indices are exactly the positive multiples of three. -/
theorem mem_trinityIdx_iff {n : ℕ} : n ∈ trinityIdx ↔ 0 < n ∧ 3 ∣ n := by
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, (digitalRoot_mem_trinity_iff hn).mp h⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, (digitalRoot_mem_trinity_iff hn).mpr h⟩

/-- The **non-trinity indices**: the positive integers not divisible by three. -/
def nonTrinityIdx : Set ℕ := {n | 0 < n ∧ ¬ (3 ∣ n)}

theorem mem_nonTrinityIdx_iff {n : ℕ} : n ∈ nonTrinityIdx ↔ 0 < n ∧ digitalRoot n ∉ trinity := by
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun hc => h ((digitalRoot_mem_trinity_iff hn).mp hc)⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun hc => h ((digitalRoot_mem_trinity_iff hn).mpr hc)⟩

/-- The trinity indices are the positive multiples of three, as a set. -/
theorem trinityIdx_eq : trinityIdx = {n : ℕ | 0 < n ∧ 3 ∣ n} :=
  Set.ext fun _ => mem_trinityIdx_iff

/-- The positive multiples of `m`, enumerated: `n ↦ m(n+1)`. -/
def multiplesEquiv {m : ℕ} (hm : 0 < m) : ℕ ≃ {n : ℕ | 0 < n ∧ m ∣ n} where
  toFun n := ⟨m * (n + 1), by positivity, ⟨n + 1, rfl⟩⟩
  invFun x := x.1 / m - 1
  left_inv n := by
    simp [Nat.mul_div_cancel_left _ hm]
  right_inv := by
    rintro ⟨n, hpos, k, rfl⟩
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hpos
      · exact h
    ext
    simp only []
    rw [Nat.mul_div_cancel_left _ hm]
    congr 1
    omega

/-! ## The trinity part of `ζ` -/

/-- **A scaled copy of `ζ` on the multiples of `m`.** For `Re s > 1` the part of the Dirichlet
series of `ζ` supported on the positive multiples of `m` is exactly `m^{-s} ζ(s)`.  Nothing here
is special to three; the trinity is the case `m = 3`. -/
theorem tsum_multiples {m : ℕ} (hm : 0 < m) {s : ℂ} (hs : 1 < s.re) :
    ∑' x : {n : ℕ | 0 < n ∧ m ∣ n}, 1 / ((x : ℕ) : ℂ) ^ s = (m : ℂ) ^ (-s) * riemannZeta s := by
  rw [← (multiplesEquiv hm).tsum_eq (fun x : {n : ℕ | 0 < n ∧ m ∣ n} => 1 / ((x : ℕ) : ℂ) ^ s)]
  have key : ∀ n : ℕ,
      (1 : ℂ) / (((multiplesEquiv hm n : {n : ℕ | 0 < n ∧ m ∣ n}) : ℕ) : ℂ) ^ s
        = (m : ℂ) ^ (-s) * (1 / ((n : ℂ) + 1) ^ s) := by
    intro n
    show (1 : ℂ) / ((m * (n + 1) : ℕ) : ℂ) ^ s = _
    have h : ((m * (n + 1) : ℕ) : ℂ)
        = Complex.ofReal ((m : ℝ)) * Complex.ofReal ((n : ℝ) + 1) := by
      push_cast; ring
    rw [h, Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), Complex.cpow_neg]
    push_cast
    field_simp
  rw [tsum_congr key, tsum_mul_left, ← zeta_eq_tsum_one_div_nat_add_one_cpow hs]

/-- **The trinity carries a perfect copy of `ζ`.** For `Re s > 1` the part of the Dirichlet
series of `ζ` supported on the indices with digital root `3`, `6` or `9` is exactly
`3^{-s} ζ(s)`. -/
theorem tsum_trinity {s : ℂ} (hs : 1 < s.re) :
    ∑' x : trinityIdx, 1 / ((x : ℕ) : ℂ) ^ s = (3 : ℂ) ^ (-s) * riemannZeta s := by
  rw [trinityIdx_eq]
  simpa using tsum_multiples (m := 3) (by norm_num) hs

/-- **And the rest is Euler's factor at three, removed.** For `Re s > 1` the part of the
Dirichlet series of `ζ` supported on the indices *outside* the trinity is `(1 - 3^{-s}) ζ(s)`. -/
theorem tsum_nontrinity {s : ℂ} (hs : 1 < s.re) :
    ∑' x : nonTrinityIdx, 1 / ((x : ℕ) : ℂ) ^ s = (1 - (3 : ℂ) ^ (-s)) * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs; linarith
  have hzero : (1 : ℂ) / ((0 : ℕ) : ℂ) ^ s = 0 := by
    simp [Complex.zero_cpow hs0]
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  -- the complement of the trinity indices differs from `nonTrinityIdx` only at `0`,
  -- where the summand vanishes
  have hind : Set.indicator trinityIdxᶜ (fun n : ℕ => 1 / (n : ℂ) ^ s)
      = Set.indicator nonTrinityIdx (fun n : ℕ => 1 / (n : ℂ) ^ s) := by
    funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : (0 : ℕ) ∉ nonTrinityIdx := by simp [nonTrinityIdx]
      by_cases hm : (0 : ℕ) ∈ trinityIdxᶜ
      · rw [Set.indicator_of_mem hm, Set.indicator_of_notMem h0]
        exact hzero
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem h0]
    · have h1 : n ∈ trinityIdxᶜ ↔ n ∈ nonTrinityIdx := by
        simp only [Set.mem_compl_iff, mem_trinityIdx_iff, nonTrinityIdx, Set.mem_setOf_eq]
        constructor
        · intro h; exact ⟨hn, fun hd => h ⟨hn, hd⟩⟩
        · rintro ⟨-, h⟩ ⟨-, hd⟩; exact h hd
      by_cases h : n ∈ trinityIdxᶜ
      · have h2 : n ∈ nonTrinityIdx := h1.mp h
        rw [Set.indicator_of_mem h, Set.indicator_of_mem h2]
      · have h2 : n ∉ nonTrinityIdx := fun hc => h (h1.mpr hc)
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h2]
  have hsplit := Summable.tsum_add_tsum_compl (f := fun n : ℕ => 1 / (n : ℂ) ^ s)
    (s := trinityIdx) (hsum.subtype _) (hsum.subtype _)
  have h1 : ∑' x : (trinityIdxᶜ : Set ℕ), (fun n : ℕ => 1 / (n : ℂ) ^ s) x
      = ∑' x : nonTrinityIdx, (fun n : ℕ => 1 / (n : ℂ) ^ s) x := by
    rw [tsum_subtype (trinityIdxᶜ : Set ℕ) (fun n : ℕ => 1 / (n : ℂ) ^ s),
      tsum_subtype nonTrinityIdx (fun n : ℕ => 1 / (n : ℂ) ^ s), hind]
  rw [h1] at hsplit
  simp only [] at hsplit
  rw [tsum_trinity hs, ← zeta_eq_tsum_one_div_nat_cpow hs] at hsplit
  linear_combination hsplit

/-- **At `s = 2`:** the trinity indices carry `π²/54` of `ζ(2) = π²/6`. -/
theorem tsum_trinity_two :
    ∑' x : trinityIdx, 1 / ((x : ℕ) : ℂ) ^ (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 54 := by
  have h := tsum_trinity (s := 2) (by norm_num)
  rw [h, riemannZeta_two]
  have h3 : (3 : ℂ) ^ (-(2 : ℂ)) = 1 / 9 := by
    rw [Complex.cpow_neg, show ((2 : ℂ)) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    norm_num
  rw [h3]
  ring

/-- **One index in three.** The scaling factor `3^{-s}` of `tsum_trinity` is `1/3` at `s = 1`:
the trinity is a third of the integers, and the Dirichlet series knows it. -/
theorem trinity_density : (3 : ℝ) ^ (-(1 : ℝ)) = 1 / 3 := by
  rw [Real.rpow_neg_one]
  norm_num

/-! ## Zeta values, and the constants of this project -/

theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  have h2 : Nat.choose 6 2 = 15 := by decide
  have h3 : Nat.choose 6 3 = 20 := by decide
  have h4 : Nat.choose 6 4 = 15 := by decide
  have h5' : Nat.choose 6 5 = 6 := by decide
  have hc : Nat.choose 4 2 = 6 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, h2, h3, h4, h5, h5', hc]

theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_six]

theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]

/-- `ζ(6) = π⁶/945`, completing `riemannZeta_two` and `riemannZeta_four`. -/
theorem riemannZeta_six : riemannZeta 6 = (Real.pi : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  norm_num [bernoulli_six, Nat.factorial] at h
  rw [h]; ring

/-- **The trinity in the even zeta values.** The denominators of `ζ(2), ζ(4), ζ(6)` over the
matching power of `π` are `6, 90, 945`, whose digital roots are `6, 9, 9`. -/
theorem digitalRoot_zeta_even_denominators :
    (digitalRoot 6, digitalRoot 90, digitalRoot 945) = (6, 9, 9) := by decide

theorem riemannZeta_neg_one : riemannZeta (-1) = -1 / 12 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 1
  norm_num [bernoulli_two] at h
  rw [h]; ring

theorem riemannZeta_neg_three : riemannZeta (-3) = 1 / 120 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 3
  norm_num [bernoulli_four] at h
  exact h

theorem riemannZeta_neg_five : riemannZeta (-5) = -1 / 252 := by
  have h := riemannZeta_neg_nat_eq_bernoulli 5
  norm_num [bernoulli_six] at h
  rw [h]; ring

/-- **The modular constants of this project are zeta values.** The exponent `24` of
`Δ = q ∏ (1 - qⁿ)²⁴`, the multiplier `240` of `E₄` (which builds `j = E₄³/Δ`) and the multiplier
`504` of `E₆` are `-2/ζ(-1)`, `2/ζ(-3)` and `-2/ζ(-5)`. -/
theorem eisenstein_constants_from_zeta :
    (-2 / riemannZeta (-1) = (24 : ℂ) ∧ 2 / riemannZeta (-3) = (240 : ℂ))
      ∧ -2 / riemannZeta (-5) = (504 : ℂ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [riemannZeta_neg_one]; norm_num
  · rw [riemannZeta_neg_three]; norm_num
  · rw [riemannZeta_neg_five]; norm_num

/-- **Their digital roots are `6, 6, 9`** — the trinity again. -/
theorem digitalRoot_eisenstein_constants :
    (digitalRoot 24, digitalRoot 240, digitalRoot 504) = (6, 6, 9) := by decide

/-- The denominator of `ζ(-5)` is `252 = τ(3)`, the third coefficient of `Δ`. -/
theorem zeta_neg_five_eq_neg_inv_tau_three :
    riemannZeta (-5) = -1 / ((DeltaGraph.tau 3 : ℤ) : ℂ) := by
  rw [riemannZeta_neg_five, DeltaGraph.tau_three]
  norm_num

/-- The trivial zero at `-6`. -/
theorem riemannZeta_neg_six : riemannZeta (-6) = 0 := by
  have h := riemannZeta_neg_two_mul_nat_add_one 2
  norm_num at h
  exact h

end Zeta369

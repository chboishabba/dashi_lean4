/-
# Locating the crossings

`RequestProject/SporadicClosure.lean` shows that where two sporadic mass curves swap rank
between two integers they must meet somewhere in between (`SporadicClosure.janko_curves_cross`,
`SporadicClosure.bottom_curves_cross`). This file halves those intervals by evaluating the
curves at a *half-integer* `s`, where the local factors are polynomials in `p^{-3/2}` and
`p^{-5/2}` and can be bracketed by rational numbers:

* `J1` overtakes `J3` already before `s = 3/2`: `∑_{d ∣ |J3|} d^{-3/2} < 2.1417 < 2.168 <
  ∑_{d ∣ |J1|} d^{-3/2}`, so the crossing lies in `(1, 3/2)`;
* `M11` overtakes `J3` before `s = 5/2`, so that crossing lies in `(2, 5/2)`.

The bracketing is elementary: `x = p^{-k/2}` is positive with `x² · p^k = 1`, so a rational `l`
with `l²·p^k ≤ 1` is a lower bound and a rational `u` with `1 ≤ u²·p^k` an upper bound; the
local factors `1 + x + ⋯ + x^e` are monotone in `x`, and the whole mass is their product.
-/
import Mathlib
import RequestProject.SporadicClosure

open Finset

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SporadicCrossing

open Sporadic Lessons SporadicZeta SporadicSpectrum SporadicClosure

/-! ## Bracketing `p^{-k/2}` by rationals -/

/-- The square of `p^{-k/2}` is `p^{-k}`. -/
theorem sq_rpow_neg_half (p k : ℕ) : ((p : ℝ) ^ (-(k / 2 : ℝ))) ^ 2 = ((p : ℝ) ^ k)⁻¹ := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← Real.rpow_natCast ((p : ℝ) ^ (-(k / 2 : ℝ))) 2, ← Real.rpow_mul hp0,
    show -(k / 2 : ℝ) * (2 : ℕ) = -(k : ℝ) by push_cast; ring, Real.rpow_neg hp0,
    Real.rpow_natCast]

/-- **Rational brackets for a half-integer power.** A rational `l ≥ 0` with `l²·p^k ≤ 1` is
below `p^{-k/2}`, and a rational `u ≥ 0` with `1 ≤ u²·p^k` is above it. -/
theorem rpow_neg_half_bounds {p k : ℕ} (hp : 0 < p) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (h1 : l ^ 2 * (p : ℝ) ^ k ≤ 1) (h2 : 1 ≤ u ^ 2 * (p : ℝ) ^ k) :
    l ≤ (p : ℝ) ^ (-(k / 2 : ℝ)) ∧ (p : ℝ) ^ (-(k / 2 : ℝ)) ≤ u := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hx0 : 0 < (p : ℝ) ^ (-(k / 2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  have hkey : ((p : ℝ) ^ (-(k / 2 : ℝ))) ^ 2 * (p : ℝ) ^ k = 1 := by
    rw [sq_rpow_neg_half p k]; field_simp
  exact ⟨by nlinarith [hx0, hkey, hpk], by nlinarith [hx0, hkey, hpk]⟩

/-- The brackets at `s = 3/2`. -/
theorem rpow_bounds_three_halves (p : ℕ) (hp : 0 < p) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (h1 : l ^ 2 * (p : ℝ) ^ 3 ≤ 1) (h2 : 1 ≤ u ^ 2 * (p : ℝ) ^ 3) :
    l ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) ∧ (p : ℝ) ^ (-(3 / 2 : ℝ)) ≤ u := by
  have h := rpow_neg_half_bounds (p := p) (k := 3) hp hl hu (by linarith)
    (by linarith)
  norm_num at h
  exact h

/-- The brackets at `s = 5/2`. -/
theorem rpow_bounds_five_halves (p : ℕ) (hp : 0 < p) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (h1 : l ^ 2 * (p : ℝ) ^ 5 ≤ 1) (h2 : 1 ≤ u ^ 2 * (p : ℝ) ^ 5) :
    l ≤ (p : ℝ) ^ (-(5 / 2 : ℝ)) ∧ (p : ℝ) ^ (-(5 / 2 : ℝ)) ≤ u := by
  have h := rpow_neg_half_bounds (p := p) (k := 5) hp hl hu (by linarith)
    (by linarith)
  norm_num at h
  exact h

/-! ## Bracketing a local factor -/

/-- A lower bound for `p^{-s}` gives a lower bound for the local factor. -/
theorem truncFactor_ge_of {p e : ℕ} {s l c : ℝ} (hl : 0 ≤ l) (h : l ≤ (p : ℝ) ^ (-s))
    (hc : c ≤ ∑ j ∈ Finset.range (e + 1), l ^ j) : c ≤ truncFactor p e s :=
  hc.trans (Finset.sum_le_sum fun j _ => by gcongr)

/-- An upper bound for `p^{-s}` gives an upper bound for the local factor. -/
theorem truncFactor_le_of {p e : ℕ} (hp : 0 < p) {s u c : ℝ} (h : (p : ℝ) ^ (-s) ≤ u)
    (hc : ∑ j ∈ Finset.range (e + 1), u ^ j ≤ c) : truncFactor p e s ≤ c := by
  refine le_trans ?_ hc
  have h0 : (0 : ℝ) ≤ (p : ℝ) ^ (-s) :=
    le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp) _)
  exact Finset.sum_le_sum fun j _ => by gcongr

/-! ## The two masses at `s = 3/2` -/

/-- `∑_{d ∣ |J1|} d^{-3/2} > 2.168`. -/
theorem janko1_three_halves_lower : (2168 : ℝ) / 1000 ≤ divisorSum janko1.order (3 / 2) := by
  have b2 := rpow_bounds_three_halves 2 (by norm_num) (l := 3535533 / 10000000)
    (u := 3535534 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rpow_bounds_three_halves 3 (by norm_num) (l := 1924500 / 10000000)
    (u := 1924501 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b5 := rpow_bounds_three_halves 5 (by norm_num) (l := 894427 / 10000000)
    (u := 894428 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b7 := rpow_bounds_three_halves 7 (by norm_num) (l := 539949 / 10000000)
    (u := 539950 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b11 := rpow_bounds_three_halves 11 (by norm_num) (l := 274101 / 10000000)
    (u := 274102 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b19 := rpow_bounds_three_halves 19 (by norm_num) (l := 120745 / 10000000)
    (u := 120746 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f2 : (15227473 : ℝ) / 10000000 ≤ truncFactor 2 3 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b2.1 (by norm_num [Finset.sum_range_succ])
  have f3 : (119245 : ℝ) / 100000 ≤ truncFactor 3 1 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b3.1 (by norm_num [Finset.sum_range_succ])
  have f5 : (10894427 : ℝ) / 10000000 ≤ truncFactor 5 1 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b5.1 (by norm_num [Finset.sum_range_succ])
  have f7 : (10539949 : ℝ) / 10000000 ≤ truncFactor 7 1 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b7.1 (by norm_num [Finset.sum_range_succ])
  have f11 : (10274101 : ℝ) / 10000000 ≤ truncFactor 11 1 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b11.1 (by norm_num [Finset.sum_range_succ])
  have f19 : (10120745 : ℝ) / 10000000 ≤ truncFactor 19 1 (3 / 2) :=
    truncFactor_ge_of (by norm_num) b19.1 (by norm_num [Finset.sum_range_succ])
  rw [divisorSum_order (3 / 2) janko1_mem]
  simp only [janko1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  calc (2168 : ℝ) / 1000
      ≤ (15227473 / 10000000) * ((119245 / 100000) * ((10894427 / 10000000) *
          ((10539949 / 10000000) * ((10274101 / 10000000) * ((10120745 / 10000000) * 1))))) := by
        norm_num
    _ ≤ truncFactor 2 3 (3 / 2) * (truncFactor 3 1 (3 / 2) * (truncFactor 5 1 (3 / 2) *
          (truncFactor 7 1 (3 / 2) * (truncFactor 11 1 (3 / 2) *
            (truncFactor 19 1 (3 / 2) * 1))))) := by
        gcongr

/-- `∑_{d ∣ |J3|} d^{-3/2} < 2.1417`. -/
theorem janko3_three_halves_upper : divisorSum janko3.order (3 / 2) ≤ (21417 : ℝ) / 10000 := by
  have b2 := rpow_bounds_three_halves 2 (by norm_num) (l := 3535533 / 10000000)
    (u := 3535534 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rpow_bounds_three_halves 3 (by norm_num) (l := 1924500 / 10000000)
    (u := 1924501 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b5 := rpow_bounds_three_halves 5 (by norm_num) (l := 894427 / 10000000)
    (u := 894428 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b17 := rpow_bounds_three_halves 17 (by norm_num) (l := 142668 / 10000000)
    (u := 142669 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b19 := rpow_bounds_three_halves 19 (by norm_num) (l := 120745 / 10000000)
    (u := 120746 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f2 : truncFactor 2 7 (3 / 2) ≤ (15465406 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b2.2 (by norm_num [Finset.sum_range_succ])
  have f3 : truncFactor 3 5 (3 / 2) ≤ (12382507 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b3.2 (by norm_num [Finset.sum_range_succ])
  have f5 : truncFactor 5 1 (3 / 2) ≤ (10894429 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b5.2 (by norm_num [Finset.sum_range_succ])
  have f17 : truncFactor 17 1 (3 / 2) ≤ (1014267 : ℝ) / 1000000 :=
    truncFactor_le_of (by norm_num) b17.2 (by norm_num [Finset.sum_range_succ])
  have f19 : truncFactor 19 1 (3 / 2) ≤ (10120747 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b19.2 (by norm_num [Finset.sum_range_succ])
  rw [divisorSum_order (3 / 2) janko3_mem]
  simp only [janko3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  simp only [truncFactor] at f2 f3 f5 f17 f19 ⊢
  calc _
      ≤ (15465406 / 10000000) * ((12382507 / 10000000) * ((10894429 / 10000000) *
          ((1014267 / 1000000) * ((10120747 / 10000000) * 1)))) := by
        gcongr
    _ ≤ (21417 : ℝ) / 10000 := by norm_num

/-! ## The two masses at `s = 5/2` -/

/-- `∑_{d ∣ |M11|} d^{-5/2} > 1.32393`. -/
theorem mathieu11_five_halves_lower :
    (132393 : ℝ) / 100000 ≤ divisorSum mathieu11.order (5 / 2) := by
  have b2 := rpow_bounds_five_halves 2 (by norm_num) (l := 1767766 / 10000000)
    (u := 1767767 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rpow_bounds_five_halves 3 (by norm_num) (l := 641500 / 10000000)
    (u := 641501 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b5 := rpow_bounds_five_halves 5 (by norm_num) (l := 178885 / 10000000)
    (u := 178886 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b11 := rpow_bounds_five_halves 11 (by norm_num) (l := 24918 / 10000000)
    (u := 24919 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f2 : (12145273 : ℝ) / 10000000 ≤ truncFactor 2 4 (5 / 2) :=
    truncFactor_ge_of (by norm_num) b2.1 (by norm_num [Finset.sum_range_succ])
  have f3 : (10682652 : ℝ) / 10000000 ≤ truncFactor 3 2 (5 / 2) :=
    truncFactor_ge_of (by norm_num) b3.1 (by norm_num [Finset.sum_range_succ])
  have f5 : (10178885 : ℝ) / 10000000 ≤ truncFactor 5 1 (5 / 2) :=
    truncFactor_ge_of (by norm_num) b5.1 (by norm_num [Finset.sum_range_succ])
  have f11 : (10024918 : ℝ) / 10000000 ≤ truncFactor 11 1 (5 / 2) :=
    truncFactor_ge_of (by norm_num) b11.1 (by norm_num [Finset.sum_range_succ])
  rw [divisorSum_order (5 / 2) mathieu11_mem]
  simp only [mathieu11, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  calc (132393 : ℝ) / 100000
      ≤ (12145273 / 10000000) * ((10682652 / 10000000) * ((10178885 / 10000000) *
          ((10024918 / 10000000) * 1))) := by norm_num
    _ ≤ truncFactor 2 4 (5 / 2) * (truncFactor 3 2 (5 / 2) * (truncFactor 5 1 (5 / 2) *
          (truncFactor 11 1 (5 / 2) * 1))) := by gcongr

/-- `∑_{d ∣ |J3|} d^{-5/2} < 1.323173`. -/
theorem janko3_five_halves_upper :
    divisorSum janko3.order (5 / 2) ≤ (1323173 : ℝ) / 1000000 := by
  have b2 := rpow_bounds_five_halves 2 (by norm_num) (l := 1767766 / 10000000)
    (u := 1767767 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b3 := rpow_bounds_five_halves 3 (by norm_num) (l := 641500 / 10000000)
    (u := 641501 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b5 := rpow_bounds_five_halves 5 (by norm_num) (l := 178885 / 10000000)
    (u := 178886 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b17 := rpow_bounds_five_halves 17 (by norm_num) (l := 8392 / 10000000)
    (u := 8393 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have b19 := rpow_bounds_five_halves 19 (by norm_num) (l := 6355 / 10000000)
    (u := 6356 / 10000000) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have f2 : truncFactor 2 7 (5 / 2) ≤ (12147361 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b2.2 (by norm_num [Finset.sum_range_succ])
  have f3 : truncFactor 3 5 (5 / 2) ≤ (10685474 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b3.2 (by norm_num [Finset.sum_range_succ])
  have f5 : truncFactor 5 1 (5 / 2) ≤ (10178887 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b5.2 (by norm_num [Finset.sum_range_succ])
  have f17 : truncFactor 17 1 (5 / 2) ≤ (10008394 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b17.2 (by norm_num [Finset.sum_range_succ])
  have f19 : truncFactor 19 1 (5 / 2) ≤ (10006357 : ℝ) / 10000000 :=
    truncFactor_le_of (by norm_num) b19.2 (by norm_num [Finset.sum_range_succ])
  rw [divisorSum_order (5 / 2) janko3_mem]
  simp only [janko3, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  simp only [truncFactor] at f2 f3 f5 f17 f19 ⊢
  calc _
      ≤ (12147361 / 10000000) * ((10685474 / 10000000) * ((10178887 / 10000000) *
          ((10008394 / 10000000) * ((10006357 / 10000000) * 1)))) := by
        gcongr
    _ ≤ (1323173 : ℝ) / 1000000 := by norm_num

/-! ## The crossings, located -/

/-- The intermediate value theorem for two mass curves, at real endpoints. -/
theorem exists_crossing_real {m n : ℕ} {a b : ℝ} (hab : a ≤ b)
    (h1 : divisorSum m a < divisorSum n a) (h2 : divisorSum n b < divisorSum m b) :
    ∃ s ∈ Set.Ioo a b, divisorSum m s = divisorSum n s := by
  set f : ℝ → ℝ := fun s => divisorSum n s - divisorSum m s with hf
  have hcont : ContinuousOn f (Set.Icc a b) :=
    ((continuous_divisorSum n).sub (continuous_divisorSum m)).continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (f b) (f a) := ⟨by simp [hf]; linarith, by simp [hf]; linarith⟩
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hab hcont hmem
  refine ⟨s, hs, ?_⟩
  have : divisorSum n s - divisorSum m s = 0 := hs0
  linarith

/-- At `s = 1` the mass of `J1` is below that of `J3`. -/
theorem janko1_lt_janko3_at_one : divisorSum janko1.order 1 < divisorSum janko3.order 1 := by
  have h : ((massQ janko1 1 : ℚ) : ℝ) < ((massQ janko3 1 : ℚ) : ℝ) := by
    exact_mod_cast ranking_swaps_one_two.1
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, divisorSum_order_nat janko1_mem,
    divisorSum_order_nat janko3_mem]
  exact h

/-- At `s = 2` the mass of `M11` is below that of `J3`. -/
theorem mathieu11_lt_janko3_at_two :
    divisorSum mathieu11.order 2 < divisorSum janko3.order 2 := by
  have h : ((massQ mathieu11 2 : ℚ) : ℝ) < ((massQ janko3 2 : ℚ) : ℝ) := by
    exact_mod_cast minimum_swaps_two_three.1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, divisorSum_order_nat mathieu11_mem,
    divisorSum_order_nat janko3_mem]
  exact h

/-- **The `J1`/`J3` crossing lies in `(1, 3/2)`** — half of the interval `(1, 2)` given by
`SporadicClosure.janko_curves_cross`. -/
theorem janko_crossing_before_three_halves :
    ∃ s ∈ Set.Ioo (1 : ℝ) (3 / 2), divisorSum janko1.order s = divisorSum janko3.order s := by
  refine exists_crossing_real (by norm_num) janko1_lt_janko3_at_one ?_
  calc divisorSum janko3.order (3 / 2) ≤ (21417 : ℝ) / 10000 := janko3_three_halves_upper
    _ < (2168 : ℝ) / 1000 := by norm_num
    _ ≤ divisorSum janko1.order (3 / 2) := janko1_three_halves_lower

/-- **The `M11`/`J3` crossing lies in `(2, 5/2)`** — half of the interval `(2, 3)` given by
`SporadicClosure.bottom_curves_cross`. -/
theorem bottom_crossing_before_five_halves :
    ∃ s ∈ Set.Ioo (2 : ℝ) (5 / 2), divisorSum mathieu11.order s = divisorSum janko3.order s := by
  refine exists_crossing_real (by norm_num) mathieu11_lt_janko3_at_two ?_
  calc divisorSum janko3.order (5 / 2) ≤ (1323173 : ℝ) / 1000000 := janko3_five_halves_upper
    _ < (132393 : ℝ) / 100000 := by norm_num
    _ ≤ divisorSum mathieu11.order (5 / 2) := mathieu11_five_halves_lower

end SporadicCrossing

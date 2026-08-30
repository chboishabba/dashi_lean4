/-
# The table of fiber sums, and what it shows

This file collects the qualitative content of the twenty fiber sums computed in
`RequestProject/FiberSumsMulti.lean` and `RequestProject/FiberSumsSingle.lean`:

* how many points each fiber contributes (`card_fiber_multi`, `card_fiber_single`);
* the fiber of `2` carries the largest absolute mass (`absFiberSum_two_max`);
* the fiber of `3` almost completely cancels in the signed sum, although its absolute mass is
  large (`fiber_three_cancellation`);
* among the fourteen primes contributing a single point, `47` has the largest normalised
  magnitude (`absFiberSum_47_max_single`), and it still lies inside Deligne's bound
  (`absFiberSum_47_lt_two`);
* the total absolute mass of the `36` highlighted points (`total_absFiberSum`).
-/
import RequestProject.FiberSumsSingle

namespace FiberSums

open PrimeFibers RamanujanTau

/-! ## How many points each fiber contributes -/

/-- The six primes whose fiber contains more than one point, and their point counts. -/
theorem card_fiber_multi :
    (primePowerFiber 2 256).card = 8 ∧ (primePowerFiber 3 256).card = 5 ∧
      (primePowerFiber 5 256).card = 3 ∧ (primePowerFiber 7 256).card = 2 ∧
      (primePowerFiber 11 256).card = 2 ∧ (primePowerFiber 13 256).card = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · rw [card_primePowerFiber (by norm_num) (by norm_num)]
      decide

/-- Each of the remaining fourteen primes contributes a single point, namely `p` itself. -/
theorem card_fiber_single {p : ℕ} (hp : p ∈ first20Primes) (hsingle : 256 < p ^ 2) :
    (primePowerFiber p 256).card = 1 := by
  have hpp := prime_of_mem_first20Primes hp
  have hle : p ≤ 71 := le_of_mem_first20Primes hp
  rw [card_primePowerFiber hpp.one_lt (by norm_num)]
  have h1 : 1 ≤ Nat.log p 256 :=
    (Nat.le_log_iff_pow_le hpp.one_lt (by norm_num)).2 (by simpa using hle.trans (by norm_num))
  have h2 : Nat.log p 256 < 2 := by
    by_contra hc
    have : p ^ 2 ≤ 256 := (Nat.le_log_iff_pow_le hpp.one_lt (by norm_num)).1 (by omega)
    omega
  omega

/-! ## The fiber of `2` carries the largest absolute mass -/

/-- Among the twenty fibers, the fiber of `2` has the largest absolute sum. -/
theorem absFiberSum_two_max {p : ℕ} (hp : p ∈ first20Primes) (hne : p ≠ 2) :
    absFiberSum p 256 < absFiberSum 2 256 := by
  have hT := abs_le.1 absFiberSum_2
  fin_cases hp
  · exact absurd rfl hne
  · have h := abs_le.1 absFiberSum_3
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_5
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_7
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_11
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_13
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_17
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_19
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_23
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_29
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_31
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_37
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_41
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_43
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_47
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_53
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_59
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_61
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_67
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_71
    linarith [h.1, h.2, hT.1, hT.2]

/-! ## Cancellation in the fiber of `3` -/

/-- The signed fiber sum of `3` is tiny while its absolute fiber sum is large: the terms of the
fiber of `3` almost completely cancel. -/
theorem fiber_three_cancellation :
    |signedFiberSum 3 256| < 0.05 ∧ 3.29 < absFiberSum 3 256 := by
  have hs := abs_le.1 signedFiberSum_3
  have ha := abs_le.1 absFiberSum_3
  constructor
  · rw [abs_lt]
    constructor <;> [linarith [hs.1]; linarith [hs.2]]
  · linarith [ha.1]

/-! ## The largest single-point fiber -/

/-- Among the fourteen primes whose fiber consists of a single point, `47` has the largest
normalised magnitude `|τ(p)|/p^{11/2}`. -/
theorem absFiberSum_47_max_single {p : ℕ} (hp : p ∈ first20Primes) (hsingle : 256 < p ^ 2)
    (hne : p ≠ 47) : absFiberSum p 256 < absFiberSum 47 256 := by
  have hT := abs_le.1 absFiberSum_47
  fin_cases hp
  · exact absurd hsingle (by norm_num)
  · exact absurd hsingle (by norm_num)
  · exact absurd hsingle (by norm_num)
  · exact absurd hsingle (by norm_num)
  · exact absurd hsingle (by norm_num)
  · exact absurd hsingle (by norm_num)
  · have h := abs_le.1 absFiberSum_17
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_19
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_23
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_29
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_31
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_37
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_41
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_43
    linarith [h.1, h.2, hT.1, hT.2]
  · exact absurd rfl hne
  · have h := abs_le.1 absFiberSum_53
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_59
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_61
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_67
    linarith [h.1, h.2, hT.1, hT.2]
  · have h := abs_le.1 absFiberSum_71
    linarith [h.1, h.2, hT.1, hT.2]

/-- The largest single-point value still lies inside Deligne's bound `|τ(p)| ≤ 2 p^{11/2}`. -/
theorem absFiberSum_47_lt_two : absFiberSum 47 256 < 2 := by
  have h := abs_le.1 absFiberSum_47
  linarith [h.2]

/-! ## The total absolute mass of the highlighted points -/

theorem sum_first20Primes (f : ℕ → ℝ) : ∑ p ∈ first20Primes, f p =
    f 2 + f 3 + f 5 + f 7 + f 11 + f 13 + f 17 + f 19 + f 23 + f 29 + f 31 + f 37
      + f 41 + f 43 + f 47 + f 53 + f 59 + f 61 + f 67 + f 71 := by
  have h : first20Primes = ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
      67, 71} : Finset ℕ) := rfl
  rw [h, show ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71} :
      Finset ℕ) = (⟨[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71],
      by decide⟩ : Finset ℕ) from by decide]
  simp [Finset.sum_mk, List.sum_cons]
  ring

/-- The absolute mass of the `36` highlighted points, split over the twenty fibers. -/
theorem sum_abs_normTau_eq_sum_absFiberSum :
    ∑ n ∈ firstTwentyFibers 256, |normTau n| = ∑ p ∈ first20Primes, absFiberSum p 256 := by
  rw [PrimeFibers.sum_firstTwentyFibers]
  rfl

/-- The total absolute mass `∑ |τ(n)/n^{11/2}|` over the `36` prime powers of the first twenty
primes below `256` is `25.83915`, to four decimal places. -/
theorem total_absFiberSum :
    |∑ n ∈ firstTwentyFibers 256, |normTau n| - 25.83915| ≤ 1e-4 := by
  rw [sum_abs_normTau_eq_sum_absFiberSum, sum_first20Primes]
  have h2 := abs_le.1 absFiberSum_2
  have h3 := abs_le.1 absFiberSum_3
  have h5 := abs_le.1 absFiberSum_5
  have h7 := abs_le.1 absFiberSum_7
  have h11 := abs_le.1 absFiberSum_11
  have h13 := abs_le.1 absFiberSum_13
  have h17 := abs_le.1 absFiberSum_17
  have h19 := abs_le.1 absFiberSum_19
  have h23 := abs_le.1 absFiberSum_23
  have h29 := abs_le.1 absFiberSum_29
  have h31 := abs_le.1 absFiberSum_31
  have h37 := abs_le.1 absFiberSum_37
  have h41 := abs_le.1 absFiberSum_41
  have h43 := abs_le.1 absFiberSum_43
  have h47 := abs_le.1 absFiberSum_47
  have h53 := abs_le.1 absFiberSum_53
  have h59 := abs_le.1 absFiberSum_59
  have h61 := abs_le.1 absFiberSum_61
  have h67 := abs_le.1 absFiberSum_67
  have h71 := abs_le.1 absFiberSum_71
  rw [abs_le]
  constructor <;>
    linarith [h2.1, h2.2, h3.1, h3.2, h5.1, h5.2, h7.1, h7.2, h11.1, h11.2, h13.1, h13.2, h17.1, h17.2, h19.1, h19.2, h23.1, h23.2, h29.1, h29.2, h31.1, h31.2, h37.1, h37.2, h41.1, h41.2, h43.1, h43.2, h47.1, h47.2, h53.1, h53.2, h59.1, h59.2, h61.1, h61.2, h67.1, h67.2, h71.1, h71.2]

end FiberSums

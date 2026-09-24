import Mathlib

/-!
# 3, 6, 9 — the digital-root trinity

"If you only knew the magnificence of the 3, 6 and 9, then you would have a key to the
universe." — attributed to Nikola Tesla.

This file makes the folklore claims around `3, 6, 9` precise and proves them.  The organising
notion is the **digital root** of a natural number: iterate "sum the decimal digits" until a
single digit remains.  Equivalently `digitalRoot n = 1 + (n-1) % 9` for `n > 0`.

Main results:

* `digitalRoot_digitsSum` : the digital root is invariant under summing decimal digits.
* `digitalRoot_mem_trinity_iff` : `digitalRoot n ∈ {3, 6, 9}` exactly when `3 ∣ n`.
* `trinity_add`, `trinity_mul` : the trinity is closed under addition and absorbs
  multiplication by anything — it is (the digital-root shadow of) an ideal.
* `digitalRoot_two_pow_period_six`, `digitalRoot_two_pow_notMem_trinity` : the doubling
  circuit `1, 2, 4, 8, 7, 5` has period six and never meets `3, 6, 9`.
* `digitalRoot_three_pow` : powers `3 ^ n`, `n ≥ 2`, all have digital root `9`.
* `trinity_generates` : `3, 6, 9` generate exactly the multiples of `3`, additively, both in
  `ℕ` and in `ℤ`; so within the world they control, three, six and nine really are all you need.
-/

namespace Tesla369

/-- The digital root of `n`: the single digit reached by repeatedly summing decimal digits.
    Closed form: `0` for `n = 0`, and `1 + (n - 1) % 9` otherwise. -/
def digitalRoot (n : ℕ) : ℕ := if n = 0 then 0 else (n - 1) % 9 + 1

/-- The trinity `{3, 6, 9}`. -/
def trinity : Finset ℕ := {3, 6, 9}

@[simp] lemma digitalRoot_zero : digitalRoot 0 = 0 := rfl

lemma digitalRoot_of_pos {n : ℕ} (hn : 0 < n) : digitalRoot n = (n - 1) % 9 + 1 := by
  simp [digitalRoot, hn.ne']

lemma digitalRoot_pos {n : ℕ} (hn : 0 < n) : 0 < digitalRoot n := by
  simp [digitalRoot_of_pos hn]

lemma digitalRoot_le_nine (n : ℕ) : digitalRoot n ≤ 9 := by
  unfold digitalRoot
  split
  · omega
  · have := Nat.mod_lt (n - 1) (show 0 < 9 by norm_num)
    omega

@[simp] lemma digitalRoot_eq_zero_iff {n : ℕ} : digitalRoot n = 0 ↔ n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact absurd h (digitalRoot_pos (Nat.pos_of_ne_zero hn)).ne'
  · rintro rfl; rfl

/-- The digital root is congruent to the number itself modulo `9`. -/
lemma digitalRoot_modEq (n : ℕ) : digitalRoot n ≡ n [MOD 9] := by
  unfold digitalRoot Nat.ModEq
  split
  · omega
  · omega

/-- Two numbers with the same residue mod `9` that are simultaneously zero or nonzero have the
same digital root. -/
lemma digitalRoot_congr {a b : ℕ} (h : a ≡ b [MOD 9]) (h0 : a = 0 ↔ b = 0) :
    digitalRoot a = digitalRoot b := by
  unfold digitalRoot
  unfold Nat.ModEq at h
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [h0.mp rfl]
  · have hb : b ≠ 0 := fun hb => by omega
    simp only [ha.ne', hb, if_false]
    omega

lemma digitalRoot_idem (n : ℕ) : digitalRoot (digitalRoot n) = digitalRoot n := by
  refine digitalRoot_congr (digitalRoot_modEq n) ?_
  simp

/-- **Casting out nines.** Summing the decimal digits does not change the digital root. -/
theorem digitalRoot_digitsSum (n : ℕ) :
    digitalRoot ((Nat.digits 10 n).sum) = digitalRoot n := by
  refine digitalRoot_congr (Nat.modEq_nine_digits_sum n).symm ?_
  constructor
  · intro h
    by_contra hn
    have hne : Nat.digits 10 n ≠ [] := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr hn
    have hlast := Nat.getLast_digit_ne_zero 10 hn
    have hmem : (Nat.digits 10 n).getLast hne ∈ Nat.digits 10 n := List.getLast_mem hne
    have hsum : 0 < (Nat.digits 10 n).sum :=
      Nat.lt_of_lt_of_le (Nat.pos_of_ne_zero hlast)
        (List.single_le_sum (by intro x _; exact Nat.zero_le x) _ hmem)
    omega
  · rintro rfl; simp

/-- On single digits the digital root does nothing. -/
lemma digitalRoot_of_le_nine {n : ℕ} (hn : n ≤ 9) : digitalRoot n = n := by
  unfold digitalRoot
  split <;> omega

/-- For `n ≥ 10` the decimal digit sum is strictly smaller than `n`: the iteration terminates. -/
lemma digitsSum_lt_self {n : ℕ} (hn : 10 ≤ n) : (Nat.digits 10 n).sum < n := by
  rw [Nat.digits_def' (by norm_num : 1 < 10) (by omega : 0 < n)]
  have h2 : (Nat.digits 10 (n / 10)).sum ≤ n / 10 := Nat.digit_sum_le 10 _
  have h3 : 1 ≤ n / 10 := (Nat.one_le_div_iff (by norm_num)).mpr hn
  simp only [List.sum_cons]
  omega

/-- Repeatedly sum the decimal digits until a single digit is left. -/
def repeatedDigitSum (n : ℕ) : ℕ :=
  if h : 10 ≤ n then
    have : (Nat.digits 10 n).sum < n := digitsSum_lt_self h
    repeatedDigitSum (Nat.digits 10 n).sum
  else n
termination_by n

/-- **The definition deserves its name**: iterating the digit sum computes the digital root. -/
theorem repeatedDigitSum_eq_digitalRoot (n : ℕ) : repeatedDigitSum n = digitalRoot n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [repeatedDigitSum]
    split
    · rename_i h
      rw [ih _ (digitsSum_lt_self h), digitalRoot_digitsSum]
    · rename_i h
      exact (digitalRoot_of_le_nine (by omega)).symm

/-- The digital root of a positive number lies in `{1, …, 9}`. -/
lemma digitalRoot_mem_range {n : ℕ} (hn : 0 < n) :
    digitalRoot n ∈ ({1, 2, 3, 4, 5, 6, 7, 8, 9} : Finset ℕ) := by
  have h1 := digitalRoot_pos hn
  have h2 := digitalRoot_le_nine n
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- **The trinity is exactly divisibility by three.** -/
theorem digitalRoot_mem_trinity_iff {n : ℕ} (hn : 0 < n) :
    digitalRoot n ∈ trinity ↔ 3 ∣ n := by
  have hmod : digitalRoot n % 9 = n % 9 := digitalRoot_modEq n
  have hr := digitalRoot_of_pos hn
  simp only [trinity, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    have : n % 3 = 0 := by omega
    omega
  · intro h
    obtain ⟨k, rfl⟩ := h
    omega

/-- The trinity is closed under addition. -/
theorem trinity_add {a b : ℕ} (ha : digitalRoot a ∈ trinity) (hb : digitalRoot b ∈ trinity) :
    digitalRoot (a + b) ∈ trinity := by
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp [trinity, digitalRoot] at ha
    · exact h
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · simp [trinity, digitalRoot] at hb
    · exact h
  rw [digitalRoot_mem_trinity_iff ha0] at ha
  rw [digitalRoot_mem_trinity_iff hb0] at hb
  rw [digitalRoot_mem_trinity_iff (by omega)]
  exact Nat.dvd_add ha hb

/-- The trinity absorbs multiplication: once a factor is in the trinity, so is the product. -/
theorem trinity_mul {a b : ℕ} (ha : digitalRoot a ∈ trinity) (hb : 0 < b) :
    digitalRoot (a * b) ∈ trinity := by
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · simp [trinity, digitalRoot] at ha
    · exact h
  rw [digitalRoot_mem_trinity_iff ha0] at ha
  rw [digitalRoot_mem_trinity_iff (Nat.mul_pos ha0 hb)]
  exact Dvd.dvd.mul_right ha b

/-- `2 ^ 6 = 64 ≡ 1 [MOD 9]`, so the doubling circuit has period six. -/
theorem digitalRoot_two_pow_period_six (n : ℕ) :
    digitalRoot (2 ^ n) = digitalRoot (2 ^ (n % 6)) := by
  have key : ∀ q r : ℕ, 2 ^ (6 * q + r) % 9 = 2 ^ r % 9 := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ k ih =>
        intro r
        have : 6 * (k + 1) + r = 6 * k + r + 6 := by ring
        rw [this, pow_add]
        have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
        rw [h64, Nat.mul_mod, ih r, ← Nat.mul_mod]
        rw [Nat.mul_mod, show 64 % 9 = 1 by norm_num, mul_one, Nat.mod_mod_of_dvd]
        exact dvd_rfl
  refine digitalRoot_congr ?_ ?_
  · have hn : 6 * (n / 6) + n % 6 = n := by omega
    unfold Nat.ModEq
    calc 2 ^ n % 9 = 2 ^ (6 * (n / 6) + n % 6) % 9 := by rw [hn]
      _ = 2 ^ (n % 6) % 9 := key _ _
  · have h1 : (0:ℕ) < 2 ^ n := pow_pos (by norm_num) n
    have h2 : (0:ℕ) < 2 ^ (n % 6) := pow_pos (by norm_num) _
    omega

/-- **The doubling circuit never touches the trinity.**  The digital roots of the powers of two
cycle through `1, 2, 4, 8, 7, 5`, and none of these is `3`, `6` or `9`. -/
theorem digitalRoot_two_pow_notMem_trinity (n : ℕ) : digitalRoot (2 ^ n) ∉ trinity := by
  rw [digitalRoot_mem_trinity_iff (pow_pos (by norm_num) n)]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow (p := 3) (by norm_num) h
  omega

/-- The explicit doubling cycle. -/
theorem digitalRoot_two_pow_values (n : ℕ) :
    digitalRoot (2 ^ n) ∈ ({1, 2, 4, 8, 7, 5} : Finset ℕ) := by
  rw [digitalRoot_two_pow_period_six n]
  have h : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases h' : (n % 6) <;> decide

/-- Powers of three from the square onwards all have digital root `9`. -/
theorem digitalRoot_three_pow {n : ℕ} (hn : 2 ≤ n) : digitalRoot (3 ^ n) = 9 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have h9 : (9 : ℕ) ∣ 3 ^ (2 + k) := ⟨3 ^ k, by rw [pow_add]; norm_num⟩
  obtain ⟨m, hm⟩ := h9
  have hpos : 0 < 3 ^ (2 + k) := pow_pos (by norm_num) _
  rw [digitalRoot_of_pos hpos, hm]
  have : 0 < m := by nlinarith [hpos, hm]
  omega

/-- Digital roots of the doubling map on the trinity itself: `3 ↦ 6 ↦ 3` and `9 ↦ 9`. -/
theorem trinity_doubling :
    digitalRoot (2 * 3) = 6 ∧ digitalRoot (2 * 6) = 3 ∧ digitalRoot (2 * 9) = 9 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **3, 6, 9 is all you need (ℕ version).** A positive natural number is a nonnegative
combination of `3`, `6` and `9` iff it is divisible by `3`. -/
theorem trinity_generates_nat (n : ℕ) :
    (∃ a b c : ℕ, n = 3 * a + 6 * b + 9 * c) ↔ 3 ∣ n := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    omega
  · rintro ⟨k, rfl⟩
    exact ⟨k, 0, 0, by ring⟩

/-- **3, 6, 9 is all you need (ℤ version).** The subgroup of `ℤ` generated by `3, 6, 9` is
exactly the multiples of `3`. -/
theorem trinity_generates :
    AddSubgroup.closure ({3, 6, 9} : Set ℤ) = AddSubgroup.zmultiples (3 : ℤ) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro x (rfl | rfl | rfl)
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
  · rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure (by norm_num)

/-- **The trinity is redundant: `3` alone is all you need.** -/
theorem three_generates :
    AddSubgroup.closure ({3} : Set ℤ) = AddSubgroup.closure ({3, 6, 9} : Set ℤ) := by
  rw [trinity_generates]
  simpa using (AddSubgroup.zmultiples_eq_closure (3 : ℤ)).symm

/-- **So is `{6, 9}`**: since `9 - 6 = 3`, dropping the `3` costs nothing either. -/
theorem six_nine_generates :
    AddSubgroup.closure ({6, 9} : Set ℤ) = AddSubgroup.zmultiples (3 : ℤ) := by
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
  · rw [AddSubgroup.zmultiples_le]
    have h9 : (9 : ℤ) ∈ AddSubgroup.closure ({6, 9} : Set ℤ) :=
      AddSubgroup.subset_closure (by norm_num)
    have h6 : (6 : ℤ) ∈ AddSubgroup.closure ({6, 9} : Set ℤ) :=
      AddSubgroup.subset_closure (by norm_num)
    have := AddSubgroup.sub_mem _ h9 h6
    norm_num at this
    exact this

/-- In `ZMod 9`, the shadow of the trinity is the set of multiples of `3`, i.e. `{0, 3, 6}`,
the unique subgroup of order three. -/
theorem trinity_zmod : {x : ZMod 9 | ∃ y : ZMod 9, x = 3 * y} = {0, 3, 6} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  revert x
  decide

/-- The digital roots `3, 6, 9` correspond, mod `9`, to the three residues `3, 6, 0`. -/
theorem trinity_residues :
    trinity.image (fun d : ℕ => (d : ZMod 9)) = ({3, 6, 0} : Finset (ZMod 9)) := by
  decide

/-- **Six is the minimal period of the doubling circuit.**  `digitalRoot_two_pow_period_six` only
says that `6` *is* a period; here we check that every period is a multiple of `6`, so the cycle
`1, 2, 4, 8, 7, 5` really has length six and not a proper divisor of it. -/
theorem digitalRoot_two_pow_period_six_minimal {d : ℕ}
    (h : ∀ n : ℕ, digitalRoot (2 ^ (n + d)) = digitalRoot (2 ^ n)) : 6 ∣ d := by
  have h0 : digitalRoot (2 ^ d) = 1 := by simpa using h 0
  rw [digitalRoot_two_pow_period_six d] at h0
  have hlt : d % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have key : ∀ r : ℕ, r < 6 → digitalRoot (2 ^ r) = 1 → r = 0 := by
    intro r hr
    interval_cases r <;> decide
  have := key (d % 6) hlt h0
  omega

end Tesla369

/-
# Six fibers, with multiplicity: the Monster's small part as a stack of modular waves

`RequestProject/TauWaves.lean` smoothed the two fibers of `modular-tau-2-and-3.svg` into the
waves `w_p(u) = sin((u+1)θ_p)/sin θ_p` and drew their interference. This file carries the same
construction over **all six small primes of the Monster**, `2, 3, 5, 7, 11, 13`, and — this is
the new ingredient — counts each prime **with the multiplicity it has in `|M|`**:

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

so the wave of `2` is taken `46` times, the wave of `3` twenty times, and so on, for a total of
`46 + 20 + 9 + 6 + 2 + 3 = 86` copies (`Sporadic.sum_small_exponents`). Three views of the same
data are defined and proved here:

* **the stack** `stackWave u = 46 w₂(u) + 20 w₃(u) + 9 w₅(u) + 6 w₇(u) + 2 w₁₁(u) + 3 w₁₃(u)`,
  the six fibers superposed with their Monster multiplicities;
* **the build-up, copy by copy** `copyStack n u`: the sum of the first `n` of the `86` copies,
  in the order `2,…,2,3,…,3,5,…,13`. It starts at `0`, ends at the stack, and at height `u = 0`
  it is the ramp `copyStack n 0 = n` — the build-up itself counts the exponents;
* **the build-up surface** `buildSurface u t`, the continuous interpolation of the previous view
  in the copy-count `t ∈ [0, 86]`, linear on each prime's block; this is the surface actually
  drawn in `visualization/monster-tau-waves-six.svg`;
* **the interference of the 2-part with the rest**, `sumSurface6`/`diffSurface6` over `(u, v)`,
  exactly as in the two-prime picture but with `46 w₂` against `20 w₃ + … + 3 w₁₃`.

The Deligne bound `|τ(p)| < 2p^{11/2}` is checked for each of the six primes
(`abs_satakeCos_lt_one_of_sq` and its six corollaries), so all six Satake angles are real and all
six waves are genuine oscillations; each of the six waves passes through the plotted points of
its fiber (`wave_eq_normTau_five`, `_seven`, `_eleven`, `_thirteen`, and the two from `TauWaves`).
-/
import RequestProject.TauWaves
import RequestProject.SmallPrimeFibers

namespace TauWavesSix

open TauWaves RamanujanTau Real

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The four new values of `τ` and the Deligne bound at the six small primes -/

theorem tau_seven : tau 7 = -16744 := by native_decide

theorem tau_eleven : tau 11 = 534612 := by native_decide

theorem tau_thirteen : tau 13 = -577738 := by native_decide

/-- **Deligne's bound as a criterion.** If `τ(p)² < 4p^{11}` then the Satake parameter
`cos θ_p = τ(p)/2p^{11/2}` lies strictly inside `[-1, 1]`, so `θ_p` is a genuine angle and the
fiber of `p` really is a sampled sine wave. -/
theorem abs_satakeCos_lt_one_of_sq {p : ℕ} (hp : 0 < p)
    (h : ((tau p : ℤ) : ℝ) ^ 2 < 4 * (p : ℝ) ^ 11) : |satakeCos p| < 1 := by
  have hrt : 0 < rt p := rt_pos hp
  have hsq : rt p ^ 2 = (p : ℝ) ^ 11 := rt_sq p
  have hb : (0 : ℝ) < 2 * rt p := by linarith
  have h2 : |((tau p : ℤ) : ℝ)| ^ 2 < (2 * rt p) ^ 2 := by
    rw [sq_abs]
    nlinarith [hsq]
  have h3 : |((tau p : ℤ) : ℝ)| < 2 * rt p := by
    nlinarith [abs_nonneg ((tau p : ℤ) : ℝ)]
  rw [satakeCos, abs_div, abs_of_pos hb, div_lt_one hb]
  exact h3

theorem abs_satakeCos_five_lt_one : |satakeCos 5| < 1 := by
  refine abs_satakeCos_lt_one_of_sq (by norm_num) ?_
  rw [RamanujanTau.tau_five]
  norm_num

theorem abs_satakeCos_seven_lt_one : |satakeCos 7| < 1 := by
  refine abs_satakeCos_lt_one_of_sq (by norm_num) ?_
  rw [tau_seven]
  norm_num

theorem abs_satakeCos_eleven_lt_one : |satakeCos 11| < 1 := by
  refine abs_satakeCos_lt_one_of_sq (by norm_num) ?_
  rw [tau_eleven]
  norm_num

theorem abs_satakeCos_thirteen_lt_one : |satakeCos 13| < 1 := by
  refine abs_satakeCos_lt_one_of_sq (by norm_num) ?_
  rw [tau_thirteen]
  norm_num

/-- The Deligne bound at all six small primes at once. -/
theorem abs_satakeCos_lt_one_of_mem {p : ℕ} (hp : p ∈ Sporadic.smallPrimes) :
    |satakeCos p| < 1 := by
  fin_cases hp
  · exact abs_satakeCos_two_lt_one
  · exact abs_satakeCos_three_lt_one
  · exact abs_satakeCos_five_lt_one
  · exact abs_satakeCos_seven_lt_one
  · exact abs_satakeCos_eleven_lt_one
  · exact abs_satakeCos_thirteen_lt_one

/-! ## Each of the six waves passes through the plotted points of its fiber -/

/-- The wave of `5` passes through the four plotted points `5^k ≤ 125`. -/
theorem wave_eq_normTau_five : ∀ k : ℕ, k ≤ 3 → wave 5 (k : ℝ) = normTau 5 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_five_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 5) (by decide) ?_
  have : (5 : ℕ) ^ (k + 2) ≤ 5 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-- The wave of `7` passes through the three plotted points `7^k ≤ 49`. -/
theorem wave_eq_normTau_seven : ∀ k : ℕ, k ≤ 2 → wave 7 (k : ℝ) = normTau 7 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_seven_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 7) (by decide) ?_
  have : (7 : ℕ) ^ (k + 2) ≤ 7 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-- The wave of `11` passes through the three plotted points `11^k ≤ 121`. -/
theorem wave_eq_normTau_eleven : ∀ k : ℕ, k ≤ 2 → wave 11 (k : ℝ) = normTau 11 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_eleven_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 11) (by decide) ?_
  have : (11 : ℕ) ^ (k + 2) ≤ 11 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-- The wave of `13` passes through the three plotted points `13^k ≤ 169`. -/
theorem wave_eq_normTau_thirteen : ∀ k : ℕ, k ≤ 2 → wave 13 (k : ℝ) = normTau 13 k := by
  refine wave_eq_normTau (by norm_num) abs_satakeCos_thirteen_lt_one ?_
  intro k hk
  refine RamanujanTau.tau_hecke_on_fiber (p := 13) (by decide) ?_
  have : (13 : ℕ) ^ (k + 2) ≤ 13 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
  simpa [RamanujanTau.displayN] using this.trans (by norm_num)

/-! ## The multiplicities -/

/-- The multiplicity with which the fiber of `p` enters the stack: the exponent of `p` in the
order of the Monster, for the six small primes, and `0` elsewhere. -/
def mult (p : ℕ) : ℕ := ((Sporadic.smallFactors.filter fun pe => pe.1 = p).map Prod.snd).sum

theorem mult_two : mult 2 = 46 := by decide
theorem mult_three : mult 3 = 20 := by decide
theorem mult_five : mult 5 = 9 := by decide
theorem mult_seven : mult 7 = 6 := by decide
theorem mult_eleven : mult 11 = 2 := by decide
theorem mult_thirteen : mult 13 = 3 := by decide

/-- The multiplicities really are the Monster's exponents. -/
theorem mult_eq_monster_factorization {p : ℕ} (hp : p ∈ Sporadic.smallPrimes) :
    mult p = Sporadic.monsterOrder.factorization p := by
  rw [mult, ← Sporadic.factorization_smallPart]
  exact Sporadic.factorization_smallPart_eq_monster hp

/-- The total number of copies in the stack: `46 + 20 + 9 + 6 + 2 + 3 = 86`, the number of
prime-power points on the six small fibers of the Monster. -/
theorem sum_mult : ∑ p ∈ Sporadic.smallPrimes, mult p = 86 := by decide

/-- The same total, read off the Monster's factorization. -/
theorem sum_mult_eq_sum_monster_exponents :
    ∑ p ∈ Sporadic.smallPrimes, mult p
      = ∑ p ∈ Sporadic.smallPrimes, Sporadic.monsterOrder.factorization p :=
  Finset.sum_congr rfl fun _ hp => mult_eq_monster_factorization hp

/-! ## View 1: the stack of the six fibers, each with its Monster multiplicity -/

/-- **The stack.** The six smoothed fibers superposed, the fiber of `p` counted `v_p(|M|)`
times: `z = 46 w₂(u) + 20 w₃(u) + 9 w₅(u) + 6 w₇(u) + 2 w₁₁(u) + 3 w₁₃(u)`. -/
noncomputable def stackWave (u : ℝ) : ℝ :=
  46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u + 6 * wave 7 u + 2 * wave 11 u + 3 * wave 13 u

/-- At height `0` every fiber contributes its multiplicity: the stack starts at the total
exponent count `86`. -/
theorem stackWave_zero : stackWave 0 = 86 := by
  rw [stackWave, wave_zero abs_satakeCos_two_lt_one, wave_zero abs_satakeCos_three_lt_one,
    wave_zero abs_satakeCos_five_lt_one, wave_zero abs_satakeCos_seven_lt_one,
    wave_zero abs_satakeCos_eleven_lt_one, wave_zero abs_satakeCos_thirteen_lt_one]
  norm_num

/-- The stack's starting height is the number of prime-power points on the six small fibers. -/
theorem stackWave_zero_eq_sum_mult :
    stackWave 0 = ((∑ p ∈ Sporadic.smallPrimes, mult p : ℕ) : ℝ) := by
  rw [stackWave_zero, sum_mult]
  norm_num

/-- At integer heights `k ≤ 2` the stack is the multiplicity-weighted combination of six
*plotted* normalised coefficients `τ(p^k)/p^{11k/2}`. -/
theorem stackWave_natCast {k : ℕ} (hk : k ≤ 2) :
    stackWave (k : ℝ) = 46 * normTau 2 k + 20 * normTau 3 k + 9 * normTau 5 k
      + 6 * normTau 7 k + 2 * normTau 11 k + 3 * normTau 13 k := by
  rw [stackWave, wave_eq_normTau_two k (by omega), wave_eq_normTau_three k (by omega),
    wave_eq_normTau_five k (by omega), wave_eq_normTau_seven k (by omega),
    wave_eq_normTau_eleven k (by omega), wave_eq_normTau_thirteen k (by omega)]

/-- The amplitude of the stack: each fiber contributes at most its multiplicity times the
amplitude `1/sin θ_p` of its own wave. -/
theorem abs_stackWave_le (u : ℝ) :
    |stackWave u| ≤ 46 / Real.sin (theta 2) + 20 / Real.sin (theta 3) + 9 / Real.sin (theta 5)
      + 6 / Real.sin (theta 7) + 2 / Real.sin (theta 11) + 3 / Real.sin (theta 13) := by
  have b2 := abs_wave_le abs_satakeCos_two_lt_one u
  have b3 := abs_wave_le abs_satakeCos_three_lt_one u
  have b5 := abs_wave_le abs_satakeCos_five_lt_one u
  have b7 := abs_wave_le abs_satakeCos_seven_lt_one u
  have b11 := abs_wave_le abs_satakeCos_eleven_lt_one u
  have b13 := abs_wave_le abs_satakeCos_thirteen_lt_one u
  have e : ∀ (m : ℝ) (x : ℝ), 0 ≤ m → |m * x| = m * |x| := by
    intro m x hm; rw [abs_mul, abs_of_nonneg hm]
  calc |stackWave u|
      ≤ |46 * wave 2 u| + |20 * wave 3 u| + |9 * wave 5 u| + |6 * wave 7 u| + |2 * wave 11 u|
          + |3 * wave 13 u| := by
        rw [stackWave]
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact abs_add_le _ _
    _ ≤ _ := by
        rw [e 46 _ (by norm_num), e 20 _ (by norm_num), e 9 _ (by norm_num),
          e 6 _ (by norm_num), e 2 _ (by norm_num), e 3 _ (by norm_num)]
        have h2 : (46 : ℝ) * |wave 2 u| ≤ 46 / Real.sin (theta 2) := by
          rw [div_eq_mul_one_div]; nlinarith
        have h3 : (20 : ℝ) * |wave 3 u| ≤ 20 / Real.sin (theta 3) := by
          rw [div_eq_mul_one_div]; nlinarith
        have h5 : (9 : ℝ) * |wave 5 u| ≤ 9 / Real.sin (theta 5) := by
          rw [div_eq_mul_one_div]; nlinarith
        have h7 : (6 : ℝ) * |wave 7 u| ≤ 6 / Real.sin (theta 7) := by
          rw [div_eq_mul_one_div]; nlinarith
        have h11 : (2 : ℝ) * |wave 11 u| ≤ 2 / Real.sin (theta 11) := by
          rw [div_eq_mul_one_div]; nlinarith
        have h13 : (3 : ℝ) * |wave 13 u| ≤ 3 / Real.sin (theta 13) := by
          rw [div_eq_mul_one_div]; nlinarith
        linarith

/-! ## View 2: building the stack up, one prime at a time -/

/-- The six blocks, in order: the prime and how many copies of its wave the stack contains. -/
def blocks : List (ℕ × ℕ) := Sporadic.smallFactors

theorem blocks_eq : blocks = [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3)] := rfl

/-- The stack after the first `j` primes have been added. -/
noncomputable def primeStack (j : ℕ) (u : ℝ) : ℝ :=
  (((blocks.take j).map fun pm => (pm.2 : ℝ) * wave pm.1 u)).sum

theorem primeStack_zero (u : ℝ) : primeStack 0 u = 0 := rfl

theorem primeStack_one (u : ℝ) : primeStack 1 u = 46 * wave 2 u := by
  simp [primeStack, blocks_eq]

theorem primeStack_two (u : ℝ) : primeStack 2 u = 46 * wave 2 u + 20 * wave 3 u := by
  simp [primeStack, blocks_eq]

theorem primeStack_three (u : ℝ) :
    primeStack 3 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u := by
  simp [primeStack, blocks_eq]; ring

theorem primeStack_four (u : ℝ) :
    primeStack 4 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u + 6 * wave 7 u := by
  simp [primeStack, blocks_eq]; ring

theorem primeStack_five (u : ℝ) :
    primeStack 5 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u + 6 * wave 7 u
      + 2 * wave 11 u := by
  simp [primeStack, blocks_eq]; ring

/-- **The build-up closes.** After all six primes the partial stack is the stack. -/
theorem primeStack_six (u : ℝ) : primeStack 6 u = stackWave u := by
  simp [primeStack, blocks_eq, stackWave]; ring

/-! ## View 3: building the stack up, one *copy* at a time -/

/-- The `86` copies in order: `2` forty-six times, `3` twenty times, `5` nine times, `7` six
times, `11` twice, `13` three times. -/
def copyList : List ℕ := blocks.flatMap fun pm => List.replicate pm.2 pm.1

theorem length_copyList : copyList.length = 86 := by decide

/-- The stack after `n` of the `86` copies have been laid down. -/
noncomputable def copyStack (n : ℕ) (u : ℝ) : ℝ :=
  ((copyList.take n).map fun p => wave p u).sum

theorem copyStack_zero (u : ℝ) : copyStack 0 u = 0 := rfl

/-- One more copy adds one more wave. -/
theorem copyStack_succ {n : ℕ} (hn : n < copyList.length) (u : ℝ) :
    copyStack (n + 1) u = copyStack n u + wave copyList[n] u := by
  have h : copyList.take (n + 1) = copyList.take n ++ [copyList[n]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hn]
    rfl
  rw [copyStack, copyStack, h, List.map_append, List.sum_append]
  simp

/-- The sum of `m` copies of the wave of `p`. -/
private theorem sum_map_replicate (m p : ℕ) (u : ℝ) :
    ((List.replicate m p).map fun q => wave q u).sum = (m : ℝ) * wave p u := by
  rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]

/-- The first block: the `46` copies of the fiber of `2`. -/
theorem copyStack_46 (u : ℝ) : copyStack 46 u = 46 * wave 2 u := by
  have h : copyList.take 46 = List.replicate 46 2 := by decide
  rw [copyStack, h, sum_map_replicate]
  norm_num

/-- After the second block: `2` and `3`, with multiplicity. -/
theorem copyStack_66 (u : ℝ) : copyStack 66 u = 46 * wave 2 u + 20 * wave 3 u := by
  have h : copyList.take 66 = List.replicate 46 2 ++ List.replicate 20 3 := by decide
  rw [copyStack, h]
  simp only [List.map_append, List.sum_append, sum_map_replicate]
  norm_num

/-- After the third block. -/
theorem copyStack_75 (u : ℝ) :
    copyStack 75 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u := by
  have h : copyList.take 75
      = List.replicate 46 2 ++ List.replicate 20 3 ++ List.replicate 9 5 := by decide
  rw [copyStack, h]
  simp only [List.map_append, List.sum_append, sum_map_replicate]
  norm_num

/-- After the fourth block. -/
theorem copyStack_81 (u : ℝ) :
    copyStack 81 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u + 6 * wave 7 u := by
  have h : copyList.take 81
      = List.replicate 46 2 ++ List.replicate 20 3 ++ List.replicate 9 5
        ++ List.replicate 6 7 := by decide
  rw [copyStack, h]
  simp only [List.map_append, List.sum_append, sum_map_replicate]
  norm_num

/-- After the fifth block. -/
theorem copyStack_83 (u : ℝ) :
    copyStack 83 u = 46 * wave 2 u + 20 * wave 3 u + 9 * wave 5 u + 6 * wave 7 u
      + 2 * wave 11 u := by
  have h : copyList.take 83
      = List.replicate 46 2 ++ List.replicate 20 3 ++ List.replicate 9 5
        ++ List.replicate 6 7 ++ List.replicate 2 11 := by decide
  rw [copyStack, h]
  simp only [List.map_append, List.sum_append, sum_map_replicate]
  norm_num

/-- **The last copy completes the stack**: `copyStack 86 = stackWave`. -/
theorem copyStack_86 (u : ℝ) : copyStack 86 u = stackWave u := by
  have h : copyList.take 86
      = List.replicate 46 2 ++ List.replicate 20 3 ++ List.replicate 9 5
        ++ List.replicate 6 7 ++ List.replicate 2 11 ++ List.replicate 3 13 := by decide
  rw [copyStack, h, stackWave]
  simp only [List.map_append, List.sum_append, sum_map_replicate]
  norm_num

/-- **The build-up is a ramp at height `0`**: after `n` copies the stack stands at `n`, because
every wave starts at `1`. The `86` steps of the build-up are exactly the `86` prime-power points
of the six small fibers of the Monster. -/
theorem copyStack_at_zero (n : ℕ) : copyStack n 0 = min n 86 := by
  have key : ∀ (l : List ℕ), (∀ p ∈ l, |satakeCos p| < 1) →
      ((l.map fun p => wave p (0 : ℝ)).sum) = l.length := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons a t ih =>
        intro h
        have ha : wave a (0 : ℝ) = 1 := wave_zero (h a (List.mem_cons_self ..))
        have ht : ∀ p ∈ t, |satakeCos p| < 1 := fun p hp => h p (List.mem_cons_of_mem _ hp)
        simp [ha, ih ht]
        ring
  have hmem : ∀ p ∈ copyList.take n, |satakeCos p| < 1 := by
    intro p hp
    have hp' : p ∈ copyList := List.mem_of_mem_take hp
    have hsub : ∀ q ∈ copyList, q ∈ Sporadic.smallPrimes := by decide
    exact abs_satakeCos_lt_one_of_mem (hsub p hp')
  rw [copyStack, key _ hmem, List.length_take, length_copyList]

/-! ## The continuous build-up surface -/

/-- The number of copies of a block of length `len`, starting at copy `offset`, that have been
laid down by "time" `t`. -/
noncomputable def blockRamp (t offset len : ℝ) : ℝ := max 0 (min len (t - offset))

theorem blockRamp_of_le {t offset len : ℝ} (h : t ≤ offset) : blockRamp t offset len = 0 := by
  rw [blockRamp, max_eq_left]
  exact min_le_of_right_le (by linarith)

theorem blockRamp_of_ge {t offset len : ℝ} (hlen : 0 ≤ len) (h : offset + len ≤ t) :
    blockRamp t offset len = len := by
  rw [blockRamp, min_eq_left (by linarith), max_eq_right hlen]

theorem blockRamp_mid {t offset len : ℝ} (h1 : offset ≤ t) (h2 : t ≤ offset + len) :
    blockRamp t offset len = t - offset := by
  rw [blockRamp, min_eq_right (by linarith), max_eq_right (by linarith)]

/-- **The build-up surface.** Over the domain `(u, t)` with `u` the height along the fibers and
`t ∈ [0, 86]` the number of copies laid down, `z = buildSurface u t` interpolates the copy-by-copy
build-up of the stack: linear in `t` on each prime's block, and equal to `copyStack n u` at the
end of every block. -/
noncomputable def buildSurface (u t : ℝ) : ℝ :=
  blockRamp t 0 46 * wave 2 u + blockRamp t 46 20 * wave 3 u + blockRamp t 66 9 * wave 5 u
    + blockRamp t 75 6 * wave 7 u + blockRamp t 81 2 * wave 11 u + blockRamp t 83 3 * wave 13 u

theorem buildSurface_zero (u : ℝ) : buildSurface u 0 = 0 := by
  rw [buildSurface, blockRamp_of_le (by norm_num), blockRamp_of_le (by norm_num),
    blockRamp_of_le (by norm_num), blockRamp_of_le (by norm_num), blockRamp_of_le (by norm_num)]
  rw [blockRamp]
  norm_num

/-- Inside the first block the surface is the fiber of `2` growing linearly in the copy-count. -/
theorem buildSurface_first_block {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 46) (u : ℝ) :
    buildSurface u t = t * wave 2 u := by
  rw [buildSurface, blockRamp_mid (by linarith) (by linarith),
    blockRamp_of_le (by linarith), blockRamp_of_le (by linarith),
    blockRamp_of_le (by linarith), blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
  ring

theorem buildSurface_46 (u : ℝ) : buildSurface u 46 = copyStack 46 u := by
  rw [buildSurface_first_block (by norm_num) (by norm_num), copyStack_46]

/-- Inside the second block: the completed `2`-part plus a growing fiber of `3`. -/
theorem buildSurface_second_block {t : ℝ} (h0 : 46 ≤ t) (h1 : t ≤ 66) (u : ℝ) :
    buildSurface u t = 46 * wave 2 u + (t - 46) * wave 3 u := by
  rw [buildSurface, blockRamp_of_ge (by norm_num) (by linarith),
    blockRamp_mid (by linarith) (by linarith),
    blockRamp_of_le (by linarith), blockRamp_of_le (by linarith),
    blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
  ring

theorem buildSurface_66 (u : ℝ) : buildSurface u 66 = copyStack 66 u := by
  rw [buildSurface_second_block (by norm_num) (by norm_num), copyStack_66]
  norm_num

/-- **The surface ends on the stack**: at `t = 86` every copy has been laid down. -/
theorem buildSurface_86 (u : ℝ) : buildSurface u 86 = stackWave u := by
  rw [buildSurface, blockRamp_of_ge (by norm_num) (by norm_num),
    blockRamp_of_ge (by norm_num) (by norm_num), blockRamp_of_ge (by norm_num) (by norm_num),
    blockRamp_of_ge (by norm_num) (by norm_num), blockRamp_of_ge (by norm_num) (by norm_num),
    blockRamp_of_ge (by norm_num) (by norm_num), stackWave]

/-- The six ramps add up to the copy-count: at any time `t ∈ [0, 86]` exactly `t` copies have
been laid down in total. -/
theorem blockRamp_total {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 86) :
    blockRamp t 0 46 + blockRamp t 46 20 + blockRamp t 66 9 + blockRamp t 75 6
      + blockRamp t 81 2 + blockRamp t 83 3 = t := by
  rcases le_or_gt t 46 with h | h
  · rw [blockRamp_mid (by linarith) (by linarith), blockRamp_of_le (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
    ring
  rcases le_or_gt t 66 with h' | h'
  · rw [blockRamp_of_ge (by norm_num) (by linarith), blockRamp_mid (by linarith) (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
    ring
  rcases le_or_gt t 75 with h'' | h''
  · rw [blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_mid (by linarith) (by linarith), blockRamp_of_le (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
    ring
  rcases le_or_gt t 81 with h3 | h3
  · rw [blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_of_ge (by norm_num) (by linarith), blockRamp_mid (by linarith) (by linarith),
      blockRamp_of_le (by linarith), blockRamp_of_le (by linarith)]
    ring
  rcases le_or_gt t 83 with h4 | h4
  · rw [blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_mid (by linarith) (by linarith), blockRamp_of_le (by linarith)]
    ring
  · rw [blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_of_ge (by norm_num) (by linarith), blockRamp_of_ge (by norm_num) (by linarith),
      blockRamp_of_ge (by norm_num) (by linarith), blockRamp_mid (by linarith) (by linarith)]
    ring

/-- Along the back edge `u = 0` the build-up surface is the straight ramp `z = t`: the picture's
staircase of `86` unit steps, one per prime-power point of the six small fibers. -/
theorem buildSurface_at_zero {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 86) : buildSurface 0 t = t := by
  rw [buildSurface, wave_zero abs_satakeCos_two_lt_one, wave_zero abs_satakeCos_three_lt_one,
    wave_zero abs_satakeCos_five_lt_one, wave_zero abs_satakeCos_seven_lt_one,
    wave_zero abs_satakeCos_eleven_lt_one, wave_zero abs_satakeCos_thirteen_lt_one]
  simpa using blockRamp_total h0 h1

/-! ## View 4: the `2`-part against the other five primes -/

/-- The `2`-part of the Monster as a wave: `46` copies of the fiber of `2`. -/
noncomputable def twoPartWave (u : ℝ) : ℝ := 46 * wave 2 u

/-- The remaining five small primes, with their multiplicities. -/
noncomputable def restWave (v : ℝ) : ℝ :=
  20 * wave 3 v + 9 * wave 5 v + 6 * wave 7 v + 2 * wave 11 v + 3 * wave 13 v

theorem twoPartWave_add_restWave (u : ℝ) : twoPartWave u + restWave u = stackWave u := by
  rw [twoPartWave, restWave, stackWave]; ring

/-- Constructive interference of the `2`-part with the rest, over the square of heights. -/
noncomputable def sumSurface6 (u v : ℝ) : ℝ := twoPartWave u + restWave v

/-- Destructive interference of the `2`-part with the rest. -/
noncomputable def diffSurface6 (u v : ℝ) : ℝ := twoPartWave u - restWave v

theorem sum6_add_diff6 (u v : ℝ) :
    sumSurface6 u v + diffSurface6 u v = 2 * twoPartWave u := by
  rw [sumSurface6, diffSurface6]; ring

theorem sum6_sub_diff6 (u v : ℝ) :
    sumSurface6 u v - diffSurface6 u v = 2 * restWave v := by
  rw [sumSurface6, diffSurface6]; ring

/-- On the diagonal the constructive view is the whole stack. -/
theorem sumSurface6_diag (u : ℝ) : sumSurface6 u u = stackWave u :=
  twoPartWave_add_restWave u

/-- The nodal set of the destructive view: where the `2`-part exactly cancels the other five
primes. -/
theorem diffSurface6_eq_zero_iff (u v : ℝ) :
    diffSurface6 u v = 0 ↔ twoPartWave u = restWave v := by
  rw [diffSurface6, sub_eq_zero]

/-! ## The stack as a solution of a wave equation -/

/-- The derivative of the stack. -/
noncomputable def stackDeriv (u : ℝ) : ℝ :=
  46 * waveDeriv 2 u + 20 * waveDeriv 3 u + 9 * waveDeriv 5 u + 6 * waveDeriv 7 u
    + 2 * waveDeriv 11 u + 3 * waveDeriv 13 u

theorem hasDerivAt_stackWave (u : ℝ) : HasDerivAt stackWave (stackDeriv u) u := by
  have h2 := ((hasDerivAt_wave 2 u).const_mul (46 : ℝ))
  have h3 := ((hasDerivAt_wave 3 u).const_mul (20 : ℝ))
  have h5 := ((hasDerivAt_wave 5 u).const_mul (9 : ℝ))
  have h7 := ((hasDerivAt_wave 7 u).const_mul (6 : ℝ))
  have h11 := ((hasDerivAt_wave 11 u).const_mul (2 : ℝ))
  have h13 := ((hasDerivAt_wave 13 u).const_mul (3 : ℝ))
  have := (((((h2.add h3).add h5).add h7).add h11).add h13)
  simpa [stackWave, stackDeriv, waveDeriv, mul_div_assoc] using this

theorem hasDerivAt_stackDeriv (u : ℝ) :
    HasDerivAt stackDeriv
      (-(46 * theta 2 ^ 2 * wave 2 u + 20 * theta 3 ^ 2 * wave 3 u + 9 * theta 5 ^ 2 * wave 5 u
        + 6 * theta 7 ^ 2 * wave 7 u + 2 * theta 11 ^ 2 * wave 11 u
        + 3 * theta 13 ^ 2 * wave 13 u)) u := by
  have h2 := ((hasDerivAt_waveDeriv 2 u).const_mul (46 : ℝ))
  have h3 := ((hasDerivAt_waveDeriv 3 u).const_mul (20 : ℝ))
  have h5 := ((hasDerivAt_waveDeriv 5 u).const_mul (9 : ℝ))
  have h7 := ((hasDerivAt_waveDeriv 7 u).const_mul (6 : ℝ))
  have h11 := ((hasDerivAt_waveDeriv 11 u).const_mul (2 : ℝ))
  have h13 := ((hasDerivAt_waveDeriv 13 u).const_mul (3 : ℝ))
  have := (((((h2.add h3).add h5).add h7).add h11).add h13)
  refine this.congr_deriv ?_
  ring

/-- **The stack is a superposition of six standing waves.** Its second derivative is the same
multiplicity-weighted combination with each term scaled by `-θ_p²`; in particular the stack is not
a single wave, and the six Satake frequencies are all visible in it. -/
theorem deriv_deriv_stackWave (u : ℝ) :
    deriv (deriv stackWave) u
      = -(46 * theta 2 ^ 2 * wave 2 u + 20 * theta 3 ^ 2 * wave 3 u + 9 * theta 5 ^ 2 * wave 5 u
        + 6 * theta 7 ^ 2 * wave 7 u + 2 * theta 11 ^ 2 * wave 11 u
        + 3 * theta 13 ^ 2 * wave 13 u) := by
  have h : deriv stackWave = stackDeriv := funext fun x => (hasDerivAt_stackWave x).deriv
  rw [h]
  exact (hasDerivAt_stackDeriv u).deriv

end TauWavesSix

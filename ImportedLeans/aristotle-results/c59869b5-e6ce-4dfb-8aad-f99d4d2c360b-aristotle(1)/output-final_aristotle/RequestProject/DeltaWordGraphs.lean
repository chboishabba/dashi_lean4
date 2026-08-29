import Mathlib
import RequestProject.DeltaGraph

/-!
# The five Hecke words, each with its own graph of `Δ`

`RequestProject/HeckeWords.lean` follows five words in the Hecke algebra,

`T₂`,  `T₃`,  `T₂T₃`,  `T₂T₃T₂`,  `T₃T₃T₃`,

and `DeltaGraph.tau_word_values` evaluates their five multipliers on the discriminant form
`Δ = q ∏ (1 - qᵐ)²⁴`:

`-24`, `252`, `-6048`, `145152`, `16003008`.

This file draws each of those five words as a modular form in its own right. A Hecke operator
acts on `q`-expansions by

`(Tₙ f)(z) = ∑_{m ≥ 1} (∑_{d ∣ gcd(n, m)} d^{k-1} a(nm/d²)) qᵐ`,   `k = 12` here,

which is `heckeCoeff`; each word is the corresponding combination of these (`wordT2`, …,
`wordT3T3T3`, the words with an inner echo carrying their extra `2¹¹ T₃` and `2·3¹¹ T₃` terms,
exactly as `HeckeWords.hmul_two_three_two` and `HeckeWords.hmul_three_three_three` prescribe).

The five theorems `wordT2_eq`, `wordT3_eq`, `wordT2T3_eq`, `wordT2T3T2_eq`, `wordT3T3T3_eq` say
that on the verified range each word's `q`-expansion is the `q`-expansion of `Δ` multiplied by
its own constant, so the five graphs are the one graph of `Δ` rescaled — that is what being an
eigenform *looks* like. `heckeApprox_eq_smul` turns this into the statement about the plotted
function on the upper half plane, and `heckeApprox_norm`, `log_norm_heckeApprox`,
`heckeApprox_neg_phase`, `word_abs_multipliers_strictMono` are the four features one sees in the
plates: the vertical offset of each profile, its size, the phase reversal of the words with a
negative multiplier, and the order of the five scales. `word_coeffs_three_dvd` and
`word_coeffs_mem_trinity` are the colouring: `τ(2) = -24` and `τ(3) = 252` are divisible by
three, so all five multipliers are, and every plotted coefficient of every word has digital root
in the trinity `{3, 6, 9}`.

## The coefficient table

`tauTable` is the list of `τ(1), …, τ(60)`, and `tauTable_eq_deltaCoeffs` certifies it against
the same eta-product expansion `DeltaGraph.deltaCoeffs` that produced `DeltaGraph.tau_table`
(one kernel evaluation, reused by every statement below). `tauT_eq_tau` records that the first
thirty entries are `DeltaGraph.tau`.

Because `Tₙ` at coefficient `m` needs `τ(nm)`, the verified range shrinks as the word grows:
`m ≤ 30` for `T₂`, `m ≤ 20` for `T₃`, `m ≤ 10` for `T₂T₃`, `m ≤ 5` for `T₂T₃T₂`, `m ≤ 2` for
`T₃T₃T₃`. Beyond those ranges the plates are drawn by the same algorithm, unverified; the
eigenform property itself, for all `n` and `m`, is Mordell's theorem and is not proved here.
-/

namespace DeltaWordGraphs

open DeltaGraph

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## The coefficients of `Δ` up to `q⁶⁰` -/

/-- `τ(1), …, τ(60)`, as a literal list; certified against the eta product in
`tauTable_eq_deltaCoeffs`. -/
def tauTable : List ℤ :=
  [1, -24, 252, -1472, 4830, -6048, -16744, 84480, -113643, -115920, 534612, -370944, -577738,
   401856, 1217160, 987136, -6905934, 2727432, 10661420, -7109760, -4219488, -12830688,
   18643272, 21288960, -25499225, 13865712, -73279080, 24647168, 128406630, -29211840,
   -52843168, -196706304, 134722224, 165742416, -80873520, 167282496, -182213314, -255874080,
   -145589976, 408038400, 308120442, 101267712, -17125708, -786948864, -548895690, -447438528,
   2687348496, 248758272, -1696965207, 611981400, -1740295368, 850430336, -1596055698,
   1758697920, 2582175960, -1414533120, 2686677840, -3081759120, -5189203740, -1791659520]

/-- **The table is the eta product.** `tauTable` is exactly the expansion of
`q ∏_{m=1}^{60} (1 - qᵐ)²⁴` computed by `DeltaGraph.deltaCoeffs`. -/
theorem tauTable_eq_deltaCoeffs : tauTable = deltaCoeffs 60 := by decide

/-- `τ(n)` read off the table (`0` outside `1 ≤ n ≤ 60`). -/
def tauT (n : ℕ) : ℤ := tauTable.getD (n - 1) 0

private theorem eq_of_map_eq {α β : Type*} {f g : α → β} :
    ∀ {l : List α}, l.map f = l.map g → ∀ a ∈ l, f a = g a
  | [], _, _, ha => absurd ha List.not_mem_nil
  | _ :: l, h, a, ha => by
      simp only [List.map_cons, List.cons.injEq] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact h.1
      · exact eq_of_map_eq h.2 a ha'

/-- The first thirty entries are the thirty coefficients of `DeltaGraph.tau_table`. -/
theorem tauT_table : (List.range' 1 30).map tauT = (List.range' 1 30).map tau := by
  rw [tau_table]; decide

/-- `tauT` is `DeltaGraph.tau` on the plotted range. -/
theorem tauT_eq_tau {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ 30) : tauT n = tau n :=
  eq_of_map_eq tauT_table n (List.mem_range'_1.mpr ⟨h1, by omega⟩)

/-! ## The Hecke image of `Δ`, coefficient by coefficient -/

/-- The coefficient of `qᵐ` in `Tₙ Δ`: `∑_{d ∣ gcd(n,m)} d¹¹ τ(nm/d²)` (weight `k = 12`, so
`d^{k-1} = d¹¹`). -/
def heckeCoeff (n m : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd n m).divisors, (d : ℤ) ^ 11 * tauT (n * m / d ^ 2)

/-- The word `T₂`. -/
def wordT2 (m : ℕ) : ℤ := heckeCoeff 2 m

/-- The word `T₃`. -/
def wordT3 (m : ℕ) : ℤ := heckeCoeff 3 m

/-- The word `T₂T₃ = T₆` (coprime letters, no echo). -/
def wordT2T3 (m : ℕ) : ℤ := heckeCoeff 6 m

/-- The word `T₂T₃T₂ = T₁₂ + 2¹¹ T₃` (`HeckeWords.hmul_two_three_two`). -/
def wordT2T3T2 (m : ℕ) : ℤ := heckeCoeff 12 m + 2 ^ 11 * heckeCoeff 3 m

/-- The word `T₃T₃T₃ = T₂₇ + 2·3¹¹ T₃` (`HeckeWords.hmul_three_three_three`). -/
def wordT3T3T3 (m : ℕ) : ℤ := heckeCoeff 27 m + 2 * 3 ^ 11 * heckeCoeff 3 m

/-! ### Each word rescales the expansion by its multiplier

Verified on the range where the required coefficients `τ(nm)` are inside `tauTable`. -/

/-- `T₂ Δ = -24 Δ`, on coefficients `1 … 30`. -/
theorem wordT2_eq : ∀ m ∈ Finset.Icc 1 30, wordT2 m = -24 * tauT m := by decide

/-- `T₃ Δ = 252 Δ`, on coefficients `1 … 20`. -/
theorem wordT3_eq : ∀ m ∈ Finset.Icc 1 20, wordT3 m = 252 * tauT m := by decide

/-- `T₂T₃ Δ = -6048 Δ`, on coefficients `1 … 10`. -/
theorem wordT2T3_eq : ∀ m ∈ Finset.Icc 1 10, wordT2T3 m = -6048 * tauT m := by decide

/-- `T₂T₃T₂ Δ = 145152 Δ`, on coefficients `1 … 5`. -/
theorem wordT2T3T2_eq : ∀ m ∈ Finset.Icc 1 5, wordT2T3T2 m = 145152 * tauT m := by decide

/-- `T₃T₃T₃ Δ = 16003008 Δ`, on coefficients `1 … 2`. -/
theorem wordT3T3T3_eq : ∀ m ∈ Finset.Icc 1 2, wordT3T3T3 m = 16003008 * tauT m := by decide

/-- **The five multipliers**, read off the first coefficient of each word — the five numbers of
`DeltaGraph.tau_word_values`, and the five vertical scales of the plates. -/
theorem word_multipliers :
    [wordT2 1, wordT3 1, wordT2T3 1, wordT2T3T2 1, wordT3T3T3 1] =
      [(-24 : ℤ), 252, -6048, 145152, 16003008] := by decide

/-- The five scales increase: `24 < 252 < 6048 < 145152 < 16003008`. Each plate sits above the
previous one, by the printed offsets. -/
theorem word_abs_multipliers_strictMono :
    [wordT2 1, wordT3 1, wordT2T3 1, wordT2T3T2 1, wordT3T3T3 1].map Int.natAbs =
        [24, 252, 6048, 145152, 16003008] ∧
      24 < 252 ∧ 252 < 6048 ∧ 6048 < 145152 ∧ 145152 < 16003008 := by decide

/-! ### The trinity, on every one of the five graphs

`τ(2) = -24` and `τ(3) = 252` are both divisible by three, so every one of the five multipliers
is, and therefore so is every coefficient of every one of the five images. On each plate every
bar is red. -/

/-- Three divides every plotted coefficient of every one of the five words. -/
theorem word_coeffs_three_dvd :
    (∀ m ∈ Finset.Icc 1 30, (3 : ℤ) ∣ wordT2 m) ∧
      (∀ m ∈ Finset.Icc 1 20, (3 : ℤ) ∣ wordT3 m) ∧
      (∀ m ∈ Finset.Icc 1 10, (3 : ℤ) ∣ wordT2T3 m) ∧
      (∀ m ∈ Finset.Icc 1 5, (3 : ℤ) ∣ wordT2T3T2 m) ∧
      (∀ m ∈ Finset.Icc 1 2, (3 : ℤ) ∣ wordT3T3T3 m) := by decide

/-- A nonzero coefficient divisible by three has digital root in the trinity `{3, 6, 9}`. -/
theorem coeff_mem_trinity {x : ℤ} (hx : x ≠ 0) (h3 : (3 : ℤ) ∣ x) :
    Tesla369.digitalRoot x.natAbs ∈ Tesla369.trinity :=
  (digitalRoot_natAbs_mem_trinity_iff hx).mpr h3

/-- **The colouring of the five plates.** Every plotted coefficient of every word has digital
root `3`, `6` or `9`. -/
theorem word_coeffs_mem_trinity :
    (∀ m ∈ Finset.Icc 1 30, Tesla369.digitalRoot (wordT2 m).natAbs ∈ Tesla369.trinity) ∧
      (∀ m ∈ Finset.Icc 1 20, Tesla369.digitalRoot (wordT3 m).natAbs ∈ Tesla369.trinity) ∧
      (∀ m ∈ Finset.Icc 1 10, Tesla369.digitalRoot (wordT2T3 m).natAbs ∈ Tesla369.trinity) ∧
      (∀ m ∈ Finset.Icc 1 5, Tesla369.digitalRoot (wordT2T3T2 m).natAbs ∈ Tesla369.trinity) ∧
      (∀ m ∈ Finset.Icc 1 2, Tesla369.digitalRoot (wordT3T3T3 m).natAbs ∈ Tesla369.trinity) := by
  decide

/-! ## The plotted functions on the upper half plane -/

/-- The partial sum `∑_{m=1}^{N} c(m) qᵐ` of a `q`-expansion with integer coefficients: the
function drawn in the plates. With `c = DeltaGraph.tau` this is `DeltaGraph.deltaApprox`. -/
noncomputable def heckeApprox (c : ℕ → ℤ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.range N, (c (m + 1) : ℂ) * qParam z ^ (m + 1)

theorem heckeApprox_tau (N : ℕ) (z : ℂ) : heckeApprox tau N z = deltaApprox N z := rfl

/-- Every one of these partial sums has horizontal period one, for the same reason `Δ` does. -/
theorem heckeApprox_periodic (c : ℕ → ℤ) (N : ℕ) (z : ℂ) :
    heckeApprox c N (z + 1) = heckeApprox c N z := by
  simp [heckeApprox, qParam_add_one]

/-- **The graph of a word is the graph of `Δ`, rescaled.** If a coefficient sequence is
`lam · τ` on `1 … N`, its partial sum is `lam` times that of `Δ`. -/
theorem heckeApprox_eq_smul {c : ℕ → ℤ} {lam : ℤ} {N : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ N → c m = lam * tau m) (z : ℂ) :
    heckeApprox c N z = (lam : ℂ) * deltaApprox N z := by
  rw [heckeApprox, deltaApprox, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m + 1 ≤ N := Finset.mem_range.mp hm
  rw [h (m + 1) (Nat.le_add_left 1 m) hmN]
  push_cast
  ring

theorem heckeApprox_wordT2 (z : ℂ) :
    heckeApprox wordT2 30 z = (-24 : ℂ) * deltaApprox 30 z := by
  have := heckeApprox_eq_smul (c := wordT2) (lam := -24) (N := 30)
    (fun m h1 h2 => by rw [wordT2_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 h2]) z
  simpa using this

theorem heckeApprox_wordT3 (z : ℂ) :
    heckeApprox wordT3 20 z = (252 : ℂ) * deltaApprox 20 z := by
  have := heckeApprox_eq_smul (c := wordT3) (lam := 252) (N := 20)
    (fun m h1 h2 => by
      rw [wordT3_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 (by omega)]) z
  simpa using this

theorem heckeApprox_wordT2T3 (z : ℂ) :
    heckeApprox wordT2T3 10 z = (-6048 : ℂ) * deltaApprox 10 z := by
  have := heckeApprox_eq_smul (c := wordT2T3) (lam := -6048) (N := 10)
    (fun m h1 h2 => by
      rw [wordT2T3_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 (by omega)]) z
  simpa using this

theorem heckeApprox_wordT2T3T2 (z : ℂ) :
    heckeApprox wordT2T3T2 5 z = (145152 : ℂ) * deltaApprox 5 z := by
  have := heckeApprox_eq_smul (c := wordT2T3T2) (lam := 145152) (N := 5)
    (fun m h1 h2 => by
      rw [wordT2T3T2_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 (by omega)]) z
  simpa using this

theorem heckeApprox_wordT3T3T3 (z : ℂ) :
    heckeApprox wordT3T3T3 2 z = (16003008 : ℂ) * deltaApprox 2 z := by
  have := heckeApprox_eq_smul (c := wordT3T3T3) (lam := 16003008) (N := 2)
    (fun m h1 h2 => by
      rw [wordT3T3T3_eq m (Finset.mem_Icc.mpr ⟨h1, h2⟩), tauT_eq_tau h1 (by omega)]) z
  simpa using this

/-! ### What the plates show

A rescaling does three visible things: it multiplies the modulus everywhere by `|lam|`, it shifts
the logarithmic profile by the constant `log |lam|`, and — when `lam < 0` — it rotates every
colour of the phase portrait by half a turn. -/

/-- The modulus of a word's graph is `|lam|` times the modulus of `Δ`'s: same shape, new scale. -/
theorem heckeApprox_norm {c : ℕ → ℤ} {lam : ℤ} {N : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ N → c m = lam * tau m) (z : ℂ) :
    ‖heckeApprox c N z‖ = |(lam : ℝ)| * ‖deltaApprox N z‖ := by
  rw [heckeApprox_eq_smul h z, norm_mul]
  simp [Complex.norm_intCast]

/-- **The profile is shifted, not deformed.** Where `Δ ≠ 0` and `lam ≠ 0`, the logarithm of the
modulus of a word's graph is the logarithm of `Δ`'s plus the constant `log |lam|`. -/
theorem log_norm_heckeApprox {c : ℕ → ℤ} {lam : ℤ} {N : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ N → c m = lam * tau m) {z : ℂ} (hlam : lam ≠ 0)
    (hz : deltaApprox N z ≠ 0) :
    Real.log ‖heckeApprox c N z‖ = Real.log |(lam : ℝ)| + Real.log ‖deltaApprox N z‖ := by
  have hl : |(lam : ℝ)| ≠ 0 := by
    simpa using hlam
  rw [heckeApprox_norm h z, Real.log_mul hl (norm_ne_zero_iff.mpr hz)]

/-- **A negative multiplier is a half turn.** For `lam < 0` the word's graph is `|lam|` times
`e^{iπ} Δ`: every hue in the phase portrait is rotated by `π`. -/
theorem heckeApprox_neg_phase {c : ℕ → ℤ} {lam : ℤ} {N : ℕ}
    (h : ∀ m, 1 ≤ m → m ≤ N → c m = lam * tau m) (hlam : lam < 0) (z : ℂ) :
    heckeApprox c N z = ((|(lam : ℝ)| : ℝ) : ℂ) * Complex.exp (Real.pi * Complex.I) *
      deltaApprox N z := by
  rw [heckeApprox_eq_smul h z, Complex.exp_pi_mul_I]
  have : |(lam : ℝ)| = -(lam : ℝ) := abs_of_neg (by exact_mod_cast hlam)
  rw [this]
  push_cast
  ring

end DeltaWordGraphs

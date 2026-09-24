import Mathlib
import RequestProject.DeltaDissection

/-!
# Frobenius, applied twice to the character

`RequestProject/DeltaDissection.lean` cut the portrait of `Δ` into Euclid's ternary cells, read
`‖Δ‖` inside each part and normalised the readings into a *character* — a matrix of grey levels
in `[0,1]`. There are two Frobeniuses one can apply to a character, and this file applies both.

**The Frobenius of linear algebra.** `frobInner` is the entrywise inner product of two blocks of
pixels and `frobNorm A = √⟪A, A⟫` the Frobenius norm — the length of the character read as a
vector of pixels. The mirror `z ↦ −z̄` of the portrait acts on characters by reversing columns
(`mirrorMat`); it is a Frobenius isometry (`frobNorm_mirror`), and the character of `Δ` is
*fixed* by it (`mirrorMat_glyph`), so the character and its mirror image have Frobenius cosine
similarity exactly one (`frobInner_glyph_mirror`). The size of the character is pinned between
`√(m+1)` and `√((m+1)(2m+2))` (`sqrt_rows_le_frobNorm_glyph`, `frobNorm_glyph_le`): every row
of the character is normalised, and no pixel exceeds one.

**The Frobenius of arithmetic.** Quantising the character to three grey levels lands it in
`ZMod 3`, where the Frobenius endomorphism `x ↦ x³` is the identity (`pix_frobenius`): the
three-shade glyph is Frobenius-stable, pixel by pixel. On the arithmetic side of `Δ` the datum
attached to Frobenius at a prime `p` is the trace `τ(p)` (`frobTrace`), and on the range where
the coefficients are certified the trace is a sum of two power characters modulo `27`,

`τ(p) ≡ p² + p⁹  (mod 27)`,  `2 + 9 = 11 = k − 1`,

(`frobTrace_mod_27`, `frobTrace_zmod_27`) — and applying the Frobenius `x ↦ x³` of `ZMod 3`
twice collapses `p⁹` to `p`, leaving `τ(p) ≡ p² + p ≡ p(p+1) (mod 3)` (`frobTrace_zmod_3`),
whence three divides `τ(p)` exactly when `p ≢ 1 (mod 3)` (`three_dvd_tau_iff_not_one_mod_three`).

The two Frobeniuses meet in `frobNorm_traceRow_le`: the row of normalised Frobenius traces
`τ(p)/p^{11/2}` over the ten primes below thirty has Frobenius norm at most `2√10`, the
Ramanujan–Deligne bound read as a length.
-/

noncomputable section

set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

open Complex

namespace DeltaFrobenius

open DeltaDissection

/-! ## The Frobenius norm of a block of pixels -/

/-- The Frobenius (entrywise) inner product of two blocks of pixels. -/
def frobInner {p q : ℕ} (A B : Fin p → Fin q → ℝ) : ℝ := ∑ r, ∑ c, A r c * B r c

/-- The Frobenius norm of a block of pixels. -/
def frobNorm {p q : ℕ} (A : Fin p → Fin q → ℝ) : ℝ := Real.sqrt (frobInner A A)

theorem frobInner_self_nonneg {p q : ℕ} (A : Fin p → Fin q → ℝ) : 0 ≤ frobInner A A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem frobNorm_nonneg {p q : ℕ} (A : Fin p → Fin q → ℝ) : 0 ≤ frobNorm A := Real.sqrt_nonneg _

theorem frobNorm_sq {p q : ℕ} (A : Fin p → Fin q → ℝ) : frobNorm A ^ 2 = frobInner A A :=
  Real.sq_sqrt (frobInner_self_nonneg A)

/-- The mirror of a block of pixels: the reflection of the portrait in the wall `x = 0`,
which reverses the columns. -/
def mirrorMat {m : ℕ} (A : Fin (m + 1) → Fin (2 * m + 2) → ℝ) :
    Fin (m + 1) → Fin (2 * m + 2) → ℝ := fun r c => A r (mirrorCol c)

/-- Reversing the columns is a permutation of the pixels, so it preserves the Frobenius inner
product. -/
theorem frobInner_mirror {m : ℕ} (A B : Fin (m + 1) → Fin (2 * m + 2) → ℝ) :
    frobInner (mirrorMat A) (mirrorMat B) = frobInner A B := by
  refine Finset.sum_congr rfl fun r _ => ?_
  exact Fintype.sum_equiv (Function.Involutive.toPerm mirrorCol mirrorCol_involutive) _ _
    fun c => rfl

/-- The mirror is a Frobenius isometry. -/
theorem frobNorm_mirror {m : ℕ} (A : Fin (m + 1) → Fin (2 * m + 2) → ℝ) :
    frobNorm (mirrorMat A) = frobNorm A := by
  rw [frobNorm, frobNorm, frobInner_mirror]

/-! ## The character of `Δ` under the Frobenius norm -/

/-- **The character of `Δ` is fixed by the mirror**, as a block of pixels. -/
theorem mirrorMat_glyph {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) (m : ℕ) :
    mirrorMat (glyph k j₀ m) = glyph k j₀ m := by
  funext r c
  exact glyph_mirror hj r c

/-- **Frobenius cosine similarity one**: the character and its mirror image are the same vector
of pixels, so their Frobenius inner product is the square of the Frobenius norm. -/
theorem frobInner_glyph_mirror {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) (m : ℕ) :
    frobInner (glyph k j₀ m) (mirrorMat (glyph k j₀ m)) = frobNorm (glyph k j₀ m) ^ 2 := by
  rw [mirrorMat_glyph hj, frobNorm_sq]

/-- **The character has Frobenius norm at least `√(m+1)`**: every one of its `m + 1` rows is
normalised, so every row contributes a black pixel. -/
theorem sqrt_rows_le_frobNorm_glyph {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) (m : ℕ) :
    Real.sqrt ((m : ℝ) + 1) ≤ frobNorm (glyph k j₀ m) := by
  refine Real.sqrt_le_sqrt ?_
  have hrow : ∀ r : Fin (m + 1), (1 : ℝ) ≤ ∑ c, glyph k j₀ m r c * glyph k j₀ m r c := by
    intro r
    obtain ⟨c, hc⟩ := glyph_row_eq_one (k := k) hj r
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun c' => glyph k j₀ m r c' * glyph k j₀ m r c')
      (fun _ _ => mul_self_nonneg _) (Finset.mem_univ c))
    show (1 : ℝ) ≤ glyph k j₀ m r c * glyph k j₀ m r c
    rw [hc]
    norm_num
  calc ((m : ℝ) + 1) = ∑ _r : Fin (m + 1), (1 : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        push_cast
        ring
    _ ≤ frobInner (glyph k j₀ m) (glyph k j₀ m) := Finset.sum_le_sum fun r _ => hrow r

theorem one_le_frobNorm_glyph {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) (m : ℕ) :
    1 ≤ frobNorm (glyph k j₀ m) := by
  refine le_trans ?_ (sqrt_rows_le_frobNorm_glyph hj m)
  rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
  exact Real.sqrt_le_sqrt (by norm_num [le_add_of_nonneg_left, Nat.cast_nonneg])

/-- The character has Frobenius norm at most `√((m+1)(2m+2))`: every pixel is at most black. -/
theorem frobNorm_glyph_le {k : ℕ} {j₀ : ℤ} (hj : 0 ≤ j₀) (m : ℕ) :
    frobNorm (glyph k j₀ m) ≤ Real.sqrt ((m + 1) * (2 * m + 2)) := by
  refine Real.sqrt_le_sqrt ?_
  have hbound : ∀ r : Fin (m + 1), ∑ c, glyph k j₀ m r c * glyph k j₀ m r c
      ≤ (2 * (m : ℝ) + 2) := by
    intro r
    have hone : ∀ c : Fin (2 * m + 2), glyph k j₀ m r c * glyph k j₀ m r c ≤ 1 := by
      intro c
      have h0 := glyph_nonneg (k := k) hj r c
      have h1 := glyph_le_one (k := k) hj r c
      nlinarith
    calc ∑ c, glyph k j₀ m r c * glyph k j₀ m r c
        ≤ ∑ _c : Fin (2 * m + 2), (1 : ℝ) := Finset.sum_le_sum fun c _ => hone c
      _ = (2 * (m : ℝ) + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
          push_cast
          ring
  calc frobInner (glyph k j₀ m) (glyph k j₀ m)
      ≤ ∑ _r : Fin (m + 1), (2 * (m : ℝ) + 2) := Finset.sum_le_sum fun r _ => hbound r
    _ = ((m : ℝ) + 1) * (2 * (m : ℝ) + 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## The Frobenius endomorphism on the quantised character -/

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- **The three-shade character is Frobenius-stable.** In `ZMod 3` the Frobenius endomorphism
`x ↦ x³` is the identity, so quantising the character to the three grey levels of the ternary
dissection produces a glyph fixed, pixel by pixel, by Frobenius. -/
theorem pix_frobenius (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) :
    pix k j₀ m r c ^ 3 = pix k j₀ m r c := ZMod.pow_card _

/-- The same statement in the language of the Frobenius endomorphism of `ZMod 3`. -/
theorem frobenius_pix (k : ℕ) (j₀ : ℤ) (m : ℕ) (r : Fin (m + 1)) (c : Fin (2 * m + 2)) :
    frobenius (ZMod 3) 3 (pix k j₀ m r c) = pix k j₀ m r c := by
  rw [frobenius_def]
  exact ZMod.pow_card _

/-! ## The arithmetic Frobenius: the trace `τ(p)` -/

/-- **The trace of Frobenius at `p`.** The number the Galois representation attached to `Δ`
records at the prime `p` is `τ(p)`; we use it here only as this datum. -/
def frobTrace (p : ℕ) : ℤ := DeltaGraph.tau p

/-- **Checked for every prime `p ≤ 30` other than three**: the trace of Frobenius is the sum of
the two power characters `p ↦ p²` and `p ↦ p⁹` modulo `27`, whose exponents add up to
`11 = k − 1`, the weight of `Δ` minus one. -/
theorem frobTrace_mod_27 : ∀ p ∈ Finset.Icc 1 30, p.Prime → p ≠ 3 →
    (27 : ℤ) ∣ frobTrace p - ((p : ℤ) ^ 2 + (p : ℤ) ^ 9) := by decide

theorem frobTrace_zmod_27 {p : ℕ} (hp : p ∈ Finset.Icc 1 30) (hpp : p.Prime) (h3 : p ≠ 3) :
    ((frobTrace p : ℤ) : ZMod 27) = (p : ZMod 27) ^ 2 + (p : ZMod 27) ^ 9 := by
  have h := frobTrace_mod_27 p hp hpp h3
  have h0 : ((frobTrace p - ((p : ℤ) ^ 2 + (p : ℤ) ^ 9) : ℤ) : ZMod 27) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  push_cast at h0
  linear_combination h0

/-- **Applying Frobenius.** In `ZMod 3` the map `x ↦ x³` is the identity, so `p⁹ = (p³)³ = p`
and the mod-`27` shape of the trace collapses to `τ(p) ≡ p² + p = p(p+1) (mod 3)`. -/
theorem frobTrace_zmod_3 {p : ℕ} (hp : p ∈ Finset.Icc 1 30) (hpp : p.Prime) (h3 : p ≠ 3) :
    ((frobTrace p : ℤ) : ZMod 3) = (p : ZMod 3) * ((p : ZMod 3) + 1) := by
  have h := frobTrace_mod_27 p hp hpp h3
  have h3d : (3 : ℤ) ∣ frobTrace p - ((p : ℤ) ^ 2 + (p : ℤ) ^ 9) :=
    dvd_trans (by norm_num) h
  have h0 : ((frobTrace p - ((p : ℤ) ^ 2 + (p : ℤ) ^ 9) : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h3d
  push_cast at h0
  have hfrob : ((p : ZMod 3)) ^ 9 = (p : ZMod 3) := by
    have h1 : ((p : ZMod 3)) ^ 3 = (p : ZMod 3) := ZMod.pow_card _
    calc ((p : ZMod 3)) ^ 9 = (((p : ZMod 3)) ^ 3) ^ 3 := by ring
      _ = (p : ZMod 3) := by rw [h1, h1]
  rw [hfrob] at h0
  linear_combination h0

/-- **The trinity, read off Frobenius.** For a prime `p ≤ 30` other than three, three divides
`τ(p)` — equivalently the digital root of `|τ(p)|` lies in `{3, 6, 9}` — exactly when `p` is not
congruent to one modulo three. -/
theorem three_dvd_tau_iff_not_one_mod_three : ∀ p ∈ Finset.Icc 1 30, p.Prime → p ≠ 3 →
    ((3 : ℤ) ∣ DeltaGraph.tau p ↔ p % 3 ≠ 1) := by decide

/-! ## The two Frobeniuses in one place -/

/-- The ten primes below thirty. -/
def primes30 : Fin 10 → ℕ := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

/-- The normalised trace of Frobenius `τ(p) / p^{11/2}`. -/
def normTrace (p : ℕ) : ℝ := (DeltaGraph.tau p : ℝ) / Real.sqrt ((p : ℝ) ^ 11)

/-- The row of normalised Frobenius traces over the ten primes below thirty, as a block of
pixels of one row. -/
def traceRow : Fin 1 → Fin 10 → ℝ := fun _ c => normTrace (primes30 c)

/-- Ramanujan's bound on the ten primes below thirty, in the form `τ(p)² ≤ 4 p¹¹`. -/
theorem tau_sq_le : ∀ p ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29], (DeltaGraph.tau p) ^ 2
    ≤ 4 * (p : ℤ) ^ 11 := by decide

theorem normTrace_sq_le {p : ℕ} (hp : p ∈ [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]) :
    normTrace p ^ 2 ≤ 4 := by
  have hp1 : 1 ≤ p := by fin_cases hp <;> norm_num
  have hppos : (0 : ℝ) < (p : ℝ) ^ 11 := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp1
    positivity
  have hsq : Real.sqrt ((p : ℝ) ^ 11) ^ 2 = (p : ℝ) ^ 11 := Real.sq_sqrt hppos.le
  have hb : ((DeltaGraph.tau p : ℝ)) ^ 2 ≤ 4 * (p : ℝ) ^ 11 := by
    exact_mod_cast tau_sq_le p hp
  rw [normTrace, div_pow, hsq, div_le_iff₀ hppos]
  linarith

/-- **The Ramanujan–Deligne bound as a Frobenius norm.** The row of normalised Frobenius traces
over the ten primes below thirty has Frobenius norm at most `2√10`. -/
theorem frobNorm_traceRow_le : frobNorm traceRow ≤ 2 * Real.sqrt 10 := by
  have hsum : frobInner traceRow traceRow ≤ 40 := by
    have h : ∀ c : Fin 10, traceRow 0 c * traceRow 0 c ≤ 4 := by
      intro c
      have h2 := normTrace_sq_le (p := primes30 c) (by fin_cases c <;> simp [primes30])
      simpa [traceRow, pow_two] using h2
    calc frobInner traceRow traceRow = ∑ c : Fin 10, traceRow 0 c * traceRow 0 c := by
          simp [frobInner]
      _ ≤ ∑ _c : Fin 10, (4 : ℝ) := Finset.sum_le_sum fun c _ => h c
      _ = 40 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          norm_num
  calc frobNorm traceRow ≤ Real.sqrt 40 := Real.sqrt_le_sqrt hsum
    _ = 2 * Real.sqrt 10 := by
        rw [show (40 : ℝ) = 2 ^ 2 * 10 by norm_num, Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by norm_num)]

end DeltaFrobenius

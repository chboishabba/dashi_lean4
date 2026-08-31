/-
# Row A1 (source lane) — the size of the eliminated-coordinate derivative

`EliminatedCoordinateDerivative` closes the *algebra* of the constrained
substitution: from `Q(U)C(U) = 0` it derives `Q C' = −Q'C`, and the pivot solve
determines

    C' = E·X ,      X = −P⁻¹·(Q'·C) .                                   (★)

That is an identity, not an estimate.  The Row A1a Gaussian sector, however, is
driven by a *quantitative* datum: the constant `K_D` in

    |D(q)_{ab}| ≤ K_D‖q‖ ,      K_D ≤ 1/2 ,

for the Lorentz-diagonal averaging / constrained-projection variation.  This file
supplies the missing arithmetic step: it turns entrywise size bounds on the
objects appearing in (★) into the constant `K_D`, so that the linear-vanishing
input of Row A1a is *computed* from source regularity estimates on `Q'`, on the
pivot inverse `P⁻¹`, on the elimination injection `E` and on the substitution
`C`, instead of being posited.

Main results:

* `abs_matmul_entry_le` — the entrywise bound for a matrix product over an
  arbitrary finite index type;
* `abs_triple_matmul_entry_le` — the same for a triple product;
* `eliminatedDerivative_entry_bound` — the size of `C'` from (★);
* `eliminatedDerivative_linear_bound` — **if the source estimate for `Q'`
  vanishes linearly at zero momentum, so does `C'`, with the explicit constant**

      K_D = |c|²·|n|·e·p·K_Q·c_C ;

* `eliminatedDerivative_smallField` — and the Row A1a smallness `K_D ≤ 1/2` then
  holds as soon as the source constants satisfy the corresponding explicit
  inequality, which is the small-field condition.

**Honest status — Row A1 is not closed.**  The four entrywise bounds are the
source estimates being invoked; what is removed is any freedom in how they
combine into the constant Row A1a consumes.
-/
import RequestProject.YangMills.EliminatedCoordinateDerivative

namespace YangMills

open Matrix Finset

/-! ## 1. Entrywise bounds for matrix products over arbitrary index types -/

/-- **Entrywise bound for a matrix product.** -/
theorem abs_matmul_entry_le {ι κ ρ : Type*} [Fintype κ] {A : Matrix ι κ ℝ} {B : Matrix κ ρ ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i : ι) (j : ρ) : |(A * B) i j| ≤ Fintype.card κ * (a * b) := by
  rw [Matrix.mul_apply]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ k ∈ (Finset.univ : Finset κ), |A i k * B k j| ≤ a * b := by
    intro k _
    rw [abs_mul]
    exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) ha
  calc ∑ k : κ, |A i k * B k j| ≤ ∑ _k : κ, a * b := Finset.sum_le_sum hterm
    _ = Fintype.card κ * (a * b) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Entrywise bound for a triple matrix product.** -/
theorem abs_triple_matmul_entry_le {ι κ ρ σ : Type*} [Fintype κ] [Fintype ρ]
    {A : Matrix ι κ ℝ} {B : Matrix κ ρ ℝ} {C : Matrix ρ σ ℝ} {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b) (hC : ∀ i j, |C i j| ≤ c)
    (i : ι) (j : σ) :
    |(A * (B * C)) i j| ≤ Fintype.card κ * Fintype.card ρ * (a * (b * c)) := by
  have hBC : ∀ (k : κ) (l : σ), |(B * C) k l| ≤ Fintype.card ρ * (b * c) :=
    fun k l => abs_matmul_entry_le hb hB hC k l
  have h := abs_matmul_entry_le (A := A) (B := B * C) ha hA hBC i j
  calc |(A * (B * C)) i j| ≤ Fintype.card κ * (a * (Fintype.card ρ * (b * c))) := h
    _ = Fintype.card κ * Fintype.card ρ * (a * (b * c)) := by ring

/-! ## 2. The size of the eliminated-coordinate derivative -/

variable {c n m : Type*} [Fintype c] [Fintype n]

/-- **The size of the substitution derivative, from the pivot solve.**  With
`C' = E·(−P⁻¹·(Q'·C))`, entrywise bounds on the four factors give an entrywise
bound on `C'`. -/
theorem eliminatedDerivative_entry_bound
    {E : Matrix n c ℝ} {Pinv : Matrix c c ℝ} {Q' : Matrix c n ℝ} {Cm : Matrix n m ℝ}
    {e p q cc : ℝ} (he : 0 ≤ e) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hE : ∀ i j, |E i j| ≤ e) (hP : ∀ i j, |Pinv i j| ≤ p)
    (hQ : ∀ i j, |Q' i j| ≤ q) (hC : ∀ i j, |Cm i j| ≤ cc)
    (i : n) (j : m) :
    |(E * (-(Pinv * (Q' * Cm)))) i j|
      ≤ Fintype.card c * Fintype.card c * Fintype.card n * (e * (p * (q * cc))) := by
  have hQC : ∀ (k : c) (l : m), |(Q' * Cm) k l| ≤ Fintype.card n * (q * cc) :=
    fun k l => abs_matmul_entry_le hq hQ hC k l
  have hneg : ∀ (k : c) (l : m), |(-(Pinv * (Q' * Cm))) k l|
      ≤ Fintype.card c * Fintype.card n * (p * (q * cc)) := by
    intro k l
    rw [Matrix.neg_apply, abs_neg]
    exact abs_triple_matmul_entry_le (A := Pinv) (B := Q') (C := Cm) hp hq hP hQ hC k l
  have h := abs_matmul_entry_le (A := E) (B := -(Pinv * (Q' * Cm))) he hE hneg i j
  calc |(E * (-(Pinv * (Q' * Cm)))) i j|
      ≤ Fintype.card c * (e * (Fintype.card c * Fintype.card n * (p * (q * cc)))) := h
    _ = Fintype.card c * Fintype.card c * Fintype.card n * (e * (p * (q * cc))) := by ring

/-- The constant that the four source estimates produce. -/
noncomputable def eliminatedDerivativeConstant (cardC cardN : ℕ) (e p KQ cc : ℝ) : ℝ :=
  cardC * cardC * cardN * (e * (p * (KQ * cc)))

theorem eliminatedDerivativeConstant_nonneg {cardC cardN : ℕ} {e p KQ cc : ℝ}
    (he : 0 ≤ e) (hp : 0 ≤ p) (hKQ : 0 ≤ KQ) (hcc : 0 ≤ cc) :
    0 ≤ eliminatedDerivativeConstant cardC cardN e p KQ cc := by
  unfold eliminatedDerivativeConstant
  positivity

/-- **The linear vanishing of the substitution derivative, from the source
estimate on `Q'`.**  If the averaging derivative obeys `|Q'(x)_{ij}| ≤ K_Q‖x‖`,
the eliminated-coordinate derivative obeys the same linear bound with the
computed constant `|c|²·|n|·e·p·K_Q·c_C`.  This is precisely the datum `K_D` that
the Row A1a Gaussian sector consumes. -/
theorem eliminatedDerivative_linear_bound
    {E : Matrix n c ℝ} {Pinv : Matrix c c ℝ} {Cm : Matrix n m ℝ}
    {Qp : (Fin 4 → ℝ) → Matrix c n ℝ} {e p KQ cc : ℝ}
    (he : 0 ≤ e) (hp : 0 ≤ p) (hKQ : 0 ≤ KQ)
    (hE : ∀ i j, |E i j| ≤ e) (hP : ∀ i j, |Pinv i j| ≤ p)
    (hC : ∀ i j, |Cm i j| ≤ cc)
    (hQ : ∀ x i j, |Qp x i j| ≤ KQ * ‖x‖)
    (x : Fin 4 → ℝ) (i : n) (j : m) :
    |(E * (-(Pinv * (Qp x * Cm)))) i j|
      ≤ eliminatedDerivativeConstant (Fintype.card c) (Fintype.card n) e p KQ cc * ‖x‖ := by
  have hnorm : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hbound := eliminatedDerivative_entry_bound (E := E) (Pinv := Pinv) (Q' := Qp x)
    (Cm := Cm) he hp (mul_nonneg hKQ hnorm) hE hP (hQ x) hC i j
  have hrw : (Fintype.card c : ℝ) * Fintype.card c * Fintype.card n
        * (e * (p * (KQ * ‖x‖ * cc)))
      = eliminatedDerivativeConstant (Fintype.card c) (Fintype.card n) e p KQ cc * ‖x‖ := by
    unfold eliminatedDerivativeConstant; ring
  rw [← hrw]
  exact hbound

/-- **The Row A1a small-field condition, written in source constants.**  The
Gaussian sector needs `K_D ≤ 1/2`; with `K_D` computed from the pivot solve this
is an explicit inequality among the four source estimates. -/
theorem eliminatedDerivative_smallField {cardC cardN : ℕ} {e p KQ cc : ℝ}
    (h : (cardC : ℝ) * cardC * cardN * (e * (p * (KQ * cc))) ≤ 1 / 2) :
    eliminatedDerivativeConstant cardC cardN e p KQ cc ≤ 1 / 2 := h

end YangMills

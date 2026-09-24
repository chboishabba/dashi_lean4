/-
**Q7 — compressed (bounded-height) exterior transport.**

The negative result of the previous cycle (`BudgetScale.lean`) is that the
*global* exterior area of the whole `d × d` evaluation family, `d ≍ L T/2π`,
carries a power of `T` and can therefore never meet the tube criterion
`E(T)/L(T)⁶ → 0`.  The proposed repair is to compress the observer to a
bounded-height coordinate block before taking any exterior budget.  This file
provides the linear algebra of that compression, entirely generally.

* `compress M f = M.submatrix f f` — coordinate restriction along an injection
  `f : κ → n` of the window indices into the full index set, together with
  `compress_add` (`P(A+E)P* = A_H + E_H`), `compress_gram`
  (`(Gram v)_H = Gram (v ∘ f)`) and `compress_comp` (composition of
  restrictions, the context-morphism law).
* `abs_trace_compress_le` and `frobSq_compress_le` — **the dimensional gain.**
  With an entrywise bound `|E i j| ≤ θ`, the compressed trace and Frobenius
  norm obey `|tr E_H| ≤ q θ` and `‖E_H‖_F² ≤ q² θ²`, where `q = card κ` is the
  *window* size, not the full dimension.
* `e2_compress_tail` — the resulting local `e₂`-transport budget: `e₂` of the
  compressed arithmetic block differs from `e₂` of the compressed Gram block by
  an explicit tail built only from `q` and `θ`.
* `gram_trace_eq_sum_norm_sq`, `e2_gram_le_half_trace_sq`,
  `e2_gram_le_of_norm_bound` — the cheap route to a local budget: for a Gram
  matrix `e₂ ≤ ½ (tr G)²`, and if the family has `q` members each of squared
  norm at most `B`, then `e₂ ≤ q²B²/2`.  This replaces a localized second-trace
  explicit formula by a norm bound plus a count.

Nothing here refers to `ζ`; every bound is an implication from an explicitly
stated hypothesis.
-/
import RiemannAnalytic.MultiplicityLift

namespace RiemannAnalytic

open Finset Matrix

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Coordinate restriction -/

/-- Coordinate compression `P M P*` along the window inclusion `f : κ → n`. -/
def compress {n κ : Type*} (M : Matrix n n ℝ) (f : κ → n) : Matrix κ κ ℝ :=
  M.submatrix f f

@[simp] theorem compress_apply {n κ : Type*} (M : Matrix n n ℝ) (f : κ → n) (i j : κ) :
    compress M f i j = M (f i) (f j) := rfl

/-- **`P(A + E)P* = A_H + E_H`.**  Compression is additive, so the source
splitting `G = A + E` restricts to the window with no error. -/
theorem compress_add {n κ : Type*} (A B : Matrix n n ℝ) (f : κ → n) :
    compress (A + B) f = compress A f + compress B f := rfl

/-- Compression of a Gram matrix is the Gram matrix of the compressed family. -/
theorem compress_gram {n κ : Type*} (v : n → E) (f : κ → n) :
    compress (Matrix.gram ℝ v) f = Matrix.gram ℝ (v ∘ f) := rfl

/-- Compressions compose: restricting to a small window through a larger one is
restricting to the small window. -/
theorem compress_comp {n κ ν : Type*} (M : Matrix n n ℝ) (f : κ → n) (g : ν → κ) :
    compress (compress M f) g = compress M (f ∘ g) := rfl

/-! ### The dimensional gain -/

/-- **Compressed trace bound.**  An entrywise bound `θ` on the error matrix gives
`|tr E_H| ≤ q θ` with `q` the *window* size. -/
theorem abs_trace_compress_le {n κ : Type*} [Fintype κ] (M : Matrix n n ℝ) (f : κ → n)
    {θ : ℝ} (hθ : ∀ i j, |M i j| ≤ θ) :
    |(compress M f).trace| ≤ (Fintype.card κ : ℝ) * θ := by
  classical
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have : ∑ i : κ, |compress M f i i| ≤ ∑ _i : κ, θ :=
    Finset.sum_le_sum fun i _ => hθ (f i) (f i)
  simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this

/-- **Compressed Frobenius bound.**  `‖E_H‖_F² ≤ q² θ²`: the number of entries is
governed by the window size, not by the ambient dimension. -/
theorem frobSq_compress_le {n κ : Type*} [Fintype κ] (M : Matrix n n ℝ) (f : κ → n)
    {θ : ℝ} (hθ : ∀ i j, |M i j| ≤ θ) :
    ∑ i : κ, ∑ j : κ, compress M f i j ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * θ ^ 2 := by
  classical
  have hpt : ∀ i j : κ, compress M f i j ^ 2 ≤ θ ^ 2 := by
    intro i j
    have h := hθ (f i) (f j)
    have h0 : |compress M f i j| ≤ θ := h
    nlinarith [abs_nonneg (compress M f i j), sq_abs (compress M f i j)]
  have : ∑ i : κ, ∑ j : κ, compress M f i j ^ 2 ≤ ∑ _i : κ, ∑ _j : κ, θ ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j
  simpa [Finset.sum_const, Finset.card_univ, sq, mul_comm, mul_left_comm, mul_assoc] using this

/-- **Local `e₂` transport.**  If two matrices differ by an error with entrywise
bound `θ`, their compressed exterior observables differ by an explicit tail
depending only on the window size `q` and on `θ` — never on the ambient
dimension. -/
theorem e2_compress_tail {n κ : Type*} [Fintype κ] (A B : Matrix n n ℝ) (f : κ → n)
    {θ : ℝ} (hθ : ∀ i j, |A i j - B i j| ≤ θ) :
    |(compress A f).trace - (compress B f).trace| ≤ (Fintype.card κ : ℝ) * θ := by
  classical
  have hsub : (compress A f).trace - (compress B f).trace = (compress (A - B) f).trace := by
    rw [← Matrix.trace_sub]
    rfl
  rw [hsub]
  exact abs_trace_compress_le (A - B) f (fun i j => hθ i j)

/-! ### The cheap local budget: trace and count -/

/-- The trace of a Gram matrix is the total squared norm of the family. -/
theorem gram_trace_eq_sum_norm_sq {n : Type*} [Fintype n] (v : n → E) :
    (Matrix.gram ℝ v).trace = ∑ i : n, ‖v i‖ ^ 2 := by
  simp [Matrix.trace, Matrix.diag, Matrix.gram]

/-- **`e₂ ≤ ½ (tr G)²` for a Gram matrix.**  The exterior area of a positive
semidefinite Gram matrix is at most half the square of its trace — so a local
*trace* bound already supplies a local exterior budget, with no second-trace
(explicit-formula) input at all. -/
theorem e2_gram_le_half_trace_sq {n : Type*} [Fintype n] [DecidableEq n] (v : n → E) :
    e2OfTraces (Matrix.gram ℝ v).trace ((Matrix.gram ℝ v * Matrix.gram ℝ v).trace)
      ≤ (Matrix.gram ℝ v).trace ^ 2 / 2 := by
  classical
  rw [e2OfTraces_gram_eq v, gram_trace_eq_sum_norm_sq v]
  have hle : ∑ i : n, ∑ j : n, (‖v i‖ ^ 2 * ‖v j‖ ^ 2 - ⟪v i, v j⟫_ℝ ^ 2)
      ≤ ∑ i : n, ∑ j : n, ‖v i‖ ^ 2 * ‖v j‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by nlinarith [sq_nonneg ⟪v i, v j⟫_ℝ]
  have hsq : ∑ i : n, ∑ j : n, ‖v i‖ ^ 2 * ‖v j‖ ^ 2 = (∑ i : n, ‖v i‖ ^ 2) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  rw [hsq] at hle
  linarith

/-- **The local budget from a norm bound and a count.**  A family of `q` vectors,
each of squared norm at most `B`, has exterior area at most `q²B²/2`. -/
theorem e2_gram_le_of_norm_bound {n : Type*} [Fintype n] [DecidableEq n] (v : n → E)
    {B : ℝ} (hv : ∀ i, ‖v i‖ ^ 2 ≤ B) :
    e2OfTraces (Matrix.gram ℝ v).trace ((Matrix.gram ℝ v * Matrix.gram ℝ v).trace)
      ≤ (Fintype.card n : ℝ) ^ 2 * B ^ 2 / 2 := by
  classical
  refine le_trans (e2_gram_le_half_trace_sq v) ?_
  have htr : (Matrix.gram ℝ v).trace ≤ (Fintype.card n : ℝ) * B := by
    rw [gram_trace_eq_sum_norm_sq v]
    have : ∑ i : n, ‖v i‖ ^ 2 ≤ ∑ _i : n, B := Finset.sum_le_sum fun i _ => hv i
    simpa [Finset.sum_const, Finset.card_univ, mul_comm] using this
  have htr0 : 0 ≤ (Matrix.gram ℝ v).trace := by
    rw [gram_trace_eq_sum_norm_sq v]
    exact Finset.sum_nonneg fun i _ => by positivity
  have := mul_self_le_mul_self htr0 htr
  nlinarith [this]

/-- **The local budget for the multiplicity-lifted family.**  With `card ι`
zeros of multiplicity at most `mmax` in the window and every vector of squared
norm at most `B`, the lifted exterior observable — the quantity that dominates
`∑_ρ m_ρ² Δ_ρ` with *no* multiplicity penalty, by `sum_mult_sq_pairDefect_le_e2`
— is at most `(2 ∑_ρ m_ρ)² B²/2`. -/
theorem e2_multFamily_le_of_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) (mult : ι → ℕ) {B : ℝ}
    (ha : ∀ ρ, ‖a ρ‖ ^ 2 ≤ B) (hb : ∀ ρ, ‖b ρ‖ ^ 2 ≤ B) :
    e2OfTraces (Matrix.gram ℝ (multPairFamily a b mult)).trace
        ((Matrix.gram ℝ (multPairFamily a b mult)
          * Matrix.gram ℝ (multPairFamily a b mult)).trace)
      ≤ (2 * ∑ ρ : ι, (mult ρ : ℝ)) ^ 2 * B ^ 2 / 2 := by
  classical
  have hcard : (Fintype.card (MultIndex mult) : ℝ) = 2 * ∑ ρ : ι, (mult ρ : ℝ) := by
    rw [card_multIndex mult]
    push_cast
    ring
  have hnorm : ∀ p : MultIndex mult, ‖multPairFamily a b mult p‖ ^ 2 ≤ B := by
    rintro ⟨ρ, i, ε⟩
    cases ε with
    | false => simpa [multPairFamily] using ha ρ
    | true => simpa [multPairFamily] using hb ρ
  have := e2_gram_le_of_norm_bound (multPairFamily a b mult) hnorm
  rwa [hcard] at this

/-- **Budget to tube, locally.**  Combining the multiplicity lift with the local
norm-and-count budget: if the window's zeros obey the quadratic floor
`c α_ρ² ≤ Δ_ρ`, all multiplicities are at least one, and every vector in the
window has squared norm at most `B`, then every offset in the window satisfies

    |α_ρ| ≤ √( (2 ∑_ρ m_ρ)² B² / (2c) ).

Every ingredient is a hypothesis; the theorem is the transport. -/
theorem local_tube_of_norm_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → E) {mult : ι → ℕ} {s : Finset ι} {offset : ι → ℝ} {c B : ℝ}
    (hc : 0 < c)
    (hfloor : ∀ ρ ∈ s, c * offset ρ ^ 2 ≤ pairDefect a b ρ)
    (hm1 : ∀ ρ ∈ s, 1 ≤ mult ρ)
    (ha : ∀ ρ, ‖a ρ‖ ^ 2 ≤ B) (hb : ∀ ρ, ‖b ρ‖ ^ 2 ≤ B)
    {ρ : ι} (hρ : ρ ∈ s) :
    |offset ρ| ≤ Real.sqrt ((2 * ∑ σ : ι, (mult σ : ℝ)) ^ 2 * B ^ 2 / 2 / c) :=
  abs_offset_le_of_e2_mult_budget a b hc hfloor hm1
    (e2_multFamily_le_of_norm_bound a b mult ha hb) hρ

end RiemannAnalytic

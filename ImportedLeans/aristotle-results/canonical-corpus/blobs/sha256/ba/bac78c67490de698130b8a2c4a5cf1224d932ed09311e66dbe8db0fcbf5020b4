/-
# Item (2) of the A1 source package: from a sign to a *uniform quantitative floor*

`SeagullSign` establishes the sign half of Row A1a: a Gram propagator, a
symmetric first variation and a negative semidefinite ("paramagnetic") second
variation make the one-loop coefficient nonnegative, and strictly positive as
soon as the bubble does not vanish.  `A1SourcePackage.paramagnetic_sign_not_uniform_floor`
shows that this is genuinely weaker than the Clay-facing datum

    β Z_j ≥ b_Z > 0    uniformly in the scale `j`.

This module closes the gap between the two *conditionally on a strictly weaker
and directly checkable source datum*: a single matrix entry of the literal
bubble kernel bounded away from zero, uniformly in the scale.

The mechanism is that the bubble is a Frobenius norm:

    Tr(G V G V) = Tr(MᵀM) = ∑_{a,b} M_{ab}²,     M = C V Cᵀ,   G = CᵀC,  Vᵀ = V,

so *every single entry* of `M` gives a quantitative lower bound, whereas the
sign argument only uses `M ≠ 0`.

* `trace_symm_mul_self_eq_sum_sq`, `bubble_eq_frobenius` — the identity.
* `betaTrace_ge_entry_sq` — `β ≥ ½ M_{ab}²` for a paramagnetic second variation.
* `brillouinSum_ge_entry_sq` — the same for the finite Brillouin sum, using one
  momentum only; the other momenta contribute nonnegatively.
* `uniformGaussianFloor_of_entryBound` — the uniform statement: a scale-indexed
  family of literal paramagnetic instances with one entry of the bubble kernel
  bounded below by `c > 0` uniformly in the scale has `β Z_j ≥ c²/2 > 0`
  uniformly, which is exactly the source datum `b_Z = c²/2`.
* `gaussianFloor_of_entryBound` — the same delivered in the field shape consumed
  by `A1LiteralSource`.
* `entryBound_nonvacuous` — the hypothesis is satisfiable.

This does **not** assert that the literal Bałaban bubble kernel has such a
uniformly nonvanishing entry; it replaces the abstract obligation "a uniform
floor `b_Z`" by the concrete one "one entry of `C V Cᵀ` is bounded away from `0`
uniformly in the scale", and supplies the constant `b_Z = c²/2` explicitly.
-/
import RequestProject.YangMills.A1SourcePackage

namespace YangMills

open Matrix Finset

variable {n : Type*} [Fintype n]

/-- For a symmetric matrix, `Tr(M·M)` is the sum of the squares of the entries. -/
theorem trace_symm_mul_self_eq_sum_sq (M : Matrix n n ℝ) (hM : Mᵀ = M) :
    (M * M).trace = ∑ a, ∑ b, (M a b) ^ 2 := by
  have hsymm : ∀ a b, M b a = M a b := by
    intro a b
    have := congrFun (congrFun hM a) b
    simpa [Matrix.transpose_apply] using this
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hsymm a b, sq]

/-- **The bubble is a Frobenius norm.**  For a Gram propagator `G = CᵀC` and a
symmetric first variation `V`, the bubble trace equals the sum of the squares of
the entries of the reduced kernel `M = C V Cᵀ`. -/
theorem bubble_eq_frobenius {G V C : Matrix n n ℝ} (hG : G = Cᵀ * C) (hV : Vᵀ = V) :
    (G * V * G * V).trace = ∑ a, ∑ b, ((C * V * Cᵀ) a b) ^ 2 := by
  have hMsymm : (C * V * Cᵀ)ᵀ = C * V * Cᵀ := by
    simp [Matrix.transpose_mul, hV, Matrix.mul_assoc]
  have h1 : G * V * G * V = Cᵀ * (C * V * Cᵀ * C * V) := by
    rw [hG]; simp [Matrix.mul_assoc]
  have h2 : (G * V * G * V).trace = ((C * V * Cᵀ) * (C * V * Cᵀ)).trace := by
    rw [h1, Matrix.trace_mul_comm]
    congr 1
    simp [Matrix.mul_assoc]
  rw [h2, trace_symm_mul_self_eq_sum_sq _ hMsymm]

/-- **A quantitative floor from a single entry.**  With a Gram propagator, a
symmetric first variation and a paramagnetic second variation, the one-loop
coefficient is at least half the square of *any* entry of the reduced bubble
kernel `M = C V Cᵀ`. -/
theorem betaTrace_ge_entry_sq {G V S C W : Matrix n n ℝ}
    (hG : G = Cᵀ * C) (hV : Vᵀ = V) (hS : S = -(Wᵀ * W)) (a b : n) :
    1 / 2 * ((C * V * Cᵀ) a b) ^ 2 ≤ betaTrace G V V S := by
  have hseag : (G * S).trace ≤ 0 := seagull_nonpos_of_negSemidef hG hS
  have hbub : (G * V * G * V).trace = ∑ x, ∑ y, ((C * V * Cᵀ) x y) ^ 2 :=
    bubble_eq_frobenius hG hV
  have hle : ((C * V * Cᵀ) a b) ^ 2 ≤ ∑ x, ∑ y, ((C * V * Cᵀ) x y) ^ 2 := by
    calc ((C * V * Cᵀ) a b) ^ 2 ≤ ∑ y, ((C * V * Cᵀ) a y) ^ 2 :=
          Finset.single_le_sum (f := fun y => ((C * V * Cᵀ) a y) ^ 2)
            (fun y _ => sq_nonneg _) (Finset.mem_univ b)
      _ ≤ ∑ x, ∑ y, ((C * V * Cᵀ) x y) ^ 2 :=
          Finset.single_le_sum (f := fun x => ∑ y, ((C * V * Cᵀ) x y) ^ 2)
            (fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _)) (Finset.mem_univ a)
  rw [betaTrace, hbub]
  linarith

/-- **The uniform Gaussian floor from a uniformly nonvanishing bubble entry.**
A scale-indexed family of literal paramagnetic instances whose reduced bubble
kernel has one entry of modulus at least `c` at every scale obeys
`β Z_j ≥ c²/2` uniformly in the scale. -/
theorem uniformGaussianFloor_of_entryBound
    {κ : ℕ → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C V S W : ∀ j, Matrix (κ j) (κ j) ℝ)
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    (a b : ∀ j, κ j) {c : ℝ} (hc : 0 ≤ c)
    (hentry : ∀ j, c ≤ |(C j * V j * (C j)ᵀ) (a j) (b j)|) (j : ℕ) :
    c ^ 2 / 2 ≤ betaTrace ((C j)ᵀ * C j) (V j) (V j) (S j) := by
  have hsq : c ^ 2 ≤ ((C j * V j * (C j)ᵀ) (a j) (b j)) ^ 2 := by
    have h := hentry j
    have habs : c ^ 2 ≤ |(C j * V j * (C j)ᵀ) (a j) (b j)| ^ 2 := by
      have h0 := abs_nonneg ((C j * V j * (C j)ᵀ) (a j) (b j))
      nlinarith
    rwa [sq_abs] at habs
  have hmain := betaTrace_ge_entry_sq (G := (C j)ᵀ * C j) (V := V j) (S := S j)
    (C := C j) (W := W j) rfl (hV j) (hS j) (a j) (b j)
  linarith

/-- **The floor in the shape consumed by `A1LiteralSource`.**  If the Gaussian
part of the shell coefficient at the reference history is the literal one-loop
coefficient of a paramagnetic instance at that scale, a uniformly nonvanishing
bubble entry supplies the field `gaussianFloor` with the explicit constant
`b_Z = c²/2 > 0`. -/
theorem gaussianFloor_of_entryBound
    {κ : ℕ → Type*} [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (C V S W : ∀ j, Matrix (κ j) (κ j) ℝ)
    (hV : ∀ j, (V j)ᵀ = V j) (hS : ∀ j, S j = -((W j)ᵀ * W j))
    (a b : ∀ j, κ j) {c : ℝ} (hc : 0 < c)
    (hentry : ∀ j, c ≤ |(C j * V j * (C j)ᵀ) (a j) (b j)|)
    (betaZ : ℕ → (ℕ → ℝ) → ℝ) (gref : ℕ → ℝ)
    (hident : ∀ j, betaZ j gref = betaTrace ((C j)ᵀ * C j) (V j) (V j) (S j)) :
    0 < c ^ 2 / 2 ∧ ∀ j, c ^ 2 / 2 ≤ betaZ j gref := by
  refine ⟨by positivity, fun j => ?_⟩
  rw [hident j]
  exact uniformGaussianFloor_of_entryBound C V S W hV hS a b (le_of_lt hc) hentry j

section Brillouin

variable {ι : Type*} [Fintype ι]
variable {κ : Type*} [Fintype κ]

/-- **The floor for the finite Brillouin sum.**  Only one momentum is used for
the lower bound; the paramagnetic sign makes all other momenta contribute
nonnegatively. -/
theorem brillouinSum_ge_entry_sq (g v s C W : ι → Matrix κ κ ℝ)
    (hg : ∀ q, g q = (C q)ᵀ * C q) (hv : ∀ q, (v q)ᵀ = v q)
    (hs : ∀ q, s q = -((W q)ᵀ * W q)) (q₀ : ι) (a b : κ) :
    1 / 2 * ((C q₀ * v q₀ * (C q₀)ᵀ) a b) ^ 2
      ≤ ∑ q, brillouinIntegrand (g q) (v q) (v q) (s q) := by
  have hterm : ∀ q ∈ (Finset.univ : Finset ι),
      0 ≤ brillouinIntegrand (g q) (v q) (v q) (s q) := by
    intro q _
    exact betaTrace_nonneg_of_seagull_nonpos (hg q) (hv q)
      (seagull_nonpos_of_negSemidef (hg q) (hs q))
  have hq₀ : 1 / 2 * ((C q₀ * v q₀ * (C q₀)ᵀ) a b) ^ 2
      ≤ brillouinIntegrand (g q₀) (v q₀) (v q₀) (s q₀) := by
    rw [brillouinIntegrand]
    exact betaTrace_ge_entry_sq (hg q₀) (hv q₀) (hs q₀) a b
  refine le_trans hq₀ ?_
  exact Finset.single_le_sum
    (f := fun q => brillouinIntegrand (g q) (v q) (v q) (s q)) hterm (Finset.mem_univ q₀)

end Brillouin

/-- **Non-vacuity.**  The entrywise hypothesis is satisfiable with a strictly
positive constant: the `1×1` instance with `C = V = 1` and `W = 0` has bubble
entry `1`, hence floor `1/2`. -/
theorem entryBound_nonvacuous :
    (1 : ℝ) ≤ |(((1 : Matrix (Fin 1) (Fin 1) ℝ) * 1 * (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ :
        Matrix (Fin 1) (Fin 1) ℝ)) 0 0|
      ∧ (1 : ℝ) ^ 2 / 2 ≤ betaTrace ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) 1 1
          (-((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 0)) := by
  constructor
  · simp
  · have := betaTrace_ge_entry_sq (G := (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)
      (V := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (S := -((0 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 0))
      (C := (1 : Matrix (Fin 1) (Fin 1) ℝ)) (W := 0) rfl (by simp) rfl 0 0
    simpa using this

end YangMills

/-
# Exact Schur / transverse geometry for multi-taper channels

Every literal channel of the two-radius balance is a *scalar* once a taper is fixed.
Running the same balance against a finite family of admissible tapers turns each
channel into a *vector* in `ι → ℝ`.  This module owns the finite-dimensional
geometry that is then used to remove selected nuisance directions **exactly**,
rather than majorizing them.

For a nuisance vector `n` and a channel vector `x`:

* `transverseComp n x = x - (⟪n,x⟫ / ‖n‖²) • n`  — the component of `x` orthogonal
  to `n`;
* `schur n x = ‖x‖² - ⟪n,x⟫² / ‖n‖²`             — the Schur complement of the
  `n`-block in the Gram matrix of `(n, x)`;
* `wedgeSq n x = ‖n‖²‖x‖² - ⟪n,x⟫²`              — the Gram determinant.

The three identities proved here are

    wedgeSq n x = ‖n‖² * ‖transverseComp n x‖²,
    schur n x   = ‖transverseComp n x‖²,
    transverseComp n (n + x) = transverseComp n x,

the last of which is the point of the whole construction: the nuisance energy
disappears *exactly*, with no triangle inequality and no tail estimate.  The
recursive two-nuisance version `elim2` removes two selected directions at once.

Nothing in this file is analytic; it is finite-dimensional linear algebra, kept
separate so that the literal modules can use it without circularity.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

noncomputable section

namespace Zeta23Bridge
namespace MultiTaperSchurCore

variable {ι : Type*} [Fintype ι]

/-! ## Inner product and norms of the coordinate space -/

/-- The Euclidean pairing of two channel vectors. -/
def dotP (n x : ι → ℝ) : ℝ := ∑ i, n i * x i

/-- The squared Euclidean norm of a channel vector. -/
def normSqP (x : ι → ℝ) : ℝ := dotP x x

theorem dotP_comm (n x : ι → ℝ) : dotP n x = dotP x n :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem dotP_add_right (n x y : ι → ℝ) : dotP n (x + y) = dotP n x + dotP n y := by
  unfold dotP
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_add]

theorem dotP_sub_right (n x y : ι → ℝ) : dotP n (x - y) = dotP n x - dotP n y := by
  unfold dotP
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [mul_sub]

theorem dotP_smul_right (n x : ι → ℝ) (c : ℝ) : dotP n (c • x) = c * dotP n x := by
  unfold dotP
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp [Pi.smul_apply]; ring

theorem normSqP_nonneg (x : ι → ℝ) : 0 ≤ normSqP x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem normSqP_eq_zero_iff (x : ι → ℝ) : normSqP x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i (_ : i ∈ Finset.univ) =>
      mul_self_nonneg (x i)).1 h
    have hi := mul_self_eq_zero.1 (hall i (Finset.mem_univ i))
    simpa using hi
  · rintro rfl; simp [normSqP, dotP]

theorem normSqP_pos_of_ne_zero {x : ι → ℝ} (hx : x ≠ 0) : 0 < normSqP x :=
  lt_of_le_of_ne (normSqP_nonneg x) (fun h => hx ((normSqP_eq_zero_iff x).1 h.symm))

/-- The expansion of the energy of `x - c • n`. -/
theorem normSqP_sub_smul (n x : ι → ℝ) (c : ℝ) :
    normSqP (x - c • n) = normSqP x - 2 * c * dotP n x + c ^ 2 * normSqP n := by
  unfold normSqP dotP
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The transverse component, the Schur complement and the Gram determinant -/

/-- `P_{n^⊥} x`: the component of `x` orthogonal to the nuisance direction `n`. -/
def transverseComp (n x : ι → ℝ) : ι → ℝ := x - (dotP n x / normSqP n) • n

/-- The Schur complement `‖x‖² - ⟪n,x⟫²/‖n‖²` of the nuisance block. -/
def schur (n x : ι → ℝ) : ℝ := normSqP x - dotP n x ^ 2 / normSqP n

/-- The Gram determinant `‖n‖²‖x‖² - ⟪n,x⟫²` of the pair `(n, x)`. -/
def wedgeSq (n x : ι → ℝ) : ℝ := normSqP n * normSqP x - dotP n x ^ 2

theorem wedgeSq_nonneg (n x : ι → ℝ) : 0 ≤ wedgeSq n x := by
  have hcs : (∑ i, n i * x i) ^ 2 ≤ (∑ i, n i ^ 2) * ∑ i, x i ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ n x
  have h1 : (∑ i, n i ^ 2) = normSqP n := by
    unfold normSqP dotP
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : (∑ i, x i ^ 2) = normSqP x := by
    unfold normSqP dotP
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : (∑ i, n i * x i) = dotP n x := rfl
  rw [h1, h2, h3] at hcs
  unfold wedgeSq
  linarith

/-- The transverse component is genuinely orthogonal to the nuisance direction. -/
theorem dotP_transverseComp (n x : ι → ℝ) : dotP n (transverseComp n x) = 0 := by
  unfold transverseComp
  rw [dotP_sub_right, dotP_smul_right]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dotP]
  · have hn' : normSqP n ≠ 0 := ne_of_gt (normSqP_pos_of_ne_zero hn)
    have hnn : dotP n n = normSqP n := rfl
    rw [hnn]
    field_simp
    ring

/-- `‖P_{n^⊥} x‖²` is exactly the Schur complement. -/
theorem normSqP_transverseComp {n : ι → ℝ} (hn : n ≠ 0) (x : ι → ℝ) :
    normSqP (transverseComp n x) = schur n x := by
  have hn' : normSqP n ≠ 0 := ne_of_gt (normSqP_pos_of_ne_zero hn)
  unfold transverseComp schur
  rw [normSqP_sub_smul]
  field_simp
  ring

/-- **The Gram determinant is the nuisance energy times the transverse energy.** -/
theorem wedgeSq_eq_normSqP_mul_transverse {n : ι → ℝ} (hn : n ≠ 0) (x : ι → ℝ) :
    wedgeSq n x = normSqP n * normSqP (transverseComp n x) := by
  have hn' : normSqP n ≠ 0 := ne_of_gt (normSqP_pos_of_ne_zero hn)
  rw [normSqP_transverseComp hn]
  unfold wedgeSq schur
  field_simp

/-! ## Exact elimination of a single nuisance direction -/

theorem transverseComp_add (n x y : ι → ℝ) :
    transverseComp n (x + y) = transverseComp n x + transverseComp n y := by
  unfold transverseComp
  rw [dotP_add_right]
  funext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, add_div]
  ring

theorem transverseComp_self {n : ι → ℝ} (hn : n ≠ 0) : transverseComp n n = 0 := by
  have hn' : normSqP n ≠ 0 := ne_of_gt (normSqP_pos_of_ne_zero hn)
  unfold transverseComp
  have hone : dotP n n / normSqP n = 1 := by
    have hnn : dotP n n = normSqP n := rfl
    rw [hnn]
    field_simp
  rw [hone]
  simp

/-- **Nuisance energy disappears exactly:** `P_{n^⊥}(n + x) = P_{n^⊥} x`. -/
theorem transverseComp_add_self_left {n : ι → ℝ} (hn : n ≠ 0) (x : ι → ℝ) :
    transverseComp n (n + x) = transverseComp n x := by
  rw [transverseComp_add, transverseComp_self hn, zero_add]

/-- A strictly positive Gram determinant certifies that the target survives the
projection. -/
theorem transverseComp_ne_zero_of_wedgeSq_pos {n x : ι → ℝ} (h : 0 < wedgeSq n x) :
    transverseComp n x ≠ 0 := by
  intro hzero
  have hn : n ≠ 0 := by
    rintro rfl
    unfold wedgeSq normSqP dotP at h
    simp at h
  rw [wedgeSq_eq_normSqP_mul_transverse hn, hzero] at h
  simp [normSqP, dotP] at h

/-! ## Exact elimination of two nuisance directions -/

/-- The second nuisance direction, after the first has been removed. -/
def perp2 (n₁ n₂ : ι → ℝ) : ι → ℝ := transverseComp n₁ n₂

/-- The two-nuisance elimination operator `E_{n₁,n₂}`. -/
def elim2 (n₁ n₂ x : ι → ℝ) : ι → ℝ :=
  transverseComp (perp2 n₁ n₂) (transverseComp n₁ x)

theorem elim2_add (n₁ n₂ x y : ι → ℝ) :
    elim2 n₁ n₂ (x + y) = elim2 n₁ n₂ x + elim2 n₁ n₂ y := by
  unfold elim2
  rw [transverseComp_add, transverseComp_add]

/-- **Recursive exact elimination:** the two selected nuisance directions vanish
identically from the residual. -/
theorem elim2_add_nuisance {n₁ n₂ : ι → ℝ} (h₁ : n₁ ≠ 0) (h₂ : perp2 n₁ n₂ ≠ 0) (x : ι → ℝ) :
    elim2 n₁ n₂ (n₁ + n₂ + x) = elim2 n₁ n₂ x := by
  unfold elim2
  rw [transverseComp_add (n := n₁) (x := n₁ + n₂) (y := x), transverseComp_add (n := n₁),
    transverseComp_self h₁, zero_add]
  rw [show transverseComp n₁ n₂ = perp2 n₁ n₂ from rfl]
  rw [transverseComp_add, transverseComp_self h₂, zero_add]

end MultiTaperSchurCore
end Zeta23Bridge

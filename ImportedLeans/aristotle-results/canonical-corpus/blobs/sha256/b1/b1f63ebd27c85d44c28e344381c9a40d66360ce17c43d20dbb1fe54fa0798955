import Spine.Observer

/-!
# The transverse Gram core, owned once

Several lanes of this corpus use the same two-vector nondegeneracy measure under
different names: the squared area `‖a‖²‖b‖² − ⟪a,b⟫²` swept by a distinguished
direction `a` and a transverse direction `b`.  `Spine.area2` is that measure.
This file collects the domain-neutral theory of it in one place, so that a lane
which needs "the transverse defect is nonnegative, vanishes exactly on collinear
pairs, equals the squared distance to the line through `a` (up to the scale
`‖a‖²`), expands as a sum of two-by-two minors, and is coercive unless the pair
is nearly aligned" can quote theorems instead of redeveloping them.

Contents (all for an arbitrary real inner product space, and the coordinate
expansion for `EuclideanSpace ℝ (Fin n)` in any dimension):

* `area2_nonneg`, `area2_self`, `area2_comm` — basic properties;
* `transverseResidual a b = ‖a‖² • b − ⟪a,b⟫ • a` — the component of `b`
  transverse to `a`, rescaled to avoid dividing;
* `inner_transverseResidual` — it is orthogonal to `a`;
* `norm_sq_transverseResidual` — **the projection identity**
  `‖‖a‖²b − ⟪a,b⟫a‖² = ‖a‖² · area2 a b`;
* `area2_eq_zero_iff` — `area2 a b = 0 ↔ b` lies on the line through `a`
  (for `a ≠ 0`), and `area2_pos_iff` its positive form;
* `area2_lagrange` — **Lagrange's identity**: twice the defect is the sum of the
  squares of all two-by-two minors `aᵢbⱼ − aⱼbᵢ`;
* `area2_dichotomy` — the coercive-or-nearly-aligned dichotomy: for every
  threshold `ε`, either the defect is at least `ε`, or the transverse residual
  is strictly smaller than `‖a‖²ε`.

Nothing here refers to any application domain; the theorems are about vectors.
-/

open RealInnerProductSpace

namespace Spine
namespace TransverseGram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! ## Basic properties of the transverse defect -/

theorem area2_comm (a b : V) : area2 a b = area2 b a := by
  simp [area2, real_inner_comm a b]; ring

@[simp] theorem area2_self (a : V) : area2 a a = 0 := by
  simp only [area2, real_inner_self_eq_norm_sq]
  ring

@[simp] theorem area2_zero_left (b : V) : area2 0 b = 0 := by simp [area2]

@[simp] theorem area2_zero_right (a : V) : area2 a 0 = 0 := by simp [area2]

/-- **The defect is nonnegative** — Cauchy–Schwarz. -/
theorem area2_nonneg (a b : V) : 0 ≤ area2 a b := by
  have h := real_inner_mul_inner_self_le a b
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  simp only [area2, sub_nonneg, sq]
  linarith

/-! ## The projection identity -/

/-- The part of `b` transverse to `a`, scaled by `‖a‖²` so that no division is
needed. -/
noncomputable def transverseResidual (a b : V) : V := (‖a‖ ^ 2) • b - ⟪a, b⟫ • a

/-- The transverse residual is orthogonal to the distinguished direction. -/
theorem inner_transverseResidual (a b : V) : ⟪a, transverseResidual a b⟫ = 0 := by
  simp [transverseResidual, inner_sub_right, real_inner_smul_right]
  ring

/-- **The projection identity.**  The squared length of the transverse residual
is `‖a‖²` times the transverse defect. -/
theorem norm_sq_transverseResidual (a b : V) :
    ‖transverseResidual a b‖ ^ 2 = ‖a‖ ^ 2 * area2 a b := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [transverseResidual, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right]
  simp only [real_inner_self_eq_norm_sq, area2, real_inner_comm b a]
  ring

/-! ## The degeneracy dichotomy -/

/-- **The defect vanishes exactly on collinear pairs.** -/
theorem area2_eq_zero_iff {a : V} (ha : a ≠ 0) (b : V) :
    area2 a b = 0 ↔ ∃ r : ℝ, b = r • a := by
  have hna : (0 : ℝ) < ‖a‖ ^ 2 := by positivity
  constructor
  · intro h
    have h0 : ‖transverseResidual a b‖ ^ 2 = 0 := by
      rw [norm_sq_transverseResidual, h, mul_zero]
    have hz : transverseResidual a b = 0 := by
      have : ‖transverseResidual a b‖ = 0 := by
        have := sq_eq_zero_iff.mp h0
        exact this
      exact norm_eq_zero.mp this
    refine ⟨⟪a, b⟫ / ‖a‖ ^ 2, ?_⟩
    have h2 : (‖a‖ ^ 2) • b = ⟪a, b⟫ • a := sub_eq_zero.mp hz
    calc b = (‖a‖ ^ 2)⁻¹ • ((‖a‖ ^ 2) • b) := by
            rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hna), one_smul]
      _ = (‖a‖ ^ 2)⁻¹ • (⟪a, b⟫ • a) := by rw [h2]
      _ = (⟪a, b⟫ / ‖a‖ ^ 2) • a := by rw [smul_smul, div_eq_inv_mul]
  · rintro ⟨r, rfl⟩
    simp only [area2, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_self_eq_norm_sq]
    ring

/-- The positive form: the defect is strictly positive exactly when the two
directions are genuinely independent. -/
theorem area2_pos_iff {a : V} (ha : a ≠ 0) (b : V) :
    0 < area2 a b ↔ ∀ r : ℝ, b ≠ r • a := by
  constructor
  · intro h r hr
    exact absurd ((area2_eq_zero_iff ha b).mpr ⟨r, hr⟩) (ne_of_gt h)
  · intro h
    rcases lt_or_eq_of_le (area2_nonneg a b) with hlt | heq
    · exact hlt
    · obtain ⟨r, hr⟩ := (area2_eq_zero_iff ha b).mp heq.symm
      exact absurd hr (h r)

/-- **The coercive-or-nearly-aligned dichotomy.**  For every threshold, either
the transverse defect is at least that large, or the transverse residual is
strictly shorter than the corresponding scale. -/
theorem area2_dichotomy {a : V} (ha : a ≠ 0) (b : V) (ε : ℝ) :
    ε ≤ area2 a b ∨ ‖transverseResidual a b‖ ^ 2 < ‖a‖ ^ 2 * ε := by
  have hna : (0 : ℝ) < ‖a‖ ^ 2 := by positivity
  rcases le_or_gt ε (area2 a b) with h | h
  · exact Or.inl h
  · exact Or.inr (by rw [norm_sq_transverseResidual]; exact mul_lt_mul_of_pos_left h hna)

/-! ## Lagrange's identity -/

/-- **Lagrange's identity in any dimension.**  Twice the transverse defect is the
sum of the squares of all two-by-two minors of the pair. -/
theorem area2_lagrange {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    2 * area2 a b = ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
  have hinner : ∀ x y : EuclideanSpace ℝ (Fin n), ⟪x, y⟫ = ∑ i, x i * y i := by
    intro x y; simp [PiLp.inner_apply, mul_comm]
  have hna : ‖a‖ ^ 2 = ∑ i, a i * a i := by rw [← real_inner_self_eq_norm_sq, hinner]
  have hnb : ‖b‖ ^ 2 = ∑ i, b i * b i := by rw [← real_inner_self_eq_norm_sq, hinner]
  have key : ∑ x, ∑ y, 2 * (a x * b y) * (a y * b x) = 2 * (∑ i, a i * b i) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [area2]
  rw [hna, hnb, hinner]
  simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, mul_pow]
  rw [key]
  ring_nf

/-- Consequently the defect is a sum of squares, which re-proves nonnegativity in
coordinates. -/
theorem area2_nonneg_of_lagrange {n : ℕ} (a b : EuclideanSpace ℝ (Fin n)) :
    0 ≤ ∑ i, ∑ j, (a i * b j - a j * b i) ^ 2 := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end TransverseGram
end Spine

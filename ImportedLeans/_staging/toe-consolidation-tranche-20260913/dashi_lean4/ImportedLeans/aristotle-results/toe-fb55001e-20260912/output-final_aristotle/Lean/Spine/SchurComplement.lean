import Spine.TransverseGram

/-!
# Eliminating a hidden direction: the Schur complement, owned once

The corpus repeatedly performs the same operation at the level of quadratic
forms: a state splits into a *hidden* (auxiliary, eliminated, gauge) direction
and a *visible* block, and one asks what quadratic form the visible block
carries once the hidden direction has been optimised away.  That effective form
is the Schur complement.

This file owns the domain-neutral, rank-one-hidden-block version of that
operation.  Fix a real inner product space `V` of visible states, a hidden
coefficient `a > 0`, a coupling vector `b : V`, and a visible form `d : V → ℝ`.
The coupled form is

```
coupled a b d x y = a x² + 2 x ⟪b, y⟫ + d y     (x : ℝ hidden, y : V visible)
```

and its Schur complement is

```
schur a b d y = d y − ⟪b, y⟫² / a .
```

Contents:

* `coupled_ge_schur`, `coupled_hiddenMin`, `schur_isLeast`, `schur_eq_iInf` —
  the Schur complement **is** the minimum of the coupled form over the hidden
  variable, attained at `x = −⟪b,y⟫/a`;
* `schur_coercive` — the quantitative transfer: if the visible block is bounded
  below by `δ` and the coupling term above by `η`, the effective form is bounded
  below by `δ − η`;
* `schur_norm_sq`, `coupled_norm_sq` — the geometric instance: eliminating the
  `u`-direction from `‖x • u + y‖²` leaves exactly `area2 u y / ‖u‖²`, so the
  transverse Gram defect of `Spine.TransverseGram` *is* a Schur complement;
* `schur_pos_iff_area2_pos` — hence the effective form is positive on `y`
  exactly when the transverse defect is.

Nothing here mentions an application domain: these are statements about a real
inner product space and a scalar hidden variable.
-/

open RealInnerProductSpace

namespace Spine
namespace SchurComplement

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coupled quadratic form on `hidden × visible`. -/
noncomputable def coupled (a : ℝ) (b : V) (d : V → ℝ) (x : ℝ) (y : V) : ℝ :=
  a * x ^ 2 + 2 * x * ⟪b, y⟫ + d y

/-- The Schur complement: the visible form corrected by the coupling. -/
noncomputable def schur (a : ℝ) (b : V) (d : V → ℝ) (y : V) : ℝ :=
  d y - ⟪b, y⟫ ^ 2 / a

/-- The hidden value at which the coupled form is minimised. -/
noncomputable def hiddenMin (a : ℝ) (b : V) (y : V) : ℝ := -(⟪b, y⟫ / a)

/-- Completing the square: the coupled form is the Schur complement plus a
nonnegative multiple of the squared deviation from the optimal hidden value. -/
theorem coupled_eq_schur_add (a : ℝ) (b : V) (d : V → ℝ) (ha : a ≠ 0) (x : ℝ) (y : V) :
    coupled a b d x y = schur a b d y + a * (x - hiddenMin a b y) ^ 2 := by
  unfold coupled schur hiddenMin
  field_simp
  ring

/-- The Schur complement is a lower bound for the coupled form. -/
theorem coupled_ge_schur {a : ℝ} (ha : 0 < a) (b : V) (d : V → ℝ) (x : ℝ) (y : V) :
    schur a b d y ≤ coupled a b d x y := by
  rw [coupled_eq_schur_add a b d (ne_of_gt ha) x y]
  have : 0 ≤ a * (x - hiddenMin a b y) ^ 2 :=
    mul_nonneg ha.le (sq_nonneg _)
  linarith

/-- The lower bound is attained at `hiddenMin`. -/
theorem coupled_hiddenMin {a : ℝ} (ha : a ≠ 0) (b : V) (d : V → ℝ) (y : V) :
    coupled a b d (hiddenMin a b y) y = schur a b d y := by
  rw [coupled_eq_schur_add a b d ha (hiddenMin a b y) y]
  simp

/-- **The Schur complement is the minimum of the coupled form over the hidden
variable.** -/
theorem schur_isLeast {a : ℝ} (ha : 0 < a) (b : V) (d : V → ℝ) (y : V) :
    IsLeast {r : ℝ | ∃ x : ℝ, coupled a b d x y = r} (schur a b d y) :=
  ⟨⟨hiddenMin a b y, coupled_hiddenMin (ne_of_gt ha) b d y⟩,
    by rintro r ⟨x, rfl⟩; exact coupled_ge_schur ha b d x y⟩

/-- The infimum form of the same statement. -/
theorem schur_eq_iInf {a : ℝ} (ha : 0 < a) (b : V) (d : V → ℝ) (y : V) :
    schur a b d y = ⨅ x : ℝ, coupled a b d x y := by
  refine le_antisymm (le_ciInf fun x => coupled_ge_schur ha b d x y) ?_
  refine ciInf_le_of_le ⟨schur a b d y, ?_⟩ (hiddenMin a b y) ?_
  · rintro r ⟨x, rfl⟩; exact coupled_ge_schur ha b d x y
  · exact le_of_eq (coupled_hiddenMin (ne_of_gt ha) b d y)

/-- **Quantitative coercivity transfer.**  If the visible block is bounded below
by `δ‖y‖²` and the eliminated coupling costs at most `η‖y‖²`, the effective form
is bounded below by `(δ − η)‖y‖²`. -/
theorem schur_coercive {a δ η : ℝ} (b : V) (d : V → ℝ) (y : V)
    (hd : δ * ‖y‖ ^ 2 ≤ d y) (hc : ⟪b, y⟫ ^ 2 / a ≤ η * ‖y‖ ^ 2) :
    (δ - η) * ‖y‖ ^ 2 ≤ schur a b d y := by
  unfold schur
  nlinarith [hd, hc]

section Geometric

variable (u y : V)

/-- The squared norm of a hidden multiple of `u` added to a visible `y` is a
coupled form with `a = ‖u‖²`, `b = u`, `d = ‖·‖²`. -/
theorem coupled_norm_sq (x : ℝ) :
    ‖x • u + y‖ ^ 2 = coupled (‖u‖ ^ 2) u (fun v => ‖v‖ ^ 2) x y := by
  show ‖x • u + y‖ ^ 2 = ‖u‖ ^ 2 * x ^ 2 + 2 * x * ⟪u, y⟫ + ‖y‖ ^ 2
  rw [norm_add_sq_real, real_inner_smul_left, norm_smul]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- **The transverse Gram defect is a Schur complement.**  Eliminating the
`u`-direction from `‖x • u + y‖²` leaves exactly `area2 u y / ‖u‖²`. -/
theorem schur_norm_sq (hu : u ≠ 0) :
    schur (‖u‖ ^ 2) u (fun v => ‖v‖ ^ 2) y = area2 u y / ‖u‖ ^ 2 := by
  have hu2 : (‖u‖ : ℝ) ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hu)
  unfold schur area2
  field_simp

/-- Hence the effective visible form is positive exactly where the transverse
defect is: hidden-variable elimination and transverse nondegeneracy are the same
condition. -/
theorem schur_pos_iff_area2_pos (hu : u ≠ 0) :
    0 < schur (‖u‖ ^ 2) u (fun v => ‖v‖ ^ 2) y ↔ 0 < area2 u y := by
  have hu2 : (0 : ℝ) < ‖u‖ ^ 2 := by
    have : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu
    positivity
  rw [schur_norm_sq u y hu, div_pos_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact h
    · exact absurd hu2 (not_lt.mpr h.le)
  · intro h; exact Or.inl ⟨h, hu2⟩

end Geometric

end SchurComplement
end Spine

/-
# Row A1a — the near/far split of the Brillouin cell, pointwise estimates

Two pointwise estimates for one-loop orbit densities `N(p) / p̂²`:

* **far region** (some axis leaves the box of radius `r = 2/5`): the literal
  denominator is floored by `64/25`, so any numerator sup `S` gives the quotient
  bound `25 S / 64`;

* **near region** (all axes inside the box): there is no denominator floor, so
  the transversality zero of the numerator must be cancelled against the zero of
  the denominator *before* taking absolute values.  Two forms are proved: the
  general Ward-compensated quotient bound `|h Ñ| / D ≤ m / c` under
  `c h ≤ D`, and the concrete consequence of the Ward-compensated quartic bound
  `|N(p)| ≤ A (p̂²)²`.

All quotients are the honest Lean division; the degenerate point `p̂² = 0`
(where Lean's division returns `0`) is covered by the statements as written.
-/
import RequestProject.YangMills.LatticeMomentum

namespace YangMills

open Real Finset

/-! ## 1. The regions -/

/-- The Brillouin zone in the fixed normalisation. -/
def InBZ (p : Fin 4 → ℝ) : Prop := ∀ μ, |p μ| ≤ 1 / 2

/-- The near box of radius `r`: every axis satisfies `|p μ| ≤ r`. -/
def NearBox (r : ℝ) (p : Fin 4 → ℝ) : Prop := ∀ μ, |p μ| ≤ r

/-- The far region at radius `r`: some axis leaves the box. -/
def FarRegion (r : ℝ) (p : Fin 4 → ℝ) : Prop := ∃ μ, r ≤ |p μ|

/-- **Constructive far-axis selection.**  A Brillouin point that is not in the
near box names an axis that is beyond the radius. -/
theorem farAxis_of_not_nearBox {r : ℝ} {p : Fin 4 → ℝ} (h : ¬ NearBox r p) :
    ∃ μ, r < |p μ| := by
  unfold NearBox at h
  push_neg at h
  exact h

/-- The two regions exhaust the Brillouin zone. -/
theorem nearBox_or_farRegion (r : ℝ) (p : Fin 4 → ℝ) :
    NearBox r p ∨ FarRegion r p := by
  by_cases h : NearBox r p
  · exact Or.inl h
  · obtain ⟨μ, hμ⟩ := farAxis_of_not_nearBox h
    exact Or.inr ⟨μ, hμ.le⟩

/-! ## 2. Far region: the literal denominator floor -/

/-- **Far denominator floor.**  If some axis of a Brillouin point is at least
`2/5` away from the origin then the literal inverse propagator is bounded below
by `64/25`. -/
theorem phatSq_floor_far {p : Fin 4 → ℝ} (hBZ : InBZ p) (hfar : FarRegion (2/5) p) :
    (64 : ℝ) / 25 ≤ phatSq p := by
  obtain ⟨μ, hμ⟩ := hfar
  exact le_trans (phat_sq_ge_of_far hμ (hBZ μ)) (phat_sq_le_phatSq p μ)

/-- The same statement with the (weaker) `87/128` sine-gap constant used by the
shell budget: `4 (87/128)² = 7569/4096`. -/
theorem phatSq_floor_far_87_128 {p : Fin 4 → ℝ} (hBZ : InBZ p)
    (hfar : FarRegion (2/5) p) : (7569 : ℝ) / 4096 ≤ phatSq p :=
  le_trans (by norm_num) (phatSq_floor_far hBZ hfar)

/-- **Far quotient bound.**  With numerator sup `S` on the far region, the
literal orbit density is bounded by `25 S / 64`. -/
theorem far_quotient_bound {p : Fin 4 → ℝ} {N S : ℝ} (hBZ : InBZ p)
    (hfar : FarRegion (2/5) p) (hN : |N| ≤ S) :
    |N / phatSq p| ≤ 25 * S / 64 := by
  have hfloor : (64 : ℝ) / 25 ≤ phatSq p := phatSq_floor_far hBZ hfar
  have hpos : (0:ℝ) < phatSq p := by linarith
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  have hS : 0 ≤ S := le_trans (abs_nonneg N) hN
  nlinarith [hN, hfloor, hS]

/-- The unit-numerator far bound actually used downstream: with `S = 1` the
density is at most `25/64` (sharper than the `4096/7569` recorded earlier). -/
theorem far_quotient_bound_unit {p : Fin 4 → ℝ} {N : ℝ} (hBZ : InBZ p)
    (hfar : FarRegion (2/5) p) (hN : |N| ≤ 1) :
    |N / phatSq p| ≤ 25 / 64 := by
  simpa using far_quotient_bound hBZ hfar hN

/-! ## 3. Near region: cancellation before absolute values -/

/-- **Ward-compensated near quotient.**  If the numerator factors as `N = h Ñ`
with `h ≥ 0` comparable to the denominator, `c h ≤ D`, and the cofactor is
bounded, `|Ñ| ≤ m`, then the quotient is bounded by `m / c` with *no*
denominator floor.  The cancellation is performed before the absolute value. -/
theorem ward_compensated_near_quotient {h cof D c m : ℝ} (hc : 0 < c)
    (hh : 0 ≤ h) (hcomp : c * h ≤ D) (hcof : |cof| ≤ m) (hD : 0 < D) :
    |h * cof / D| ≤ m / c := by
  have hquot : h / D ≤ 1 / c := by
    rw [div_le_div_iff₀ hD hc]
    linarith
  have hm : 0 ≤ m := le_trans (abs_nonneg cof) hcof
  rw [abs_div, abs_of_pos hD, abs_mul, abs_of_nonneg hh, div_le_div_iff₀ hD hc]
  have hhD : h * c ≤ D := by linarith
  nlinarith [abs_nonneg cof, hcof, hm, hh, hD.le, hc.le]

/-- **Near quotient from the Ward-compensated quartic bound.**  If the joint
numerator obeys `|N(p)| ≤ A (p̂²)²` — the shape forced by transversality, the
regular remainder vanishing to second order in `p̂²` — then the orbit density is
bounded by `A p̂²`, hence by `16 A` on the whole Brillouin zone. -/
theorem near_quotient_of_quartic_bound {p : Fin 4 → ℝ} {N A : ℝ}
    (hN : |N| ≤ A * (phatSq p) ^ 2) : |N / phatSq p| ≤ A * phatSq p := by
  rcases eq_or_lt_of_le (phatSq_nonneg p) with hz | hpos
  · have hz0 : phatSq p = 0 := hz.symm
    simp [hz0]
  · rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    nlinarith [hN, hpos]

/-- **Boundary witness for the near criterion.**  The near criterion
`m / c ≤ 2/5` is exactly boundary-tight: there is admissible data attaining
`|h Ñ / D| = m / c = 2/5`, so `2/5` cannot be lowered without further input. -/
theorem near_quotient_boundary_sharp :
    ∃ h cof D c m : ℝ, 0 < c ∧ 0 ≤ h ∧ c * h ≤ D ∧ |cof| ≤ m ∧ 0 < D ∧
      |h * cof / D| = 2 / 5 ∧ m / c = 2 / 5 :=
  ⟨1, 2 / 5, 1, 1, 2 / 5, by norm_num, by norm_num, by norm_num,
    by rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2 / 5)], by norm_num,
    by norm_num [abs_of_nonneg], by norm_num⟩

/-- Uniform form on the Brillouin cell: the quartic constant `A ≤ 1/40`
delivers exactly the near per-orbit bound `2/5` demanded by the shell budget. -/
theorem near_quotient_bound_two_fifths {p : Fin 4 → ℝ} {N A : ℝ} (hA : 0 ≤ A)
    (hA' : A ≤ 1 / 40) (hN : |N| ≤ A * (phatSq p) ^ 2) :
    |N / phatSq p| ≤ 2 / 5 := by
  have h1 : |N / phatSq p| ≤ A * phatSq p := near_quotient_of_quartic_bound hN
  have h2 : phatSq p ≤ 16 := phatSq_le_sixteen p
  nlinarith [phatSq_nonneg p]

end YangMills

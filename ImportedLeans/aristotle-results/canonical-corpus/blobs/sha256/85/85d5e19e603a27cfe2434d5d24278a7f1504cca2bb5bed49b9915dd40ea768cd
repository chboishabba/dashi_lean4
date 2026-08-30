/-
# Which operator does a carrier actually admit?

"The X of Y" is legitimate only when `Y`'s data is exhibited as an instance of
the structure that theorem `X` is about, with the hypotheses checked.  This
module settles that question for two candidate operators on an amounts carrier —
one *positively* and one *negatively*.

**Negative: there is no Hamiltonian on an odd-dimensional carrier.**  A
Hamiltonian needs a phase space: a nondegenerate alternating form.  Over `ℝ`
every alternating form on an odd-dimensional space is degenerate
(`Spine.Duality.odd_alternating_form_degenerate`), so on the five-dimensional
taste carrier of `Cuisine.SensoryCore` no symplectic structure exists at all
(`Spine.Duality.taste_carrier_no_symplectic_form`).  "The Hamiltonian of
cinnamon in a dish's taste" is therefore not merely unproved on this carrier: the
structure the phrase names provably is not there.

**Positive: convex duality is available, and is the honest operator.**  The
Legendre–Fenchel conjugate of an acceptability functional over ingredient
amounts is defined here, with Fenchel–Young
(`Spine.Duality.fenchel_young`) and — the substantive part — the marginal-rate
reading: at an interior optimum the dual coordinate *is* the derivative of the
acceptability functional (`Spine.Duality.dual_eq_deriv`).  That is what makes
"how much cinnamon is one unit of sugar worth here" a theorem rather than a
metaphor.

**The nondegeneracy gate applies here too.**  A flat acceptability functional
has no finite conjugate in any nonzero direction
(`Spine.Duality.flat_not_bddAbove`): constant preference yields no trade-off
information, exactly as a constant channel yields no transverse area.
-/
import Mathlib
import Spine.Observer

open RealInnerProductSpace Matrix

namespace Spine
namespace Duality

/-! ## The negative: no symplectic structure in odd dimension -/

/-- Over `ℝ`, an alternating (skew) matrix of odd size is singular. -/
theorem odd_skew_det_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Odd (Fintype.card ι)) (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) : A.det = 0 := by
  have h1 : A.det = (-1 : ℝ) ^ Fintype.card ι * A.det := by
    conv_lhs => rw [← Matrix.det_transpose A]
    rw [hA, Matrix.det_neg]
  rw [hn.neg_one_pow] at h1
  linarith

/-- **No phase space in odd dimension.**  Every alternating bilinear form on an
odd-dimensional real coordinate space is degenerate: some nonzero vector is
annihilated by it. -/
theorem odd_alternating_form_degenerate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : Odd (Fintype.card ι)) (A : Matrix ι ι ℝ) (hA : Aᵀ = -A) :
    ∃ v : ι → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  obtain ⟨v, hv, hAv⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr (odd_skew_det_zero hn A hA)
  exact ⟨v, hv, hAv⟩

/-- **The taste carrier admits no symplectic form.**  The sensory carrier of
`Cuisine.SensoryCore` has five taste dimensions, and five is odd, so every
alternating form on it is degenerate.  There is no phase space here, hence no
Hamiltonian; the honest operator on this carrier is the Legendre transform
below. -/
theorem card_tasteDimension : Fintype.card Cuisine.SensoryCore.TasteDimension = 5 := by decide

theorem taste_carrier_no_symplectic_form
    (A : Matrix Cuisine.SensoryCore.TasteDimension Cuisine.SensoryCore.TasteDimension ℝ)
    (hA : Aᵀ = -A) :
    ∃ v : Cuisine.SensoryCore.TasteDimension → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 :=
  odd_alternating_form_degenerate (by rw [card_tasteDimension]; decide) A hA

/-! ## The positive: the Legendre–Fenchel conjugate -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The set of values whose supremum defines the conjugate: here `y` is a vector
of marginal rates and `x` a vector of amounts. -/
def valueSet (f : E → ℝ) (y : E) : Set ℝ := {r | ∃ x, r = ⟪y, x⟫ - f x}

theorem valueSet_nonempty (f : E → ℝ) (y : E) : (valueSet f y).Nonempty := ⟨_, 0, rfl⟩

/-- The Legendre–Fenchel conjugate of an acceptability functional. -/
noncomputable def conjugate (f : E → ℝ) (y : E) : ℝ := sSup (valueSet f y)

theorem le_conjugate {f : E → ℝ} {y : E} (h : BddAbove (valueSet f y)) (x : E) :
    ⟪y, x⟫ - f x ≤ conjugate f y :=
  le_csSup h ⟨x, rfl⟩

/-- **Fenchel–Young.**  Whenever the conjugate is finite, amounts and marginal
rates pair below the sum of the functional and its dual. -/
theorem fenchel_young {f : E → ℝ} {y : E} (h : BddAbove (valueSet f y)) (x : E) :
    ⟪y, x⟫ ≤ f x + conjugate f y := by
  have := le_conjugate h x
  linarith

/-- **The nondegeneracy gate for duality.**  A flat acceptability functional has
no finite conjugate in any nonzero direction: constant preference carries no
trade-off information at all. -/
theorem flat_not_bddAbove {c : ℝ} {y : E} (hy : y ≠ 0) :
    ¬ BddAbove (valueSet (fun _ : E => c) y) := by
  rintro ⟨B, hB⟩
  have hy2 : 0 < ⟪y, y⟫ := real_inner_self_pos.mpr hy
  set t : ℝ := (B + c + 1) / ⟪y, y⟫ with ht
  have hmem : ⟪y, t • y⟫ - c ∈ valueSet (fun _ : E => c) y := ⟨t • y, rfl⟩
  have hle := hB hmem
  rw [real_inner_smul_right, ht, div_mul_cancel₀ _ (ne_of_gt hy2)] at hle
  linarith

/-- **The dual coordinate is the marginal rate.**  If the acceptability
functional `f` is differentiable at `x₀` and the Fenchel objective
`x ↦ ⟪y, x⟫ − f x` has a local maximum there, then `y` *is* the derivative of
`f` at `x₀`: for every direction `v`, `f' v = ⟪y, v⟫`.  This is the theorem that
licenses reading dual coordinates as "how much of one ingredient another is
worth here". -/
theorem dual_eq_deriv {f : E → ℝ} {y x₀ : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x₀)
    (hmax : IsLocalMax (fun x => ⟪y, x⟫ - f x) x₀) :
    ∀ v, f' v = ⟪y, v⟫ := by
  have h1 : HasFDerivAt (fun x : E => ⟪y, x⟫) (innerSL ℝ y) x₀ :=
    (innerSL ℝ y).hasFDerivAt
  have hg : HasFDerivAt (fun x : E => ⟪y, x⟫ - f x) (innerSL ℝ y - f') x₀ := h1.sub hf
  have hzero := hmax.hasFDerivAt_eq_zero hg
  intro v
  have := congrArg (fun L : E →L[ℝ] ℝ => L v) hzero
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    innerSL_apply_apply] at this
  linarith [this]

/-- **"How much cinnamon is one unit of sugar worth here."**  At an interior
optimum the trade-off rate between two ingredient directions is the ratio of the
dual coordinates, and it equals the ratio of the acceptability functional's
directional derivatives.  This is the exact sense in which the phrase is a
theorem rather than a metaphor: the carrier is the amounts space, the structure
is convex duality, the map is the acceptability functional, and the hypothesis
verified is differentiability at an optimum. -/
theorem tradeoff_rate {f : E → ℝ} {y x₀ : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x₀) (hmax : IsLocalMax (fun x => ⟪y, x⟫ - f x) x₀)
    (u v : E) :
    f' u / f' v = ⟪y, u⟫ / ⟪y, v⟫ := by
  rw [dual_eq_deriv hf hmax u, dual_eq_deriv hf hmax v]

/-- The converse reading: if `y` is the derivative of `f` at `x₀` and the
objective attains a *global* maximum there, the conjugate is computed exactly by
that optimum. -/
theorem conjugate_eq_of_isMaxOn {f : E → ℝ} {y x₀ : E}
    (hmax : ∀ x, ⟪y, x⟫ - f x ≤ ⟪y, x₀⟫ - f x₀) :
    conjugate f y = ⟪y, x₀⟫ - f x₀ := by
  have hbdd : BddAbove (valueSet f y) :=
    ⟨⟪y, x₀⟫ - f x₀, by rintro r ⟨x, rfl⟩; exact hmax x⟩
  refine le_antisymm (csSup_le (valueSet_nonempty f y) ?_) (le_csSup hbdd ⟨x₀, rfl⟩)
  rintro r ⟨x, rfl⟩
  exact hmax x

end Duality
end Spine

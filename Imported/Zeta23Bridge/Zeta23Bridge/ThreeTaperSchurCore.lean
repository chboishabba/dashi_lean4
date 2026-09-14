/-
# Exact elimination of *two* nuisance directions in the three-taper channel

`MultiTaperSchurCore` owns the one-nuisance geometry and the recursive operator

    elim2 n₁ n₂ x = P_{(P_{n₁^⊥} n₂)^⊥} (P_{n₁^⊥} x),

together with the exactness statement `elim2 n₁ n₂ (n₁ + n₂ + x) = elim2 n₁ n₂ x`.
What is still missing for the two-zero stage is the *survival* criterion: a usable
certificate that the target is **not** annihilated by the double projection.

For three tapers the channel space is `Fin 3 → ℝ`, and the criterion is the plain
`3 × 3` determinant:

    det3 n₁ n₂ t ≠ 0   ⟹   elim2 n₁ n₂ t ≠ 0.

The proof is exact linear algebra, with no inequality at all: `elim2 n₁ n₂ t` is by
construction `t` minus an explicit linear combination of `n₁` and `n₂`, so if it
vanishes then `t` lies in the span of the two nuisance directions and the determinant
degenerates.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.MultiTaperSchurCore

noncomputable section

namespace Zeta23Bridge
namespace ThreeTaperSchurCore

open Zeta23Bridge.MultiTaperSchurCore

/-! ## `elim2` removes an explicit linear combination -/

variable {ι : Type*} [Fintype ι]

/-- The coefficient of the *second* nuisance direction in `elim2`. -/
def elimCoeff2 (n₁ n₂ x : ι → ℝ) : ℝ :=
  dotP (perp2 n₁ n₂) (transverseComp n₁ x) / normSqP (perp2 n₁ n₂)

/-- The coefficient of the *first* nuisance direction in `elim2`. -/
def elimCoeff1 (n₁ n₂ x : ι → ℝ) : ℝ :=
  dotP n₁ x / normSqP n₁ - elimCoeff2 n₁ n₂ x * (dotP n₁ n₂ / normSqP n₁)

/-- **`elim2` is `x` minus an explicit combination of the two nuisance directions.** -/
theorem elim2_eq_sub (n₁ n₂ x : ι → ℝ) :
    elim2 n₁ n₂ x
      = x - elimCoeff1 n₁ n₂ x • n₁ - elimCoeff2 n₁ n₂ x • n₂ := by
  unfold elim2 elimCoeff1 elimCoeff2 perp2 transverseComp
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- If the double projection kills the target, the target lay in the span of the two
nuisance directions. -/
theorem exists_comb_of_elim2_eq_zero {n₁ n₂ x : ι → ℝ} (h : elim2 n₁ n₂ x = 0) :
    ∃ a b : ℝ, x = a • n₁ + b • n₂ := by
  refine ⟨elimCoeff1 n₁ n₂ x, elimCoeff2 n₁ n₂ x, ?_⟩
  have h' := elim2_eq_sub n₁ n₂ x
  rw [h] at h'
  funext i
  have hi : (0 : ℝ) = x i - elimCoeff1 n₁ n₂ x * n₁ i - elimCoeff2 n₁ n₂ x * n₂ i := by
    have := congrFun h' i
    simpa using this
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-! ## The three-dimensional determinant certificate -/

/-- The determinant of three channel vectors of the three-taper family. -/
def det3 (u v w : Fin 3 → ℝ) : ℝ :=
  u 0 * v 1 * w 2 - u 0 * v 2 * w 1 - u 1 * v 0 * w 2
    + u 1 * v 2 * w 0 + u 2 * v 0 * w 1 - u 2 * v 1 * w 0

/-- The determinant degenerates on a linear combination of its first two arguments. -/
theorem det3_comb (u v : Fin 3 → ℝ) (a b : ℝ) : det3 u v (a • u + b • v) = 0 := by
  unfold det3
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The survival criterion.**  A nonzero `3 × 3` determinant certifies that the
target direction survives the exact elimination of *both* nuisance directions. -/
theorem elim2_ne_zero_of_det3_ne_zero {n₁ n₂ t : Fin 3 → ℝ} (h : det3 n₁ n₂ t ≠ 0) :
    elim2 n₁ n₂ t ≠ 0 := by
  intro hz
  obtain ⟨a, b, rfl⟩ := exists_comb_of_elim2_eq_zero hz
  exact h (det3_comb n₁ n₂ a b)

/-- The residual energy after the exact removal of two nuisance directions is strictly
positive. -/
theorem normSqP_elim2_pos {n₁ n₂ t : Fin 3 → ℝ} (h : det3 n₁ n₂ t ≠ 0) :
    0 < normSqP (elim2 n₁ n₂ t) :=
  normSqP_pos_of_ne_zero (elim2_ne_zero_of_det3_ne_zero h)

/-- **Exactness of the double elimination**, restated here for the three-taper channel:
the two selected nuisance directions leave no residue whatsoever. -/
theorem elim2_add_two_nuisances {n₁ n₂ : Fin 3 → ℝ} (h₁ : n₁ ≠ 0) (h₂ : perp2 n₁ n₂ ≠ 0)
    (x : Fin 3 → ℝ) : elim2 n₁ n₂ (n₁ + n₂ + x) = elim2 n₁ n₂ x :=
  elim2_add_nuisance h₁ h₂ x

/-- A nonzero determinant forces the first nuisance direction to be nonzero. -/
theorem ne_zero_of_det3_ne_zero {n₁ n₂ t : Fin 3 → ℝ} (h : det3 n₁ n₂ t ≠ 0) : n₁ ≠ 0 := by
  intro h0
  apply h
  subst h0
  unfold det3
  simp

/-- A nonzero determinant forces the second nuisance direction to be transverse to the
first, so the double elimination is well posed. -/
theorem perp2_ne_zero_of_det3_ne_zero {n₁ n₂ t : Fin 3 → ℝ} (h : det3 n₁ n₂ t ≠ 0) :
    perp2 n₁ n₂ ≠ 0 := by
  intro h0
  apply h
  have hc : ∀ i, n₂ i = (dotP n₁ n₂ / normSqP n₁) * n₁ i := by
    intro i
    have hi : (perp2 n₁ n₂) i = 0 := by rw [h0]; rfl
    have hi' : n₂ i - (dotP n₁ n₂ / normSqP n₁) * n₁ i = 0 := hi
    linarith
  unfold det3
  rw [hc 0, hc 1, hc 2]
  ring

/-- **The constructed elimination is exact.**  A nonzero determinant supplies both
side conditions of `elim2_add_two_nuisances`, so the two selected nuisance responses
are removed from the residual with no error term whatsoever. -/
theorem elim2_add_two_nuisances_of_det3_ne_zero {n₁ n₂ t : Fin 3 → ℝ}
    (h : det3 n₁ n₂ t ≠ 0) (x : Fin 3 → ℝ) :
    elim2 n₁ n₂ (n₁ + n₂ + x) = elim2 n₁ n₂ x :=
  elim2_add_nuisance (ne_zero_of_det3_ne_zero h) (perp2_ne_zero_of_det3_ne_zero h) x

end ThreeTaperSchurCore
end Zeta23Bridge

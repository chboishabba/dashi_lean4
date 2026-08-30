/-
# The literal three-taper channel: two nuisance zeros removed exactly

`LiteralWeilTwoTaperCoefficientGate` runs the literal two-radius balance against a
*pair* of tapers and eliminates one nuisance zero exactly.  This module runs the same
balance against a *triple* of tapers, so that each literal zero contributes a vector in
`Fin 3 → ℝ` and **two** selected nuisance zeros can be removed exactly, by the
recursive operator `elim2` of `MultiTaperSchurCore`.

The admission certificate is the `3 × 3` determinant of the three response vectors.
Because each coordinate is quadratically small in the sampling radius,

    |zeroHeightDefect (g j) r ρ - r² · zeroLeadingCoeff (g j) ρ| ≤ r⁴ · zeroRemainderCoeff (g j) ρ,

the determinant is `r⁶`-small with the radius-free leading determinant as coefficient
(`abs_tripleDet_sub_leading_le`), and the admission test is again a radius-free
comparison of coefficients:

    r² · tripleRemainderCoeff < |tripleLeadingDet|  ⟹  tripleDet ≠ 0
                                                   ⟹  elim2 n₁ n₂ t ≠ 0.

`exists_radius_elim2_ne_zero` turns a nonzero leading determinant into an explicit
radius threshold.  The exactness of the elimination itself
(`elim2_add_two_nuisances_literal`) carries no error term at all: the two selected
directions are annihilated identically, not majorized.

Two sharp limitations of the mechanism are also proved, exactly as in the two-taper
case: the leading determinant vanishes whenever two of the three zeros have the same
height (`tripleLeadingDet_eq_zero_of_heightOf_eq₀₁` and its two companions), and it is
proportional to the determinant of the three tapers' `targetLeadingCoeff` responses
(`tripleLeadingDet_eq`), so the whole question is a total-positivity question about the
`3 × 3` matrix of leading responses.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoTaperCoefficientGate
import Zeta23Bridge.ThreeTaperCrossDetLeading

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilThreeTaperCoefficientGate

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.ThreeTaperSchurCore
open Zeta23Bridge.ThreeTaperCrossDetLeading

/-! ## The three-taper response vector of a single literal zero -/

/-- The literal response of the zero `ρ` to the three-taper family, at sampling
radius `r`. -/
def zeroRespVec3 (g : Fin 3 → ℝ → ℝ) (r : ℝ) (ρ : Zeros) : Fin 3 → ℝ :=
  fun j => zeroHeightDefect (g j) r ρ

/-- The radius-free leading response vector of the zero `ρ`. -/
def leadingVec3 (g : Fin 3 → ℝ → ℝ) (ρ : Zeros) : Fin 3 → ℝ :=
  fun j => zeroLeadingCoeff (g j) ρ

/-- The remainder coefficients of the zero `ρ`. -/
def remainderVec3 (g : Fin 3 → ℝ → ℝ) (ρ : Zeros) : Fin 3 → ℝ :=
  fun j => zeroRemainderCoeff (g j) ρ

theorem remainderVec3_nonneg (g : Fin 3 → ℝ → ℝ) (ρ : Zeros) (i : Fin 3) :
    0 ≤ remainderVec3 g ρ i := by
  unfold remainderVec3 zeroRemainderCoeff
  have := defectRemainderCoeff_nonneg (g i) (heightOf ρ)
  positivity

/-- The literal `3 × 3` determinant of two nuisance zeros against the target. -/
def tripleDet (g : Fin 3 → ℝ → ℝ) (r : ℝ) (σ₁ σ₂ ρ : Zeros) : ℝ :=
  det3 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ)

/-- The radius-free leading `3 × 3` determinant. -/
def tripleLeadingDet (g : Fin 3 → ℝ → ℝ) (σ₁ σ₂ ρ : Zeros) : ℝ :=
  det3 (leadingVec3 g σ₁) (leadingVec3 g σ₂) (leadingVec3 g ρ)

/-- The explicit relative remainder constant of the literal `3 × 3` determinant. -/
def tripleRemainderCoeff (g : Fin 3 → ℝ → ℝ) (σ₁ σ₂ ρ : Zeros) : ℝ :=
  det3Rem (leadingVec3 g σ₁) (remainderVec3 g σ₁) (leadingVec3 g σ₂) (remainderVec3 g σ₂)
    (leadingVec3 g ρ) (remainderVec3 g ρ)

theorem tripleRemainderCoeff_nonneg (g : Fin 3 → ℝ → ℝ) (σ₁ σ₂ ρ : Zeros) :
    0 ≤ tripleRemainderCoeff g σ₁ σ₂ ρ :=
  det3Rem_nonneg (remainderVec3_nonneg g σ₁) (remainderVec3_nonneg g σ₂)
    (remainderVec3_nonneg g ρ)

/-! ## The radius expansion of the literal three-taper determinant -/

private theorem respVec3_bound {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j)) (ρ : Zeros) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (i : Fin 3) :
    |zeroRespVec3 g r ρ i - r ^ 2 * leadingVec3 g ρ i|
      ≤ (r ^ 2) ^ 2 * remainderVec3 g ρ i := by
  have h := abs_zeroHeightDefect_sub_leading_le (hg i) (hgc i) ρ r hr0 hr1
  unfold zeroRespVec3 leadingVec3
  calc |zeroHeightDefect (g i) r ρ - r ^ 2 * zeroLeadingCoeff (g i) ρ|
      ≤ r ^ 4 * zeroRemainderCoeff (g i) ρ := h
    _ = (r ^ 2) ^ 2 * remainderVec3 g ρ i := by unfold remainderVec3; ring

/-- **The literal three-taper determinant is `r⁶`-small, with the radius-free leading
determinant as its coefficient.** -/
theorem abs_tripleDet_sub_leading_le {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ₁ σ₂ ρ : Zeros) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |tripleDet g r σ₁ σ₂ ρ - r ^ 6 * tripleLeadingDet g σ₁ σ₂ ρ|
      ≤ r ^ 8 * tripleRemainderCoeff g σ₁ σ₂ ρ := by
  have hs0 : (0:ℝ) ≤ r ^ 2 := by positivity
  have hs1 : r ^ 2 ≤ 1 := by nlinarith
  have h := abs_det3_sub_leading_le (s := r ^ 2) hs0 hs1
    (respVec3_bound hg hgc σ₁ hr0 hr1) (respVec3_bound hg hgc σ₂ hr0 hr1)
    (respVec3_bound hg hgc ρ hr0 hr1)
    (remainderVec3_nonneg g σ₁) (remainderVec3_nonneg g σ₂) (remainderVec3_nonneg g ρ)
  calc |tripleDet g r σ₁ σ₂ ρ - r ^ 6 * tripleLeadingDet g σ₁ σ₂ ρ|
      = |det3 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ)
          - (r ^ 2) ^ 3 * det3 (leadingVec3 g σ₁) (leadingVec3 g σ₂) (leadingVec3 g ρ)| := by
        unfold tripleDet tripleLeadingDet; ring_nf
    _ ≤ (r ^ 2) ^ 4 * tripleRemainderCoeff g σ₁ σ₂ ρ := h
    _ = r ^ 8 * tripleRemainderCoeff g σ₁ σ₂ ρ := by ring

/-- **The literal two-nuisance coefficient gate.**  A radius-free comparison of leading
coefficients forces the literal `3 × 3` determinant to be nonzero. -/
theorem tripleDet_ne_zero_of_coefficientGate {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ₁ σ₂ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * tripleRemainderCoeff g σ₁ σ₂ ρ < |tripleLeadingDet g σ₁ σ₂ ρ|) :
    tripleDet g r σ₁ σ₂ ρ ≠ 0 := by
  have hs0 : (0:ℝ) < r ^ 2 := by positivity
  have hs1 : r ^ 2 ≤ 1 := by nlinarith
  exact det3_ne_zero_of_coefficient_gate (s := r ^ 2) hs0 hs1
    (respVec3_bound hg hgc σ₁ hr0.le hr1) (respVec3_bound hg hgc σ₂ hr0.le hr1)
    (respVec3_bound hg hgc ρ hr0.le hr1)
    (remainderVec3_nonneg g σ₁) (remainderVec3_nonneg g σ₂) (remainderVec3_nonneg g ρ) hgate

/-! ## Admission: the target survives the exact removal of two nuisance zeros -/

/-- **Two-zero admission.**  Under the coefficient gate the target response survives the
exact elimination of *both* selected nuisance responses. -/
theorem elim2_ne_zero_of_coefficientGate {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ₁ σ₂ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * tripleRemainderCoeff g σ₁ σ₂ ρ < |tripleLeadingDet g σ₁ σ₂ ρ|) :
    elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ) ≠ 0 :=
  elim2_ne_zero_of_det3_ne_zero
    (tripleDet_ne_zero_of_coefficientGate hg hgc σ₁ σ₂ ρ hr0 hr1 hgate)

/-- The residual energy of the target after the exact removal of the two nuisance zeros
is strictly positive. -/
theorem normSqP_elim2_pos_of_coefficientGate {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ₁ σ₂ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * tripleRemainderCoeff g σ₁ σ₂ ρ < |tripleLeadingDet g σ₁ σ₂ ρ|) :
    0 < normSqP (elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ)) :=
  normSqP_elim2_pos (tripleDet_ne_zero_of_coefficientGate hg hgc σ₁ σ₂ ρ hr0 hr1 hgate)

/-- **From a nonzero leading determinant to an explicit radius threshold.** -/
theorem exists_radius_tripleDet_ne_zero {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j)) {σ₁ σ₂ ρ : Zeros}
    (hL : tripleLeadingDet g σ₁ σ₂ ρ ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      tripleDet g r σ₁ σ₂ ρ ≠ 0 := by
  set C : ℝ := tripleRemainderCoeff g σ₁ σ₂ ρ with hCdef
  have hC0 : 0 ≤ C := by rw [hCdef]; exact tripleRemainderCoeff_nonneg g σ₁ σ₂ ρ
  have hL0 : 0 < |tripleLeadingDet g σ₁ σ₂ ρ| := abs_pos.mpr hL
  refine ⟨min 1 (|tripleLeadingDet g σ₁ σ₂ ρ| / (C + 1)), ?_, min_le_left _ _, ?_⟩
  · exact lt_min one_pos (div_pos hL0 (by linarith))
  · intro r hr0 hr
    have hr1 : r ≤ 1 := hr.trans (min_le_left _ _)
    have hr2 : r ≤ |tripleLeadingDet g σ₁ σ₂ ρ| / (C + 1) := hr.trans (min_le_right _ _)
    have hrC : r * (C + 1) ≤ |tripleLeadingDet g σ₁ σ₂ ρ| := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < C + 1)] at hr2
      exact hr2
    have hsq : r ^ 2 * C ≤ r * C := by
      nlinarith [mul_nonneg (mul_nonneg hr0.le (sub_nonneg.mpr hr1)) hC0]
    refine tripleDet_ne_zero_of_coefficientGate hg hgc σ₁ σ₂ ρ hr0 hr1 ?_
    rw [← hCdef]
    nlinarith [hsq, hrC, hr0]

/-- **The full two-nuisance admission.**  A nonzero radius-free leading determinant
produces a radius threshold below which the target response survives the exact
elimination of both selected nuisance zeros. -/
theorem exists_radius_elim2_ne_zero {g : Fin 3 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j)) {σ₁ σ₂ ρ : Zeros}
    (hL : tripleLeadingDet g σ₁ σ₂ ρ ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ r0 →
      elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) (zeroRespVec3 g r ρ) ≠ 0 := by
  obtain ⟨r0, hr0, hr01, hdet⟩ := exists_radius_tripleDet_ne_zero hg hgc hL
  exact ⟨r0, hr0, hr01, fun r hrpos hrle =>
    elim2_ne_zero_of_det3_ne_zero (hdet r hrpos hrle)⟩

/-- **Exact elimination in the literal channel.**  Whatever else the fibre contains, the
two selected nuisance directions are removed from the residual with no error term. -/
theorem elim2_add_two_nuisances_literal {g : Fin 3 → ℝ → ℝ} {r : ℝ} {σ₁ σ₂ : Zeros}
    (h₁ : zeroRespVec3 g r σ₁ ≠ 0)
    (h₂ : perp2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) ≠ 0) (x : Fin 3 → ℝ) :
    elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂)
        (zeroRespVec3 g r σ₁ + zeroRespVec3 g r σ₂ + x)
      = elim2 (zeroRespVec3 g r σ₁) (zeroRespVec3 g r σ₂) x :=
  elim2_add_two_nuisances h₁ h₂ x

/-! ## What the leading determinant actually is, and when it degenerates -/

/-- The literal leading determinant is the multiplicity product times the determinant of
the three tapers' leading responses at the three heights. -/
theorem tripleLeadingDet_eq (g : Fin 3 → ℝ → ℝ) (σ₁ σ₂ ρ : Zeros) :
    tripleLeadingDet g σ₁ σ₂ ρ
      = 8 * ((Zeta23.zetaZeroConfig).mult σ₁ : ℝ) * ((Zeta23.zetaZeroConfig).mult σ₂ : ℝ)
          * ((Zeta23.zetaZeroConfig).mult ρ : ℝ)
        * det3 (fun j => targetLeadingCoeff (g j) (heightOf σ₁))
            (fun j => targetLeadingCoeff (g j) (heightOf σ₂))
            (fun j => targetLeadingCoeff (g j) (heightOf ρ)) := by
  unfold tripleLeadingDet leadingVec3 zeroLeadingCoeff det3
  ring

/-- **Sharp limitation.**  If two of the three zeros have the same height, the leading
determinant vanishes for *every* taper triple: this mechanism can only separate zeros
of pairwise distinct height moduli. -/
theorem tripleLeadingDet_eq_zero_of_heightOf_eq₀₁ (g : Fin 3 → ℝ → ℝ) {σ₁ σ₂ ρ : Zeros}
    (h : heightOf σ₁ = heightOf σ₂) : tripleLeadingDet g σ₁ σ₂ ρ = 0 := by
  rw [tripleLeadingDet_eq, h]
  unfold det3
  ring

theorem tripleLeadingDet_eq_zero_of_heightOf_eq₀₂ (g : Fin 3 → ℝ → ℝ) {σ₁ σ₂ ρ : Zeros}
    (h : heightOf σ₁ = heightOf ρ) : tripleLeadingDet g σ₁ σ₂ ρ = 0 := by
  rw [tripleLeadingDet_eq, h]
  unfold det3
  ring

theorem tripleLeadingDet_eq_zero_of_heightOf_eq₁₂ (g : Fin 3 → ℝ → ℝ) {σ₁ σ₂ ρ : Zeros}
    (h : heightOf σ₂ = heightOf ρ) : tripleLeadingDet g σ₁ σ₂ ρ = 0 := by
  rw [tripleLeadingDet_eq, h]
  unfold det3
  ring

end LiteralWeilThreeTaperCoefficientGate
end Zeta23Bridge

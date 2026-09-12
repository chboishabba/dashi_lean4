/-
# The literal two-taper Schur admission gate

The previous tranche proved a no-go for the *scalar* projective gate: at high
ordinate the off-ordinate channel is majorized by the absolute zero mass `W(t)`,
and that comparison loses.  The successor architecture is to stop majorizing the
nearby offenders and remove them **exactly**, by running the same literal balance
against a *family* of admissible tapers and projecting the nuisance directions out.

This module installs the first literal instance, with two tapers.  For a fixed pair
`g = (g₀, g₁)` and a sampling radius `r`, every zero `ρ` of the same-ordinate fibre
responds with the **vector**

    N_ρ = (D_ρ(g₀, r), D_ρ(g₁, r)) ∈ ℝ²,      D_ρ(g, r) = zeroHeightDefect g r ρ.

For a selected nuisance zero `σ` and the target zero `ρ` the admission certificate of
`TwoTaperCrossDetSchur` is the scalar cross determinant

    Δ_{σ,ρ}(r) = D_σ(g₀,r) D_ρ(g₁,r) - D_σ(g₁,r) D_ρ(g₀,r),

and `Δ_{σ,ρ}(r) ≠ 0` already gives `wedgeSq(N_σ, N_ρ) > 0` and hence
`P_{N_σ^⊥} N_ρ ≠ 0`: the target survives the *exact* removal of the nuisance
direction.  No `W(t)`, no absolute value, no zero-tail estimate occurs in that
statement.

Because each literal coordinate is quadratically small in the radius
(`abs_zeroHeightDefect_sub_leading_le`), the determinant has an `r⁴` leading term
with an `r⁶` remainder, so the admission test becomes the **radius-free coefficient
gate**

    r² · C_{σ,ρ} < |Δ⁰_{σ,ρ}|,
    Δ⁰_{σ,ρ} = L_σ(g₀) L_ρ(g₁) - L_σ(g₁) L_ρ(g₀).

Two honest limitations are also proved here, and they are sharp:

* `crossDet_eq_zero_of_heightOf_eq` — if the nuisance and the target have the same
  height, the two-taper determinant vanishes *identically in `r`, for every pair of
  tapers*.  The same holds for opposite heights, since the response depends on the
  height only through `cosh`.  So this mechanism can only eliminate a nuisance zero
  whose **height modulus differs** from the target's; in particular it never
  separates a zero from its functional-equation partner.
* `leadingCrossDet_eq_zero_of_ratio_eq` — proportional response profiles give a
  vanishing leading determinant.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
import Zeta23Bridge.TwoTaperCrossDetSchur
import Zeta23Bridge.TwoTaperCrossDetLeading

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTwoTaperCoefficientGate

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.MultiTaperSchurCore Zeta23Bridge.TwoTaperCrossDetSchur
open Zeta23Bridge.TwoTaperCrossDetLeading

/-! ## The two-taper response vector of a single literal zero -/

/-- The literal response of the zero `ρ` to the two-taper family, at sampling
radius `r`. -/
def zeroRespVec (g : Fin 2 → ℝ → ℝ) (r : ℝ) (ρ : Zeros) : Fin 2 → ℝ :=
  fun j => zeroHeightDefect (g j) r ρ

/-- The literal cross determinant of a nuisance zero `σ` against the target `ρ`. -/
def crossDet (g : Fin 2 → ℝ → ℝ) (r : ℝ) (σ ρ : Zeros) : ℝ :=
  det2 (zeroRespVec g r σ) (zeroRespVec g r ρ)

theorem crossDet_eq (g : Fin 2 → ℝ → ℝ) (r : ℝ) (σ ρ : Zeros) :
    crossDet g r σ ρ
      = zeroHeightDefect (g 0) r σ * zeroHeightDefect (g 1) r ρ
        - zeroHeightDefect (g 1) r σ * zeroHeightDefect (g 0) r ρ := rfl

/-- The radius-free leading determinant. -/
def leadingCrossDet (g : Fin 2 → ℝ → ℝ) (σ ρ : Zeros) : ℝ :=
  zeroLeadingCoeff (g 0) σ * zeroLeadingCoeff (g 1) ρ
    - zeroLeadingCoeff (g 1) σ * zeroLeadingCoeff (g 0) ρ

/-- The explicit relative remainder constant of the literal cross determinant. -/
def crossRemainderCoeff (g : Fin 2 → ℝ → ℝ) (σ ρ : Zeros) : ℝ :=
  crossRemainder (zeroLeadingCoeff (g 0) σ) (zeroRemainderCoeff (g 0) σ)
    (zeroLeadingCoeff (g 1) σ) (zeroRemainderCoeff (g 1) σ)
    (zeroLeadingCoeff (g 0) ρ) (zeroRemainderCoeff (g 0) ρ)
    (zeroLeadingCoeff (g 1) ρ) (zeroRemainderCoeff (g 1) ρ)

theorem zeroRemainderCoeff_nonneg (g : ℝ → ℝ) (ρ : Zeros) : 0 ≤ zeroRemainderCoeff g ρ := by
  unfold zeroRemainderCoeff
  have := defectRemainderCoeff_nonneg g (heightOf ρ)
  positivity

theorem crossRemainderCoeff_nonneg (g : Fin 2 → ℝ → ℝ) (σ ρ : Zeros) :
    0 ≤ crossRemainderCoeff g σ ρ :=
  crossRemainder_nonneg (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _)
    (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _)

/-! ## The radius expansion of the literal determinant -/

/-- **The literal two-taper determinant is quartically small in the radius, with the
radius-free leading determinant as its coefficient.** -/
theorem abs_crossDet_sub_leading_le {g : Fin 2 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ ρ : Zeros) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |crossDet g r σ ρ - r ^ 4 * leadingCrossDet g σ ρ|
      ≤ r ^ 6 * crossRemainderCoeff g σ ρ :=
  TwoTaperCrossDetLeading.abs_crossDet_sub_leading_le hr0 hr1
    (abs_zeroHeightDefect_sub_leading_le (hg 0) (hgc 0) σ r hr0 hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 1) (hgc 1) σ r hr0 hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 0) (hgc 0) ρ r hr0 hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 1) (hgc 1) ρ r hr0 hr1)
    (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _)
    (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _)

/-- **The literal coefficient gate.**  A radius-free comparison of leading
coefficients forces the literal cross determinant to be nonzero. -/
theorem crossDet_ne_zero_of_coefficientGate {g : Fin 2 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * crossRemainderCoeff g σ ρ < |leadingCrossDet g σ ρ|) :
    crossDet g r σ ρ ≠ 0 :=
  TwoTaperCrossDetLeading.crossDet_ne_zero_of_coefficient_gate hr0 hr1
    (abs_zeroHeightDefect_sub_leading_le (hg 0) (hgc 0) σ r hr0.le hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 1) (hgc 1) σ r hr0.le hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 0) (hgc 0) ρ r hr0.le hr1)
    (abs_zeroHeightDefect_sub_leading_le (hg 1) (hgc 1) ρ r hr0.le hr1)
    (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _)
    (zeroRemainderCoeff_nonneg _ _) (zeroRemainderCoeff_nonneg _ _) hgate

/-! ## Admission: the strict Gram wedge and the exact elimination -/

/-- **The Gram admission certificate.**  Under the coefficient gate the nuisance and
target response vectors span a nondegenerate plane. -/
theorem wedgeSq_pos_of_coefficientGate {g : Fin 2 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * crossRemainderCoeff g σ ρ < |leadingCrossDet g σ ρ|) :
    0 < wedgeSq (zeroRespVec g r σ) (zeroRespVec g r ρ) :=
  wedgeSq_pos_of_det2_ne_zero (crossDet_ne_zero_of_coefficientGate hg hgc σ ρ hr0 hr1 hgate)

/-- **The target survives the exact removal of the nuisance zero.** -/
theorem transverseComp_ne_zero_of_coefficientGate {g : Fin 2 → ℝ → ℝ}
    (hg : ∀ j, Continuous (g j)) (hgc : ∀ j, HasCompactSupport (g j))
    (σ ρ : Zeros) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hgate : r ^ 2 * crossRemainderCoeff g σ ρ < |leadingCrossDet g σ ρ|) :
    transverseComp (zeroRespVec g r σ) (zeroRespVec g r ρ) ≠ 0 :=
  transverseComp_ne_zero_of_wedgeSq_pos
    (wedgeSq_pos_of_coefficientGate hg hgc σ ρ hr0 hr1 hgate)

/-- **Exact elimination.**  Whatever else the fibre contains, the selected nuisance
direction is removed from the residual with no error term at all. -/
theorem transverseComp_add_nuisance {g : Fin 2 → ℝ → ℝ} {r : ℝ} {σ : Zeros}
    (hσ : zeroRespVec g r σ ≠ 0) (x : Fin 2 → ℝ) :
    transverseComp (zeroRespVec g r σ) (zeroRespVec g r σ + x)
      = transverseComp (zeroRespVec g r σ) x :=
  transverseComp_add_self_left hσ x

/-! ## The two sharp degeneracies of the two-taper channel -/

theorem heightDefect_neg_height (g : ℝ → ℝ) (r a : ℝ) :
    heightDefect g r (-a) 0 = heightDefect g r a 0 := by
  have hE : ∀ s : ℝ, evenResp g (-a) s = evenResp g a s := by
    intro s
    have hfun : (fun u : ℝ => g u * (Real.cosh (-a * u) * Real.cos (s * u)))
        = fun u : ℝ => g u * (Real.cosh (a * u) * Real.cos (s * u)) := by
      funext u
      rw [show -a * u = -(a * u) by ring, Real.cosh_neg]
    unfold evenResp
    rw [hfun]
  unfold heightDefect
  rw [hE, hE]

/-- **First degeneracy.**  Two zeros of the same height have parallel two-taper
response vectors, so the cross determinant vanishes identically — for every pair of
tapers and every radius. -/
theorem crossDet_eq_zero_of_heightOf_eq (g : Fin 2 → ℝ → ℝ) (r : ℝ) {σ ρ : Zeros}
    (h : heightOf σ = heightOf ρ) : crossDet g r σ ρ = 0 := by
  unfold crossDet det2 zeroRespVec zeroHeightDefect
  rw [h]
  ring

/-- **First degeneracy, reflected form.**  The response depends on the height only
through `cosh`, so a zero and its functional-equation partner (opposite height) are
also inseparable by this mechanism. -/
theorem crossDet_eq_zero_of_heightOf_eq_neg (g : Fin 2 → ℝ → ℝ) (r : ℝ) {σ ρ : Zeros}
    (h : heightOf σ = -heightOf ρ) : crossDet g r σ ρ = 0 := by
  unfold crossDet det2 zeroRespVec zeroHeightDefect
  rw [h, heightDefect_neg_height, heightDefect_neg_height]
  ring

/-- The same degeneracy at the level of the leading coefficients. -/
theorem leadingCrossDet_eq_zero_of_heightOf_eq (g : Fin 2 → ℝ → ℝ) {σ ρ : Zeros}
    (h : heightOf σ = heightOf ρ) : leadingCrossDet g σ ρ = 0 := by
  unfold leadingCrossDet zeroLeadingCoeff
  rw [h]
  ring

/-- **Second degeneracy / the live obligation.**  The leading determinant is nonzero
exactly when the two tapers see the nuisance and the target in *different
proportions*.  This response-ratio separation is the analytic content that the
localized-window geometry has to supply. -/
theorem leadingCrossDet_ne_zero_of_ratio_ne (g : Fin 2 → ℝ → ℝ) {σ ρ : Zeros}
    (h0 : zeroLeadingCoeff (g 0) ρ ≠ 0) (h1 : zeroLeadingCoeff (g 1) ρ ≠ 0)
    (hratio : zeroLeadingCoeff (g 0) σ / zeroLeadingCoeff (g 0) ρ
      ≠ zeroLeadingCoeff (g 1) σ / zeroLeadingCoeff (g 1) ρ) :
    leadingCrossDet g σ ρ ≠ 0 :=
  leadingDet_ne_zero_of_ratio_ne h0 h1 hratio

theorem leadingCrossDet_eq_zero_of_ratio_eq (g : Fin 2 → ℝ → ℝ) {σ ρ : Zeros}
    (h0 : zeroLeadingCoeff (g 0) ρ ≠ 0) (h1 : zeroLeadingCoeff (g 1) ρ ≠ 0)
    (hratio : zeroLeadingCoeff (g 0) σ / zeroLeadingCoeff (g 0) ρ
      = zeroLeadingCoeff (g 1) σ / zeroLeadingCoeff (g 1) ρ) :
    leadingCrossDet g σ ρ = 0 :=
  leadingDet_eq_zero_of_ratio_eq h0 h1 hratio

end LiteralWeilTwoTaperCoefficientGate
end Zeta23Bridge

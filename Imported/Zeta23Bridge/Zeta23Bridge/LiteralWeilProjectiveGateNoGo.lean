/-
# The projective gate is still quantitatively dead at large ordinates

`LiteralWeilProjectiveSeparationGate` proves the projectivized sandwich

    0 < D_{ρ*}(r) ≤ D_cluster(t, r) ≤ r² · E_proj(g, Λ, t, C_Γ),

and `LiteralWeilTargetDefectLeadingCoefficient` proves that the signal side is
itself `r² · zeroLeadingCoeff + O(r⁴)`.  The gate therefore became a comparison of
`r`-free coefficients.  This module carries that comparison out with explicit
majorants and shows that, exactly as in the radiuswise lane, the **coefficient
comparison fails once the off-ordinate zero mass is heavy relative to the target**.

The two sides are majorized as follows, for gate data with support radius `Λ`:

* residual side  — `20 t² ‖g‖₁² W(t) ≤ E_proj(g, Λ, t, C_Γ)`
  (`projectiveEnvelope_ge`), because `projStripCoeff` already contains the factor
  `(2 + 2|t| + t²)‖g‖₁ · 5(1+Λ)²‖g‖₁ · e^{Λ/2} ≥ 5 t² ‖g‖₁²`;
* signal side    — `zeroLeadingCoeff + zeroRemainderCoeff ≤ projSignalBound · ‖g‖₁²`
  with `projSignalBound = (3Λ² + (34Λ⁴ + 10Λ⁶)/12) · m_ρ · cosh(aΛ)`
  (`zeroLeadingCoeff_le`, `zeroRemainderCoeff_le`).

Hence, for `0 < r ≤ 1`,

    projSignalBound ≤ 20 t² W(t)   ⟹   ¬ (r² · E_proj < D_ρ(r))

(`projectiveGate_impossible_of_heavy_offOrdinate`).  Since
`Λ = 9π/(4|t|)` for the gate tapers of `exists_gateData`, `projSignalBound` decays
like `t⁻²` while the left-hand side grows like `t²`; the projectivization removed
the *order* mismatch in `r` but not the *ordinate* mismatch.  This is a statement
about the majorization method, not about the literal balance: it is what makes the
multi-taper Gram/Schur nuisance projection the next genuine step.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
import Zeta23Bridge.LiteralWeilProjectiveSeparationGate

noncomputable section

open scoped Real
open MeasureTheory

namespace Zeta23Bridge
namespace LiteralWeilProjectiveGateNoGo

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveStripConstant
open Zeta23Bridge.LiteralWeilProjectiveSeparationGate
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-! ## Majorizing the taper moments by the support radius -/

/-- If the weight `w` is bounded by `W` on the support radius of `g`, the weighted
absolute mass of `g` is at most `W · ‖g‖₁`. -/
theorem absMomWeight_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {w : ℝ → ℝ} (hw : Continuous w) {Λ W : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hbd : ∀ u, |u| ≤ Λ → w u ≤ W) :
    (∫ u : ℝ, |g u| * w u) ≤ W * taperMass g := by
  have h1 : Integrable (fun u : ℝ => |g u| * w u) := taper_integrable hg.abs hgc.abs hw
  have habs : Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  have h2 : Integrable (fun u : ℝ => W * |g u|) := habs.const_mul W
  have hpt : ∀ u : ℝ, |g u| * w u ≤ W * |g u| := by
    intro u
    by_cases hu : g u = 0
    · simp [hu]
    · have hle := hbd u (hsupp u hu)
      calc |g u| * w u ≤ |g u| * W := mul_le_mul_of_nonneg_left hle (abs_nonneg _)
        _ = W * |g u| := by ring
  calc (∫ u : ℝ, |g u| * w u) ≤ ∫ u : ℝ, W * |g u| := integral_mono h1 h2 hpt
    _ = W * taperMass g := by rw [integral_const_mul]; rfl

theorem cosh_le_of_abs_le {y u Λ : ℝ} (hΛ : 0 ≤ Λ) (hu : |u| ≤ Λ) :
    Real.cosh (y * u) ≤ Real.cosh (y * Λ) := by
  refine Real.cosh_le_cosh.mpr ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hΛ]
  exact mul_le_mul_of_nonneg_left hu (abs_nonneg _)

theorem absMom0_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (y : ℝ) :
    absMom0 g y ≤ Real.cosh (y * Λ) * taperMass g :=
  absMomWeight_le hg hgc (by fun_prop) hsupp fun _ hu => cosh_le_of_abs_le hΛ hu

theorem absMom2_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (y : ℝ) :
    absMom2 g y ≤ Λ ^ 2 * Real.cosh (y * Λ) * taperMass g := by
  refine absMomWeight_le hg hgc (by fun_prop) hsupp fun u hu => ?_
  have hsq : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hc := cosh_le_of_abs_le (y := y) hΛ hu
  exact mul_le_mul hsq hc (Real.cosh_pos _).le (by positivity)

theorem absMom4_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (y : ℝ) :
    absMom4 g y ≤ Λ ^ 4 * Real.cosh (y * Λ) * taperMass g := by
  refine absMomWeight_le hg hgc (by fun_prop) hsupp fun u hu => ?_
  have hsq2 : u ^ 2 ≤ Λ ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hsq : u ^ 4 ≤ Λ ^ 4 := by nlinarith [sq_nonneg u, sq_nonneg Λ]
  have hc := cosh_le_of_abs_le (y := y) hΛ hu
  exact mul_le_mul hsq hc (Real.cosh_pos _).le (by positivity)

/-! ## Signs of the taper moments -/

theorem coshMoment_nonneg {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) (y : ℝ) :
    0 ≤ coshMoment g y :=
  integral_nonneg fun u => mul_nonneg (hnn u) (Real.cosh_pos _).le

theorem sqCoshMoment_nonneg {g : ℝ → ℝ} (hnn : ∀ u, 0 ≤ g u) (y : ℝ) :
    0 ≤ sqCoshMoment g y :=
  integral_nonneg fun u =>
    mul_nonneg (hnn u) (mul_nonneg (by positivity) (Real.cosh_pos _).le)

/-! ## Majorizing the signal coefficients -/

theorem zeroLeadingCoeff_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (ρ : Zeros) :
    zeroLeadingCoeff g ρ
      ≤ 3 * ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * Λ ^ 2
          * Real.cosh (heightOf ρ * Λ) * taperMass g ^ 2 := by
  set a := heightOf ρ with ha
  set m : ℝ := ((Zeta23.zetaZeroConfig).mult ρ : ℝ) with hm
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hMass : (0:ℝ) ≤ taperMass g := taperMass_nonneg g
  -- the subtracted term is nonnegative
  have hsub : 0 ≤ coshMoment g a * sqCoshMoment g 0 :=
    mul_nonneg (coshMoment_nonneg hnn a) (sqCoshMoment_nonneg hnn 0)
  -- upper bounds on the surviving product
  have hNa : sqCoshMoment g a ≤ Λ ^ 2 * Real.cosh (a * Λ) * taperMass g :=
    le_trans (le_trans (le_abs_self _) (abs_sqCoshMoment_le hg hgc a))
      (absMom2_le hg hgc hsupp hΛ a)
  have hM0 : coshMoment g 0 ≤ taperMass g := by
    have h := le_trans (le_trans (le_abs_self _) (abs_coshMoment_le hg hgc 0))
      (absMom0_le hg hgc hsupp hΛ 0)
    simpa using h
  have hNa0 : 0 ≤ sqCoshMoment g a := sqCoshMoment_nonneg hnn a
  have hM00 : 0 ≤ coshMoment g 0 := coshMoment_nonneg hnn 0
  have hprod : sqCoshMoment g a * coshMoment g 0
      ≤ (Λ ^ 2 * Real.cosh (a * Λ) * taperMass g) * taperMass g :=
    mul_le_mul hNa hM0 hM00 (by positivity)
  have hexp : zeroLeadingCoeff g ρ
      = 3 * m * (sqCoshMoment g a * coshMoment g 0 - coshMoment g a * sqCoshMoment g 0) := by
    unfold zeroLeadingCoeff targetLeadingCoeff
    rw [← hm, ← ha]; ring
  rw [hexp]
  nlinarith [hprod, hsub, hm0]

theorem zeroRemainderCoeff_le {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {Λ : ℝ} (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ) (ρ : Zeros) :
    zeroRemainderCoeff g ρ
      ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * ((34 * Λ ^ 4 + 10 * Λ ^ 6) / 12)
          * Real.cosh (heightOf ρ * Λ) * taperMass g ^ 2 := by
  set a := heightOf ρ with ha
  set m : ℝ := ((Zeta23.zetaZeroConfig).mult ρ : ℝ) with hm
  have hm0 : (0:ℝ) ≤ m := by positivity
  have hMass : (0:ℝ) ≤ taperMass g := taperMass_nonneg g
  have hcosh : (1:ℝ) ≤ Real.cosh (a * Λ) := Real.one_le_cosh _
  have h4a : absMom4 g a ≤ Λ ^ 4 * Real.cosh (a * Λ) * taperMass g :=
    absMom4_le hg hgc hsupp hΛ a
  have h00 : absMom0 g 0 ≤ taperMass g := by
    simpa using absMom0_le hg hgc hsupp hΛ 0
  have h0a : absMom0 g a ≤ Real.cosh (a * Λ) * taperMass g := absMom0_le hg hgc hsupp hΛ a
  have h40 : absMom4 g 0 ≤ Λ ^ 4 * taperMass g := by
    simpa using absMom4_le hg hgc hsupp hΛ 0
  have h2a : absMom2 g a ≤ Λ ^ 2 * Real.cosh (a * Λ) * taperMass g :=
    absMom2_le hg hgc hsupp hΛ a
  have n4a := absMom4_nonneg g a
  have n00 := absMom0_nonneg g 0
  have n0a := absMom0_nonneg g a
  have n40 := absMom4_nonneg g 0
  have n2a := absMom2_nonneg g a
  have p1 : absMom4 g a * absMom0 g 0
      ≤ (Λ ^ 4 * Real.cosh (a * Λ) * taperMass g) * taperMass g :=
    mul_le_mul h4a h00 n00 (by positivity)
  have p2 : absMom0 g a * absMom4 g 0
      ≤ (Real.cosh (a * Λ) * taperMass g) * (Λ ^ 4 * taperMass g) :=
    mul_le_mul h0a h40 n40 (by positivity)
  have p3 : absMom2 g a * absMom4 g 0
      ≤ (Λ ^ 2 * Real.cosh (a * Λ) * taperMass g) * (Λ ^ 4 * taperMass g) :=
    mul_le_mul h2a h40 n40 (by positivity)
  have hexp : zeroRemainderCoeff g ρ
      = 2 * m * ((17 * (absMom4 g a * absMom0 g 0 + absMom0 g a * absMom4 g 0)
          + 10 * (absMom2 g a * absMom4 g 0)) / 24) := by
    unfold zeroRemainderCoeff defectRemainderCoeff
    rw [← hm, ← ha]
  rw [hexp]
  have hsum : 17 * (absMom4 g a * absMom0 g 0 + absMom0 g a * absMom4 g 0)
      + 10 * (absMom2 g a * absMom4 g 0)
      ≤ 17 * ((Λ ^ 4 * Real.cosh (a * Λ) * taperMass g) * taperMass g
            + (Real.cosh (a * Λ) * taperMass g) * (Λ ^ 4 * taperMass g))
        + 10 * ((Λ ^ 2 * Real.cosh (a * Λ) * taperMass g) * (Λ ^ 4 * taperMass g)) := by
    linarith [p1, p2, p3]
  have hscale := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2 * m / 24 by positivity)
  linarith [hscale]

/-! ## Majorizing the residual coefficient from below -/

theorem projStripCoeff_ge {g : ℝ → ℝ} {Λ t : ℝ} (hΛ : 0 ≤ Λ) :
    5 * t ^ 2 * taperMass g ^ 2 ≤ projStripCoeff g Λ t := by
  have hM : (0:ℝ) ≤ taperMass g := taperMass_nonneg g
  have hD : (0:ℝ) ≤ taperMass (deriv g) := taperMass_nonneg _
  have hD2 : (0:ℝ) ≤ taperMass (deriv (deriv g)) := taperMass_nonneg _
  have hexp : (1:ℝ) ≤ Real.exp (Λ / 2) := Real.one_le_exp (by linarith)
  have hbase : 5 * t ^ 2 * taperMass g ^ 2
      ≤ (5 * (1 + Λ) ^ 2 * taperMass g)
        * ((2 + 2 * |t| + t ^ 2) * taperMass g + (2 + 2 * |t|) * taperMass (deriv g)
            + taperMass (deriv (deriv g))) := by
    have hq : (0:ℝ) ≤ Λ ^ 2 + 2 * Λ := by nlinarith
    have h1 : (5 : ℝ) * taperMass g ≤ 5 * (1 + Λ) ^ 2 * taperMass g := by
      nlinarith [mul_nonneg hM hq]
    have h2 : t ^ 2 * taperMass g
        ≤ (2 + 2 * |t| + t ^ 2) * taperMass g + (2 + 2 * |t|) * taperMass (deriv g)
            + taperMass (deriv (deriv g)) := by
      have habs : (0:ℝ) ≤ |t| := abs_nonneg t
      nlinarith
    have h0 : (0:ℝ) ≤ 5 * taperMass g := by positivity
    have h0' : (0:ℝ) ≤ t ^ 2 * taperMass g := by positivity
    calc 5 * t ^ 2 * taperMass g ^ 2 = (5 * taperMass g) * (t ^ 2 * taperMass g) := by ring
      _ ≤ (5 * (1 + Λ) ^ 2 * taperMass g)
            * ((2 + 2 * |t| + t ^ 2) * taperMass g + (2 + 2 * |t|) * taperMass (deriv g)
                + taperMass (deriv (deriv g))) := by
          refine mul_le_mul h1 h2 h0' ?_
          nlinarith
  have hnn : (0:ℝ) ≤ (5 * (1 + Λ) ^ 2 * taperMass g)
      * ((2 + 2 * |t| + t ^ 2) * taperMass g + (2 + 2 * |t|) * taperMass (deriv g)
          + taperMass (deriv (deriv g))) := by
    have habs : (0:ℝ) ≤ |t| := abs_nonneg t
    have : (0:ℝ) ≤ 5 * (1 + Λ) ^ 2 * taperMass g := by positivity
    nlinarith
  unfold projStripCoeff
  nlinarith [hbase, hnn, hexp]

theorem projectiveEnvelope_ge {g : ℝ → ℝ} {Λ t CG : ℝ} (hΛ : 0 ≤ Λ) (hCG : 0 ≤ CG) :
    20 * t ^ 2 * taperMass g ^ 2 * offOrdWeight t ≤ projectiveEnvelope g Λ t CG := by
  have hW : 0 ≤ offOrdWeight t := offOrdWeight_nonneg t
  have hS := projStripCoeff_ge (g := g) (Λ := Λ) (t := t) hΛ
  have hS0 : (0:ℝ) ≤ projStripCoeff g Λ t := by
    have : (0:ℝ) ≤ 5 * t ^ 2 * taperMass g ^ 2 := by positivity
    linarith
  have hstep : 20 * t ^ 2 * taperMass g ^ 2 * offOrdWeight t
      ≤ 4 * projStripCoeff g Λ t * offOrdWeight t := by
    nlinarith [hS, hW]
  have hrest : (0:ℝ) ≤ projStripCoeff g Λ t * CG
      + 20 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2 := by
    have h1 : (0:ℝ) ≤ projStripCoeff g Λ t * CG := mul_nonneg hS0 hCG
    have h2 : (0:ℝ) ≤ 20 * Λ ^ 2 * Real.cosh (Λ / 2) * taperMass g ^ 2 := by
      have := (Real.cosh_pos (Λ / 2)).le
      positivity
    linarith
  unfold projectiveEnvelope
  linarith

/-! ## The no-go -/

/-- The explicit majorant of the signal coefficient, `‖g‖₁²` factored out. -/
def projSignalBound (m Λ a : ℝ) : ℝ :=
  (3 * Λ ^ 2 + (34 * Λ ^ 4 + 10 * Λ ^ 6) / 12) * m * Real.cosh (a * Λ)

/-- **`projectiveGate_impossible_of_heavy_offOrdinate`.**  The projectivized gate
inequality is *impossible* whenever the off-ordinate zero mass beats the explicit
signal majorant.  This is a comparison of two explicit expressions; it does not use
the literal balance and does not assume the existence of an off-line zero, so it is
a limitation of the majorization method itself. -/
theorem projectiveGate_impossible_of_heavy_offOrdinate
    {g : ℝ → ℝ} {t r Λ CG : ℝ} {ρ : Zeros} (hd : GateData g t r Λ) (hr1 : r ≤ 1)
    (hCG : 0 ≤ CG)
    (hheavy : projSignalBound ((Zeta23.zetaZeroConfig).mult ρ : ℝ) Λ (heightOf ρ)
        ≤ 20 * t ^ 2 * offOrdWeight t) :
    ¬ (r ^ 2 * projectiveEnvelope g Λ t CG < zeroHeightDefect g r ρ) := by
  intro hgate
  have hr0 : 0 < r := hd.radiusPos
  have hcont : Continuous g := hd.smooth.continuous
  have hMass : (0:ℝ) ≤ taperMass g := taperMass_nonneg g
  have hsq : (0:ℝ) ≤ taperMass g ^ 2 := by positivity
  have hUp := abs_zeroHeightDefect_sub_leading_le hcont hd.compactSupport ρ r hr0.le hr1
  have hUp' : zeroHeightDefect g r ρ
      ≤ r ^ 2 * zeroLeadingCoeff g ρ + r ^ 4 * zeroRemainderCoeff g ρ := by
    have h := (abs_le.1 hUp).2
    linarith
  have hL := zeroLeadingCoeff_le hcont hd.compactSupport hd.nonneg hd.supportRadius
    hd.lambdaNonneg ρ
  have hC := zeroRemainderCoeff_le hcont hd.compactSupport hd.supportRadius
    hd.lambdaNonneg ρ
  have hCnn : 0 ≤ zeroRemainderCoeff g ρ := by
    have h := defectRemainderCoeff_nonneg g (heightOf ρ)
    unfold zeroRemainderCoeff
    exact mul_nonneg (by positivity) h
  have hr2 : (0:ℝ) < r ^ 2 := by positivity
  have hrle1 : r ^ 2 ≤ 1 := by nlinarith
  have hr4 : r ^ 4 ≤ r ^ 2 := by
    nlinarith [mul_nonneg hr2.le (sub_nonneg.2 hrle1)]
  have hLC : zeroLeadingCoeff g ρ + zeroRemainderCoeff g ρ
      ≤ projSignalBound ((Zeta23.zetaZeroConfig).mult ρ : ℝ) Λ (heightOf ρ)
          * taperMass g ^ 2 := by
    unfold projSignalBound
    linarith [hL, hC]
  have hgap : 0 ≤ zeroRemainderCoeff g ρ * (r ^ 2 - r ^ 4) :=
    mul_nonneg hCnn (by linarith)
  have hscale := mul_le_mul_of_nonneg_left hLC hr2.le
  have hsig : zeroHeightDefect g r ρ
      ≤ r ^ 2 * (projSignalBound ((Zeta23.zetaZeroConfig).mult ρ : ℝ) Λ (heightOf ρ)
          * taperMass g ^ 2) := by
    nlinarith [hUp', hgap, hscale]
  have hEnv := projectiveEnvelope_ge (g := g) (Λ := Λ) (t := t) (CG := CG)
    hd.lambdaNonneg hCG
  have hcmp := mul_le_mul_of_nonneg_right hheavy hsq
  have hcmp2 := mul_le_mul_of_nonneg_left hcmp hr2.le
  have hEnv2 := mul_le_mul_of_nonneg_left hEnv hr2.le
  nlinarith [hgate, hsig, hcmp2, hEnv2]

end LiteralWeilProjectiveGateNoGo
end Zeta23Bridge

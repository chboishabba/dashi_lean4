import Synthesis.RiemannNormalizedProjectiveSameOrdinateCollapse
import Synthesis.RiemannCanonicalGateData

/-!
# Sign of the normalized horizontal quadratic coefficient at q = 0

The exact same-ordinate collapse gives two descriptions of one atom:

  A_rho^proj = -2 t D_rho

and

  A_rho^proj
    = m_rho * (a_rho^2/t^2) * Q_proj(t,a_rho/t,0).

For the canonical GateData, D_rho > 0 for every off-line zero.  Since t>0,
multiplicity is positive, and a_rho^2/t^2>0, the divided-square projective
horizontal coefficient is strictly negative at the physical same-ordinate point:

  Q_proj(t,a_rho/t,0) < 0.

Thus the exact alpha^2 factor has a theorem-bearing orientation, not merely a
vanishing order.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

theorem canonical_zeroHeightDefect_pos
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (hoff : heightOf rho ≠ 0) :
    0 <
    zeroHeightDefect
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
      rho := by
  let hd := quantitativeCanonicalGateData ht
  obtain ⟨u, v, hu, hv, huv⟩ := hd.twoPoint
  exact zeroHeightDefect_pos
    hd.smooth.continuous
    hd.compactSupport
    hd.nonneg
    hd.radiusPos
    hd.radial
    hu hv huv hoff

/-- Strict negativity of the divided-square horizontal projective kernel at the
same-ordinate physical point for every actual off-line zero. -/
theorem normalizedProjectiveHorizontalQuadratic_sameOrd_neg
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    normalizedProjectiveHorizontalQuadratic t
      (normalizedHorizontalHeight t rho) 0 < 0 := by
  have ht0 : 0 < t := by linarith
  have hD := canonical_zeroHeightDefect_pos ht hoff
  have hatomNeg :
      normalizedProjectiveOffZeroAtom t rho < 0 := by
    rw [normalizedProjectiveOffZeroAtom_sameOrd_eq_neg_two_t_mul_heightDefect
      ht him]
    nlinarith
  have hhoriz :=
    normalizedProjectiveOffZeroAtom_sameOrd_eq_heightSq_horizontal
      ht him
  have hmNat :
      (1 : ℕ) ≤ (zetaZeroConfig).mult (rho : ℂ) :=
    (zetaZeroConfig).one_le_mult (rho : ℂ) rho.2
  have hm :
      0 < ((zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    exact_mod_cast hmNat
  have ha2 : 0 < (heightOf rho) ^ 2 / t ^ 2 := by
    exact div_pos (sq_pos_of_ne_zero hoff) (sq_pos_of_pos ht0)
  have hcoef :
      0 <
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * ((heightOf rho) ^ 2 / t ^ 2) :=
    mul_pos hm ha2
  rw [hhoriz] at hatomNeg
  exact (mul_neg_iff.mp hatomNeg).resolve_left (not_lt_of_ge hcoef.le)

end Synthesis

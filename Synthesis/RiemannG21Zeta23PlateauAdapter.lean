import Mathlib.Tactic
import Synthesis.RiemannG21PositivePlateauMoment

/-!
# G21 adapter for the literal Zeta23 taper plateau

The companion Zeta23 parameter layer proves

* `0 < w`,
* `8*w <= L`,
* `phi(u)=1` whenever `|u| <= L/2-w`,
* `phi(u)>=0`.

Those hypotheses contain a canonical positive interval large enough for G21:

  l=L/16, m=L/8, r=L/4, R=L/2.

Indeed `L/4 <= L/2-w` follows already from `8w<=L`, so the entire interval
`(L/16,L/4)` lies inside the literal unit plateau.  This adapter is intentionally
stated against theorem-shaped inputs instead of importing Zeta23 directly,
because the companion currently pins a different Mathlib revision.  A future
same-object dependency/transport only has to instantiate these exact source
hypotheses.
-/

noncomputable section

open Set

namespace Synthesis

/-- Exact rational geometry of the canonical plateau subdivision. -/
theorem zeta23CanonicalPlateauGeometry
    {L w : ℝ} (hw : 0 < w) (hwL : 8*w <= L) :
    0 < L/16 ∧ L/16 < L/8 ∧ L/8 < L/4 ∧ L/4 < L/2 ∧ L/4 <= L/2-w := by
  have hL : 0 < L := by linarith
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

/-- `phi=1` on the Zeta23 plateau gives strict positivity on the canonical
positive subinterval used by the continuum moment compiler. -/
theorem zeta23CanonicalPlateauPositive
    {phi : ℝ → ℝ} {L w : ℝ}
    (hw : 0 < w) (hwL : 8*w <= L)
    (hphiOne : ∀ {u : ℝ}, |u| <= L/2-w -> phi u = 1) :
    ∀ u ∈ Ioo (L/16) (L/4), 0 < phi u := by
  intro u hu
  obtain ⟨hlpos, _, _, _, hrplateau⟩ := zeta23CanonicalPlateauGeometry hw hwL
  have hu0 : 0 < u := hlpos.trans hu.1
  have habs : |u| <= L/2-w := by
    rw [abs_of_pos hu0]
    exact hu.2.le.trans hrplateau
  rw [hphiOne habs]
  norm_num

/-- Canonical source-facing package.  It does not manufacture integrability;
those are supplied by the literal taper attachment. -/
structure Zeta23PlateauAttachment (phi : ℝ → ℝ) (L w : ℝ) : Prop where
  w_pos : 0 < w
  eight_w_le_L : 8*w <= L
  phi_nonneg : ∀ x, 0 <= phi x
  phi_eq_one : ∀ {u : ℝ}, |u| <= L/2-w -> phi u = 1

/-- The generic positive-plateau hypotheses required by G21 follow directly
from the literal Zeta23-style package. -/
theorem Zeta23PlateauAttachment.g21_plateau
    {phi : ℝ → ℝ} {L w : ℝ}
    (h : Zeta23PlateauAttachment phi L w) :
    0 < L/16 ∧ L/16 < L/8 ∧ L/8 < L/4 ∧ L/4 < L/2 ∧
    (∀ x ∈ Icc (0:ℝ) (L/2), 0 <= phi x) ∧
    (∀ x ∈ Ioo (L/16) (L/4), 0 < phi x) := by
  obtain ⟨h1,h2,h3,h4,_⟩ := zeta23CanonicalPlateauGeometry h.w_pos h.eight_w_le_L
  refine ⟨h1,h2,h3,h4,?_,?_⟩
  · intro x hx
    exact h.phi_nonneg x
  · exact zeta23CanonicalPlateauPositive h.w_pos h.eight_w_le_L h.phi_eq_one

end Synthesis

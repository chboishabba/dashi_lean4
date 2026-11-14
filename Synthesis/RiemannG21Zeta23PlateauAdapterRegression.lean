import Synthesis.RiemannG21Zeta23PlateauAdapter

/-! RED-first regression contract for the Zeta23 parameter/plateau adapter. -/

namespace Synthesis

example {L w : ℝ} (hw : 0 < w) (hwL : 8*w <= L) :
    0 < L/16 ∧ L/16 < L/8 ∧ L/8 < L/4 ∧ L/4 < L/2 ∧ L/4 <= L/2-w := by
  exact zeta23CanonicalPlateauGeometry hw hwL

example {phi : ℝ → ℝ} {L w : ℝ}
    (hw : 0 < w) (hwL : 8*w <= L)
    (hphiOne : ∀ {u : ℝ}, |u| <= L/2-w -> phi u = 1) :
    ∀ u ∈ Set.Ioo (L/16) (L/4), 0 < phi u := by
  exact zeta23CanonicalPlateauPositive hw hwL hphiOne

end Synthesis

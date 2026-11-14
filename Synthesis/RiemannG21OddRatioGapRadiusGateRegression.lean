import Synthesis.RiemannG21OddRatioGapRadiusGate

/-!
RED-first regression contract for the G21 odd ratio-gap / explicit-radius tranche.
The imported production owner is intentionally created in the following commit.
-/

namespace Synthesis

example {n1A n3A n1P n3P : ℝ}
    (hA : 0 < n1A) (hP : 0 < n1P)
    (hcross : n3A * n1P < n1A * n3P) :
    n3A / n1A < n3P / n1P := by
  exact oddRatioGap_of_crossProduct hA hP hcross

example {R gap : ℝ} (hR : 0 <= R) (hgap : 0 < gap) :
    ∃ r : ℝ, 0 < r ∧
      (510 * R^4 + 100 * R^6 + 4 * R^8) * r^2 < 900 * gap := by
  exact exists_supportOnlyOddRadiusGate hR hgap

example {R gap : ℝ} (hR : 0 <= R) (hgap : 0 < gap) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      (510 * R^4 + 100 * R^6 + 4 * R^8) * r^2 < 900 * gap := by
  exact exists_unit_supportOnlyOddRadiusGate hR hgap

end Synthesis

import Synthesis.RiemannG21CommonParityRadius

namespace Synthesis

example {R oddGap evenGap : ℝ}
    (hR : 0 <= R) (ho : 0 < oddGap) (he : 0 < evenGap) :
    ∃ r : ℝ, 0 < r ∧ r <= 1 ∧
      g21OddSupportPolynomial R*r^2 < 900*oddGap ∧
      g21EvenSupportPolynomial R*r^2 < 54*evenGap := by
  exact exists_unit_commonParityRadiusGate hR ho he

end Synthesis

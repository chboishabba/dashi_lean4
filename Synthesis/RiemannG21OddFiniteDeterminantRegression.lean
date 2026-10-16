import Synthesis.RiemannG21OddFiniteDeterminant

namespace Synthesis

example {r n1a n3a n1p n3p : ℝ} :
    oddCubicDeterminant r n1a n3a n1p n3p =
      -(36*r^4) * (n1a*n3p - n3a*n1p) := by
  exact oddCubicDeterminant_eq_signal

example {r n1a n3a n1p n3p ea1 ea2 ep1 ep2 : ℝ} :
    oddActualDeterminant r n1a n3a n1p n3p ea1 ea2 ep1 ep2
      - oddCubicDeterminant r n1a n3a n1p n3p
      = sixTermDetError
          (oddCubicTrunc r n1a n3a) (oddCubicTrunc (2*r) n1a n3a)
          (oddCubicTrunc r n1p n3p) (oddCubicTrunc (2*r) n1p n3p)
          ea1 ea2 ep1 ep2 := by
  exact oddActualDeterminant_sub_cubic

end Synthesis

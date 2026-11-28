import Mathlib
import YangMills.CompactSimpleCasimirOrbitFactorization

namespace RequestProject.YangMills

example
    (C lower total : ℝ)
    (hC : 0 ≤ C)
    (h : lower ≤ total) :
    C * lower ≤ C * total :=
  casimir_scale_transports_lower_bound C hC h

example (C a b c d : ℝ) :
    C * (a + b + c + d) = C * a + C * b + C * c + C * d :=
  casimir_scale_distributes_four_orbits C a b c d

end RequestProject.YangMills

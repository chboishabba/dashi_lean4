import Synthesis.RiemannG21AtomicHyperbolicTP2

namespace Synthesis

example {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.sinh (p*v) * Real.sinh (a*u)
      > Real.sinh (p*u) * Real.sinh (a*v) := by
  exact sinhKernel_strictTP2 ha hap hu huv

example {a p u v : ℝ}
    (ha : 0 < a) (hap : a < p) (hu : 0 < u) (huv : u < v) :
    Real.cosh (p*v) * Real.cosh (a*u)
      > Real.cosh (p*u) * Real.cosh (a*v) := by
  exact coshKernel_strictTP2 ha hap hu huv

end Synthesis

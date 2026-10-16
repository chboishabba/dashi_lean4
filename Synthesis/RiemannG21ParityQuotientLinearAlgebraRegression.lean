import Synthesis.RiemannG21ParityQuotientLinearAlgebra

namespace Synthesis

example {ea1 ea2 ep1 ep2 oa1 oa2 op1 op2 c d lam mu : ℝ}
    (he : ea1*ep2 - ea2*ep1 ≠ 0)
    (ho : oa1*op2 - oa2*op1 ≠ 0)
    (h1 : c*ea1 + d*oa1 = lam*ep1 + mu*op1)
    (h2 : c*ea1 - d*oa1 = lam*ep1 - mu*op1)
    (h3 : c*ea2 + d*oa2 = lam*ep2 + mu*op2)
    (h4 : c*ea2 - d*oa2 = lam*ep2 - mu*op2) :
    c = 0 ∧ d = 0 ∧ lam = 0 ∧ mu = 0 := by
  exact parityMinors_force_modPole_independence he ho h1 h2 h3 h4

end Synthesis

import Synthesis.RiemannG21SupportPolynomial

namespace Synthesis

example {R n1a n3a n5a n1p n3p n5p : ℝ}
    (hR : 0 <= R)
    (h1a : 0 <= n1a) (h3a0 : 0 <= n3a) (h5a0 : 0 <= n5a)
    (h1p : 0 <= n1p) (h3p0 : 0 <= n3p) (h5p0 : 0 <= n5p)
    (h3a : n3a <= R^2*n1a) (h5a : n5a <= R^4*n1a)
    (h3p : n3p <= R^2*n1p) (h5p : n5p <= R^4*n1p) :
    determinantErrorConstant
      (6*n1a+n3a) (12*n1a+8*n3a)
      (6*n1p+n3p) (12*n1p+8*n3p)
      (n5a/20) (n5p/20)
      <= (n1a*n1p/25) * g21OddSupportPolynomial R := by
  exact determinantErrorConstant_le_supportPolynomial hR
    h1a h3a0 h5a0 h1p h3p0 h5p0 h3a h5a h3p h5p

end Synthesis

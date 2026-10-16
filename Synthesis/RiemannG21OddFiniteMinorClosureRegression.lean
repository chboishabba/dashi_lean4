import Synthesis.RiemannG21OddFiniteMinorClosure

namespace Synthesis

example {R r n1a n3a n5a n1p n3p n5p ea1 ea2 ep1 ep2 : ℝ}
    (hR : 0 <= R) (hr : 0 < r) (hr1 : r <= 1)
    (h1a : 0 < n1a) (h3a0 : 0 <= n3a) (h5a0 : 0 <= n5a)
    (h1p : 0 < n1p) (h3p0 : 0 <= n3p) (h5p0 : 0 <= n5p)
    (h3a : n3a <= R^2*n1a) (h5a : n5a <= R^4*n1a)
    (h3p : n3p <= R^2*n1p) (h5p : n5p <= R^4*n1p)
    (hgate : g21OddSupportPolynomial R * r^2 <
      900 * (n3p/n1p - n3a/n1a))
    (hea1 : |ea1| <= r^5*(n5a/20))
    (hea2 : |ea2| <= 32*r^5*(n5a/20))
    (hep1 : |ep1| <= r^5*(n5p/20))
    (hep2 : |ep2| <= 32*r^5*(n5p/20)) :
    oddActualDeterminant r n1a n3a n1p n3p ea1 ea2 ep1 ep2 < 0 := by
  exact oddActualDeterminant_neg_of_supportGate
    hR hr hr1 h1a h3a0 h5a0 h1p h3p0 h5p0
    h3a h5a h3p h5p hgate hea1 hea2 hep1 hep2

end Synthesis

import Mathlib.Tactic
import Synthesis.RiemannG21OddFiniteDeterminant
import Synthesis.RiemannG21OddDeterminantMargin

/-!
# G21 actual finite odd-minor closure from the support-only gate

This is the quantitative P2 theorem for the odd sector.

Assume literal nonnegative moments N1,N3,N5 at heights a,p, compact-support
bounds N3<=R^2 N1 and N5<=R^4 N1, and choose 0<r<=1 satisfying

  P(R) r^2 < 900 (N3(p)/N1(p) - N3(a)/N1(a)),

where P(R)=510R^4+100R^6+4R^8.

If the four actual response remainders satisfy the fifth-order bounds at r and
2r, then the actual two-radius odd determinant is strictly negative in the
historical G21 orientation.

Thus the finite odd minor itself requires no additional analytic hypothesis
once the continuum ratio gap, compact-support moment bounds and integrated
fifth-order remainder are supplied.
-/

namespace Synthesis

/-- Division-free identity relating the normalized ratio gap to Delta_odd. -/
theorem oddDelta_eq_mass_mul_ratioGap
    {n1a n3a n1p n3p : ℝ}
    (h1a : 0 < n1a) (h1p : 0 < n1p) :
    n1a*n3p - n3a*n1p =
      n1a*n1p * (n3p/n1p - n3a/n1a) := by
  field_simp [h1a.ne', h1p.ne']
  ring

/-- The support-only small-radius gate closes the actual odd finite minor. -/
theorem oddActualDeterminant_neg_of_supportGate
    {R r n1a n3a n5a n1p n3p n5p ea1 ea2 ep1 ep2 : ℝ}
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
  have hpoly : 0 <= g21OddSupportPolynomial R :=
    g21OddSupportPolynomial_nonneg R
  have hgap : 0 < n3p/n1p - n3a/n1a := by
    have hlhs : 0 <= g21OddSupportPolynomial R * r^2 :=
      mul_nonneg hpoly (sq_nonneg r)
    nlinarith
  have hdeltaId := oddDelta_eq_mass_mul_ratioGap h1a h1p
  have hdelta : 0 < n1a*n3p - n3a*n1p := by
    rw [hdeltaId]
    positivity
  have hA1a0 : 0 <= 6*n1a+n3a := by positivity
  have hA2a0 : 0 <= 12*n1a+8*n3a := by positivity
  have hA1p0 : 0 <= 6*n1p+n3p := by positivity
  have hA2p0 : 0 <= 12*n1p+8*n3p := by positivity
  have hca0 : 0 <= n5a/20 := by positivity
  have hcp0 : 0 <= n5p/20 := by positivity
  have hta1 := oddCubicTrunc_abs_le_r_A1 hr.le hr1 h1a.le h3a0
  have hta2 := oddCubicTrunc_two_mul_abs_le_r_A2 hr.le hr1 h1a.le h3a0
  have htp1 := oddCubicTrunc_abs_le_r_A1 hr.le hr1 h1p.le h3p0
  have htp2 := oddCubicTrunc_two_mul_abs_le_r_A2 hr.le hr1 h1p.le h3p0
  have herr :
      |sixTermDetError
          (oddCubicTrunc r n1a n3a) (oddCubicTrunc (2*r) n1a n3a)
          (oddCubicTrunc r n1p n3p) (oddCubicTrunc (2*r) n1p n3p)
          ea1 ea2 ep1 ep2| <=
        r^6 * determinantErrorConstant
          (6*n1a+n3a) (12*n1a+8*n3a)
          (6*n1p+n3p) (12*n1p+8*n3p)
          (n5a/20) (n5p/20) :=
    sixTermDetError_le_coefficient hr.le hr1
      hA1a0 hA2a0 hA1p0 hA2p0 hca0 hcp0
      hta1 hta2 htp1 htp2 hea1 hea2 hep1 hep2
  have hC := determinantErrorConstant_le_supportPolynomial hR
    h1a.le h3a0 h5a0 h1p.le h3p0 h5p0 h3a h5a h3p h5p
  have hr6 : 0 <= r^6 := by positivity
  have herrSupport :
      |sixTermDetError
          (oddCubicTrunc r n1a n3a) (oddCubicTrunc (2*r) n1a n3a)
          (oddCubicTrunc r n1p n3p) (oddCubicTrunc (2*r) n1p n3p)
          ea1 ea2 ep1 ep2| <=
        r^6 * ((n1a*n1p/25) * g21OddSupportPolynomial R) := by
    exact herr.trans (mul_le_mul_of_nonneg_left hC hr6)
  have hscale : 0 < r^4 * (n1a*n1p/25) := by positivity
  have hgateScaled := mul_lt_mul_of_pos_left hgate hscale
  have hstrict :
      r^6 * ((n1a*n1p/25) * g21OddSupportPolynomial R)
        < 36*r^4*(n1a*n3p - n3a*n1p) := by
    rw [hdeltaId]
    nlinarith [hgateScaled]
  have hdiff :
      |oddActualDeterminant r n1a n3a n1p n3p ea1 ea2 ep1 ep2
        - oddCubicDeterminant r n1a n3a n1p n3p|
      < |oddCubicDeterminant r n1a n3a n1p n3p| := by
    rw [oddActualDeterminant_sub_cubic]
    have hcubicAbs :
        |oddCubicDeterminant r n1a n3a n1p n3p|
          = 36*r^4*(n1a*n3p - n3a*n1p) := by
      rw [oddCubicDeterminant_eq_signal]
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 <= 36*r^4),
        abs_of_pos hdelta]
    rw [hcubicAbs]
    exact herrSupport.trans_lt hstrict
  have hcubic : oddCubicDeterminant r n1a n3a n1p n3p < 0 := by
    rw [oddCubicDeterminant_eq_signal]
    positivity
  exact negative_of_abs_sub_lt_abs hcubic hdiff

end Synthesis

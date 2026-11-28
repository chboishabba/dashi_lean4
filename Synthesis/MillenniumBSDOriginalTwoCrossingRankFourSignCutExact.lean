import Synthesis.MillenniumBSDSignedMellinMomentProgressionExact

/-!
Original two-crossing signed Mellin obstruction at the rank-four
complex second-derivative target.

The original integrated positive polynomial (a true analytic-source
input) and zero total mass force a sign alternative. A purported
m2=0 certificate is incompatible with m1 >= 0. This is useful for
selecting or refuting original period-return producers, but it does
NOT establish a sign of the actual selected m1 or an analytic L''=0.
-/
namespace DASHI.BSD.SignedCrossing

/-- Exact required first-moment sign for a zero second moment, with
the ORIGINAL signed two-crossing quadratic polynomial. -/
theorem twoCrossing_zeroSecond_requires_negativeFirst
    {a b m0 m1 m2 : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzeroMass : m0 = 0)
    (hzeroSecond : m2 = 0)
    (hpositive : 0 <
      h a b 0 * m2 - h a b 1 * m1 + (a*b)^(0+1) * m0) :
    m1 < 0 := by
  have hh : 0 < h a b 1 := h_pos ha hb 1
  simp only [hzeroMass, hzeroSecond, mul_zero, zero_sub, add_zero] at hpositive
  by_contra hn
  have hnonneg : 0 ≤ m1 := le_of_not_gt hn
  have hp := mul_nonneg hh.le hnonneg
  linarith

/-- Original two-crossing signed positivity makes a nonnegative first
Mellin moment force a STRICT positive second moment. Equivalently,
the original complex second-derivative zero requires separate
signed cancellation; it is not obtained from positive return data. -/
theorem twoCrossing_nonnegativeFirst_forces_positiveSecond
    {a b m0 m1 m2 : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hzeroMass : m0 = 0)
    (hfirst : 0 ≤ m1)
    (hpositive : 0 <
      h a b 0 * m2 - h a b 1 * m1 + (a*b)^(0+1) * m0) :
    0 < m2 :=
  next_moment_pos ha hb 0 hzeroMass hfirst hpositive

end DASHI.BSD.SignedCrossing

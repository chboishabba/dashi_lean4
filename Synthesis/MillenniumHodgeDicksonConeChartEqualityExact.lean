import Synthesis.MillenniumHodgeDicksonConeHomogeneousChartExact

namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- The original affine evaluation of two same-degree homogeneous
numerators agrees precisely when their difference lies in the cone ideal.
No reducedness assumption is needed. -/
theorem homogeneous_chart_equality (p q : ProjectiveAmbientPoly) (d : ℕ)
    (hpq : (p-q).IsHomogeneous d) :
    p-q ∈ actualConeIdeal ↔ coneAtOne p = coneAtOne q := by
  rw [homogeneous_cone_chart_kernel (p-q) d hpq, map_sub, sub_eq_zero]

/-- Cross multiply before comparing different-degree chart numerators.
The supplied homogeneity is explicit; this is the fraction equality
criterion, not yet a construction of the scheme chart. -/
theorem chart_cross_numerator_equality (p q : ProjectiveAmbientPoly) (d e : ℕ)
    (hh : (p * (MvPolynomial.X none)^e - q * (MvPolynomial.X none)^d).IsHomogeneous (d+e)) :
    p * (MvPolynomial.X none)^e - q * (MvPolynomial.X none)^d ∈ actualConeIdeal ↔
      coneAtOne p = coneAtOne q := by
  have h := homogeneous_chart_equality
    (p * (MvPolynomial.X none)^e) (q * (MvPolynomial.X none)^d) (d+e) hh
  have h1 : coneAtOne (MvPolynomial.X none) = 1 := by simp [coneAtOne, coneAffineValue]
  simpa [map_mul, map_pow, h1] using h

end
end DASHI.Hodge.DicksonCoupled

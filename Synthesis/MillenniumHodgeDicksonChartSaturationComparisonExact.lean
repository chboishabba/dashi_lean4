import Synthesis.MillenniumHodgeDicksonConeChartEqualityExact

/-! Section 21f. Exact denominator-stability for the original
homogeneous cone chart; no appeal to pointwise reducedness. -/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- Cross-numerator equality is unchanged by multiplication by an
arbitrary power of the original homogenizing coordinate. This is the
necessary saturation criterion for an actual localized h-chart. -/
theorem chart_cross_equality_stable_under_h
    (p q : ProjectiveAmbientPoly) (d e r : ℕ)
    (hh : (p * (MvPolynomial.X none)^e -
          q * (MvPolynomial.X none)^d).IsHomogeneous (d+e)) :
    (MvPolynomial.X none)^r *
        (p * (MvPolynomial.X none)^e -
          q * (MvPolynomial.X none)^d) ∈ actualConeIdeal ↔
        coneAtOne p = coneAtOne q := by
  rw [actualCone_h_saturated,
    chart_cross_numerator_equality p q d e hh]

/-- Even the zero-denominator-power case uses the same original chart
carrier; this identifies the localized equality predicate without
introducing an auxiliary affine scheme. -/
theorem chart_same_degree_stable_under_h
    (p q : ProjectiveAmbientPoly) (d r : ℕ)
    (hh : (p-q).IsHomogeneous d) :
    (MvPolynomial.X none)^r * (p-q) ∈ actualConeIdeal ↔
      coneAtOne p = coneAtOne q := by
  rw [actualCone_h_saturated,
    homogeneous_chart_equality p q d hh]

end
end DASHI.Hodge.DicksonCoupled

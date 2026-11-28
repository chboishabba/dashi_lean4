import Synthesis.MillenniumHodgeDicksonChartSaturationComparisonExact

/-! Original homogeneous-component evaluation of the full cone ideal.
This is not merely a pointwise algebraic-set kernel. -/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- The entire original homogeneous cone ideal is determined by exact
degreewise evaluations in the original, potentially nonreduced open ring. -/
theorem original_cone_ideal_iff_degreewise_evaluation
    (p : ProjectiveAmbientPoly) :
    p ∈ actualConeIdeal ↔
      ∀ d : ℕ, coneAtOne (MvPolynomial.homogeneousComponent d p) = 0 := by
  rw [actualCone_mem_iff_components]
  constructor
  · intro h d
    exact (homogeneous_cone_chart_kernel
      (MvPolynomial.homogeneousComponent d p) d
      (MvPolynomial.homogeneousComponent_isHomogeneous d p)).mp (h d)
  · intro h d
    exact (homogeneous_cone_chart_kernel
      (MvPolynomial.homogeneousComponent d p) d
      (MvPolynomial.homogeneousComponent_isHomogeneous d p)).mpr (h d)

/-- A global polynomial vanishes in the original cone precisely when
all of its original homogeneous source coefficients vanish. -/
theorem original_cone_ideal_iff_cone_coefficients
    (p : ProjectiveAmbientPoly) :
    p ∈ actualConeIdeal ↔ ∀ d : ℕ, (actualConeMap p).coeff d = 0 := by
  rw [original_cone_ideal_iff_degreewise_evaluation]
  simp_rw [← coneMap_coeff]

end
end DASHI.Hodge.DicksonCoupled

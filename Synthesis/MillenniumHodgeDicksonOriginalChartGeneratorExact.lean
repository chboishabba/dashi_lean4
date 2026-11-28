import Synthesis.MillenniumHodgeDicksonConeComponentKernelExact

/-!
Original h=1 chart: every canonical affine source coordinate has an
explicit homogeneous numerator. This supplies the generator image
for the genuine degree-zero Proj localization; it does NOT assume that
those coordinates generate the entire localized source algebra.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- On the same original coordinate carrier, the homogeneous projective
coordinate X_i becomes the actual affine source coordinate at h=1. -/
theorem original_chart_coordinate_has_homogeneous_lift
    (i : OriginalCoord) :
    ∃ p : ProjectiveAmbientPoly,
      p.IsHomogeneous 1 ∧
      coneAtOne p = originalOpenCoord i := by
  refine ⟨MvPolynomial.X (some i), ?_, ?_⟩
  · simpa using
      (MvPolynomial.isHomogeneous_X (some i) (R := ℚ))
  · simp [coneAtOne, coneAffineValue]

/-- The homogenizing coordinate has degree one but maps to the unit
of the actual source ring on the principal open. -/
theorem original_chart_h_maps_to_one :
    coneAtOne (MvPolynomial.X none) = 1 := by
  simp [coneAtOne, coneAffineValue]

end
end DASHI.Hodge.DicksonCoupled

import Synthesis.MillenniumHodgeDicksonOriginalChartGeneratorExact

/-!
Original affine coordinate algebra to projective h-chart: source-level
bidirectional polynomial lifting. This does not silently identify the
coordinate-generated subalgebra with the entire localized source A:
the global/proper chart may have additional denominator generators.

The inverse is a genuine polynomial substitution on the ORIGINAL
coordinates and preserves nilpotents because it uses ring homomorphisms
rather than pointwise equations.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section

/-- The original affine coordinate-polynomial evaluation, kept distinct
from the ambient localized source algebra. -/
def originalCoordinateEval :
    MvPolynomial OriginalCoord ℚ →+* ActualSourceOpen :=
  MvPolynomial.eval₂Hom
    (algebraMap ℚ ActualSourceOpen) originalOpenCoord

/-- Reuse exactly the source projective coordinate names; the chosen
homogenizing h coordinate is not mixed into their indices. -/
def projectiveCoordinateLift :
    MvPolynomial OriginalCoord ℚ →+* ProjectiveAmbientPoly :=
  MvPolynomial.rename some

/-- Source-polynomial to original cone chart evaluation, BIDI on
coordinate-generated functions. The remaining affine A=B assertion is
an independent algebra generation / denominator-weld obligation. -/
theorem originalCoordinateEval_eq_cone_lift (p : MvPolynomial OriginalCoord ℚ) :
    coneAtOne (projectiveCoordinateLift p) = originalCoordinateEval p := by
  classical
  have h : coneAtOne.comp projectiveCoordinateLift =
      originalCoordinateEval := by
    apply MvPolynomial.ringHom_ext
    intro i
    simp [originalCoordinateEval, projectiveCoordinateLift,
      coneAtOne, coneAffineValue]
  exact congrArg (fun f : MvPolynomial OriginalCoord ℚ →+* ActualSourceOpen => f p) h

/-- Every element of the original coordinate-generated affine subring,
not just each individual coordinate, has a literal original projective
numerator at h=1. -/
theorem original_coordinate_generated_has_projective_lift
    (z : ActualSourceOpen)
    (hz : z ∈ Set.range originalCoordinateEval) :
    ∃ q : ProjectiveAmbientPoly, coneAtOne q = z := by
  obtain ⟨p, rfl⟩ := hz
  exact ⟨projectiveCoordinateLift p,
    originalCoordinateEval_eq_cone_lift p⟩

end
end DASHI.Hodge.DicksonCoupled

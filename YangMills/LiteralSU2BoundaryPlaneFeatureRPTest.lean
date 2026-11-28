import YangMills.LiteralSU2BoundaryPlaneFeatureRP

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (β : ℝ) (hβ : 0 ≤ β)
    (f : SU2PositiveInteriorLinks n → ℝ)
    (hfMeas : Measurable f)
    (hfInt : MeasureTheory.Integrable f (literalSU2PositiveInteriorHaar n)) :
    0 ≤ independentBoundaryFeatureExponentialQuadratic
      (literalSU2BoundaryPlaneHaar n)
      (literalSU2PositiveInteriorHaar n)
      (Finset.univ : Finset (SU2BoundaryPlaneCrossingFeatureIndex n))
      (fun _ => (1 : ℝ))
      (su2BoundaryPlaneCrossingFeature n)
      β f :=
  su2_boundary_plane_augmented_crossing_exponential_rp
    n β hβ f hfMeas hfInt

end RequestProject.YangMills

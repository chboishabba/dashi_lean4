import Mathlib
import YangMills.LiteralSU2BoundaryPlaneHaarSplit

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (p : SU2BoundaryTemporalLinkIndex n) :
    (su2BoundaryTemporalPlaneEquiv n).symm
      (su2BoundaryTemporalPlaneEquiv n p) = p := by
  simp

example
    (n : ℕ) [NeZero n] :
    MeasureTheory.Measure.map
      (su2BoundaryTemporalPlaneAssemble n)
      (literalSU2BoundaryPlaneHaar n) =
      literalSU2BoundaryTemporalHaar n :=
  literal_su2_boundary_temporal_haar_plane_split n

end RequestProject.YangMills

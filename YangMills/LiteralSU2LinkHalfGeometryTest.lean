import Mathlib
import YangMills.LiteralSU2LinkHalfGeometry
import YangMills.LiteralSU2LinkSectorProductSplit

namespace RequestProject.YangMills

/-! Compile probes for the final Wilson OS2 product decomposition. -/

example
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n)) :
    su2PositiveInteriorLink n p ∨
      su2NegativeInteriorLink n p ∨
      su2ReflectionBoundaryTemporalLink n p :=
  su2_even_time_link_cut_exhaustive n p

example
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2ReflectionBoundaryTemporalLink n p) :
    fourDimensionalEvenTimeReflectLinkIndex p = p :=
  su2_boundary_temporal_link_index_fixed n p hp

example
    (n : ℕ) [NeZero n]
    (p : FourDimensionalLinkIndex (2 * n))
    (hp : su2PositiveInteriorLink n p) :
    su2NegativeInteriorLink n
      (fourDimensionalEvenTimeReflectLinkIndex p) :=
  su2_positive_interior_reflects_negative n p hp

example
    (n : ℕ) [NeZero n] :
    SU2PositiveInteriorLinkIndex n ≃ SU2NegativeInteriorLinkIndex n :=
  su2PositiveNegativeLinkReflectionEquiv n

example
    (n : ℕ) [NeZero n] :
    (SU2PositiveInteriorLinkIndex n ⊕
      SU2BoundaryTemporalLinkIndex n ⊕
      SU2NegativeInteriorLinkIndex n) ≃
      FourDimensionalLinkIndex (2 * n) :=
  su2LinkSectorSumEquiv n

end RequestProject.YangMills

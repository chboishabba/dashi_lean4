import Mathlib
import YangMills.LiteralSU2CrossingHalfPathSectorGeometry

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2ReflectionBoundaryTemporalLink n (p.1, p.2.1) ∧
    su2NegativeInteriorLink n (su2Shift p.1 p.2.1, p.2.2) ∧
    su2PositiveInteriorLink n (p.1, p.2.2) ∧
    su2ReflectionBoundaryTemporalLink n (su2Shift p.1 p.2.2, p.2.1) :=
  su2_upper_crossing_link_sector_geometry n p hp

example
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2ReflectionBoundaryTemporalLink n (p.1, p.2.1) ∧
    su2PositiveInteriorLink n (su2Shift p.1 p.2.1, p.2.2) ∧
    su2NegativeInteriorLink n (p.1, p.2.2) ∧
    su2ReflectionBoundaryTemporalLink n (su2Shift p.1 p.2.2, p.2.1) :=
  su2_lower_crossing_link_sector_geometry n p hp

end RequestProject.YangMills

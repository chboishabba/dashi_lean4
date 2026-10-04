import Mathlib
import YangMills.LiteralSU2CrossingSlabGeometry

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n] :
    su2UpperCrossingPlaquettes n ∪ su2LowerCrossingPlaquettes n =
      su2EvenTimeCrossingPlaquettes n :=
  su2_crossing_slabs_partition n

example
    (n : ℕ) [NeZero n] :
    Disjoint (su2UpperCrossingPlaquettes n)
      (su2LowerCrossingPlaquettes n) :=
  su2_crossing_slabs_disjoint n

end RequestProject.YangMills

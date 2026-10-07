import YangMills.LiteralSU2CrossingPositiveIndexCoincidence

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2UpperCrossingPlaquettes n) :
    su2UpperCrossingRightPositiveIndex n p hp =
      su2UpperCrossingLeftPositiveIndex n p hp :=
  su2_upper_crossing_positive_index_coincides n p hp

example
    (n : ℕ) [NeZero n]
    (p : SU2LiteralPlaquetteIndex (2 * n))
    (hp : p ∈ su2LowerCrossingPlaquettes n) :
    su2LowerCrossingRightPositiveIndex n p hp =
      su2LowerCrossingLeftPositiveIndex n p hp :=
  su2_lower_crossing_positive_index_coincides n p hp

end RequestProject.YangMills

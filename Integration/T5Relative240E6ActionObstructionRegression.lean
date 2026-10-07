import Integration.T5Relative240E6ActionObstruction

namespace Integration.T5Relative240E6ActionObstructionRegression

open Integration.T5Relative240E6ActionObstruction

example : Fintype.card StandardRelative240 = 240 := standard_relative_card_240
example : standardIsDiagonal badPoint = false := bad_point_is_relative
example : standardIsDiagonal (Integration.E6Mod3WeylAction.reflectStandard .s3 badPoint) = true :=
  s3_sends_bad_point_to_diagonal
example : ¬ NaturalRelative240InvariantUnderE6 := natural_relative_240_not_e6_invariant
example : IsEmpty NaturalE6ActionOnRelative240 := no_natural_e6_action_on_relative_240
example : canonicalBoundary.naturalSameActionE8RecognitionBlocked = true := rfl
example : canonicalBoundary.allPossibleTernary240ActionsBlocked = false := rfl

end Integration.T5Relative240E6ActionObstructionRegression

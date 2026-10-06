import Integration.E8LiteralMixed27Fibres

namespace Integration.E8LiteralMixed27FibresRegression

open Integration.E8LiteralMixed27Fibres

example : Fintype.card Plus0 = 27 := plus0_card
example : Fintype.card Plus1 = 27 := plus1_card
example : Fintype.card Plus2 = 27 := plus2_card
example : Fintype.card Minus0 = 27 := minus0_card
example : Fintype.card Minus1 = 27 := minus1_card
example : Fintype.card Minus2 = 27 := minus2_card
example : 81 = 27 + 27 + 27 := by norm_num
example : ∀ s r, reflectedWeight s r = a2Weight r := literal_e6_reflection_preserves_a2_weight
example : ¬ BareF3FiveOrbitSize 27 := no_bare_f3five_27_orbit_size
example : canonicalBoundary.literalMixedFibresSixTimes27Paid = true := rfl
example : canonicalBoundary.bareF3FiveSupplies27Orbit = false := rfl
example : canonicalBoundary.albert27RecognitionAutomaticallyPaid = false := rfl

end Integration.E8LiteralMixed27FibresRegression

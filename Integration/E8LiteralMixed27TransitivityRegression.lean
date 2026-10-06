import Integration.E8LiteralMixed27Transitivity

namespace Integration.E8LiteralMixed27TransitivityRegression

open Integration.E8LiteralMixed27Transitivity

example : ∀ seed : Plus0, plus0Orbit seed = Finset.univ := plus0_orbit_full
example : ∀ seed : Plus1, plus1Orbit seed = Finset.univ := plus1_orbit_full
example : ∀ seed : Plus2, plus2Orbit seed = Finset.univ := plus2_orbit_full
example : ∀ seed : Minus0, minus0Orbit seed = Finset.univ := minus0_orbit_full
example : ∀ seed : Minus1, minus1Orbit seed = Finset.univ := minus1_orbit_full
example : ∀ seed : Minus2, minus2Orbit seed = Finset.univ := minus2_orbit_full
example : canonicalBoundary.sixFibresE6TransitivePaid = true := rfl
example : canonicalBoundary.actionChosenByTransport = false := rfl

end Integration.E8LiteralMixed27TransitivityRegression

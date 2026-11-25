import Integration.E6F3OrbitTransitivity

namespace Integration.E6F3OrbitTransitivityRegression

open Integration.E6F3OrbitTransitivity

example : nullOrbit = Finset.univ := null_orbit_full
example : q1Orbit = Finset.univ := q1_orbit_full
example : q2Orbit = Finset.univ := q2_orbit_full
example : nullOrbit.card = 80 := null_orbit_card
example : q1Orbit.card = 90 := q1_orbit_card
example : q2Orbit.card = 72 := q2_orbit_card
example : canonicalBoundary.nullOrbitTransitivePaid = true := rfl
example : canonicalBoundary.q1OrbitTransitivePaid = true := rfl
example : canonicalBoundary.q2OrbitTransitivePaid = true := rfl
example : canonicalBoundary.fullGeneratedGroupOrderNeededForTransitivity = false := rfl

end Integration.E6F3OrbitTransitivityRegression

import Integration.F3E6ProjectiveIncidenceDuality

namespace DASHI.Integration.F3E6ProjectiveIncidenceDualityRegression

open F3E6ProjectiveIncidenceDuality

example : projectiveLagrangianFinset.card = 40 := projectiveLagrangian_card
example : projectiveNullFinset.card = 40 := projectiveNull_card
example : standardProjectiveNullFinset.card = 40 := standardProjectiveNull_card
example : projectiveLagrangianFinset = projectiveNullFinset := projective_lagrangian_eq_null

example (p q : ProjectiveLagPoint) :
    lagIncidence p q ↔ nullOrthogonal (toProjectiveNull p) (toProjectiveNull q) :=
  lagIncidence_iff_nullOrthogonal p q

example (p q : ProjectiveLagPoint) :
    lagIncidence p q ↔
      standardNullOrthogonal (lagToStandardNull p) (lagToStandardNull q) :=
  lagIncidence_iff_standardNullOrthogonal p q

example (p : ProjectiveLagPoint) : standardNullToLag (lagToStandardNull p) = p :=
  standardNull_lag_roundTrip p

example (z : StandardProjectiveNullPoint) : lagToStandardNull (standardNullToLag z) = z :=
  lag_standardNull_roundTrip z

example (z : StandardProjectiveNullPoint) : (standardNeighbors z).card = 12 :=
  standard_degree12 z

example (x y : StandardProjectiveNullPoint) (hxy : x ≠ y) :
    standardAdjacent x y → (standardCommonNeighbors x y).card = 2 :=
  standard_adjacent_common2 x y hxy

example (x y : StandardProjectiveNullPoint) (hxy : x ≠ y) :
    ¬ standardAdjacent x y → (standardCommonNeighbors x y).card = 4 :=
  standard_nonadjacent_common4 x y hxy

example : incidenceBoundary.projectiveLagCount40Paid = true := rfl
example : incidenceBoundary.projectiveNullCount40Paid = true := rfl
example : incidenceBoundary.standardE6ProjectiveNullCount40Paid = true := rfl
example : incidenceBoundary.lagNullProjectiveSameObjectPaid = true := rfl
example : incidenceBoundary.standardE6ProjectiveEquivalencePaid = true := rfl
example : incidenceBoundary.incidenceOrthogonalityEquivalencePaid = true := rfl
example : incidenceBoundary.projectiveSRG401224Paid = true := rfl
example : incidenceBoundary.rawPuncturedT4PromotedToLagCarrier = false := rfl

end DASHI.Integration.F3E6ProjectiveIncidenceDualityRegression

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

example : incidenceBoundary.projectiveLagCount40Paid = true := rfl
example : incidenceBoundary.projectiveNullCount40Paid = true := rfl
example : incidenceBoundary.standardE6ProjectiveNullCount40Paid = true := rfl
example : incidenceBoundary.lagNullProjectiveSameObjectPaid = true := rfl
example : incidenceBoundary.standardE6ProjectiveEquivalencePaid = true := rfl
example : incidenceBoundary.incidenceOrthogonalityEquivalencePaid = true := rfl
example : incidenceBoundary.rawPuncturedT4PromotedToLagCarrier = false := rfl

end DASHI.Integration.F3E6ProjectiveIncidenceDualityRegression

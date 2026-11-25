import Integration.E6SelectedStabilizerFaceSameObject

namespace Integration.E6SelectedStabilizerFaceSameObjectRegression

open Integration.E6SelectedStabilizerFaceSameObject
open Integration.E6RootStabilizerA5SixSet
open Integration.E6F3GeneratedGroupClosure

example : alpha0Stabilizer.card = 720 := alpha0_stabilizer_card
example : synchronizedA5Graph.card = 720 := synchronized_graph_card
example : synchronizedMatrices = alpha0Stabilizer := synchronized_matrices_eq_alpha0_stabilizer
example : synchronizedTables = allSym6Tables := synchronized_tables_eq_sym6
example : q2SeedStabilizer.image conjugateSeedToAlpha0 = alpha0Stabilizer :=
  conjugated_old_stabilizer_eq_alpha0_stabilizer
example : canonicalBoundary.selectedMatrixFaceSameObjectPaid = true := rfl

end Integration.E6SelectedStabilizerFaceSameObjectRegression

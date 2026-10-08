import Integration.E6FullMatrixTernary27SameAction

namespace Integration.E6FullMatrixTernary27SameActionRegression

open Integration.E6FullMatrixTernary27SameAction
open Integration.E6F3GeneratedGroupClosure

example : fullSynchronizedGraph.card = 51840 := full_synchronized_graph_card
example : fullSynchronizedMatrices = generatedMatrixSet :=
  full_synchronized_matrices_eq_generated_e6
example : generatedPointTables.card = 51840 := generated_point_table_card
example : canonicalBoundary.fullPairedClosure51840Paid = true := rfl
example : canonicalBoundary.fullSameActionGraphBijectiveBothWaysPaid = true := rfl
example : canonicalBoundary.directA5LocalCheckRetained = true := rfl
example : canonicalBoundary.albertProductPaid = false := rfl
example : canonicalBoundary.monsterNormalizerRealizationPaid = false := rfl

end Integration.E6FullMatrixTernary27SameActionRegression

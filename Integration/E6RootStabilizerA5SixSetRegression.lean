import Integration.E6RootStabilizerA5SixSet

namespace Integration.E6RootStabilizerA5SixSetRegression

open Integration.E6RootStabilizerA5SixSet

example : Fintype.card Omega5Plus = 6 := omega5_plus_card
example : Fintype.card Omega5Zero = 15 := omega5_zero_card
example : Fintype.card Omega5Minus = 6 := omega5_minus_card
example : a5GeneratedTables.card = 720 := a5_generated_table_card
example : allSym6Tables.card = 720 := all_sym6_table_card
example : a5GeneratedTables = allSym6Tables := a5_generated_tables_are_exactly_sym6
example : canonicalBoundary.explicitA5SubsystemOrthogonalToRootPaid = true := rfl
example : canonicalBoundary.minusculeSixFifteenSixPaid = true := rfl
example : canonicalBoundary.sixSetGeneratedActionEqualsAllSym6Paid = true := rfl
example : canonicalBoundary.selectedQ2MatrixStabilizerSameObjectWeldPaid = false := rfl

end Integration.E6RootStabilizerA5SixSetRegression

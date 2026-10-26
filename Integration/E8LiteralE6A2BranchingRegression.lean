import Integration.E8LiteralE6A2Branching

namespace Integration.E8LiteralE6A2BranchingRegression

open Integration.E8LiteralE6A2Branching

example : e8ScaledDot a2SimpleA a2SimpleB = -4 := a2_simple_inner_product

example : Fintype.card LiteralE6Sector = 72 := literal_e6_sector_card
example : Fintype.card LiteralA2Sector = 6 := literal_a2_sector_card
example : Fintype.card LiteralMixedPlus = 81 := literal_mixed_plus_card
example : Fintype.card LiteralMixedMinus = 81 := literal_mixed_minus_card

example : Fintype.card E8ScaledRoot = 72 + 81 + 81 + 6 := literal_e8_branching_count
example : ∀ r, exactlyOneLiteralBranchSector r := literal_branch_sector_total

example : canonicalBoundary.literalE8Branching7281816Paid = true := rfl
example : canonicalBoundary.e6OrthogonalComplementCount72Paid = true := rfl
example : canonicalBoundary.branchingCountMatchCreatesTernarySectorEquivalence = false := rfl

end Integration.E8LiteralE6A2BranchingRegression

import Integration.E8E6A2TernaryBranchingCandidate

namespace Integration.E8E6A2TernaryBranchingCandidateRegression

open Integration.E6Mod3QuadraticBridge
open Integration.E8E6A2TernaryBranchingCandidate

example : Fintype.card SelectedAffinePlane = 9 := selected_affine_plane_card
example : Fintype.card SelectedAffineLine = 3 := selected_affine_line_card

example : ∀ z : SelectedAffinePlane, standardQuadratic z.1 = 1 :=
  selected_plane_lies_in_qone

example : Fintype.card E6Sector = 72 := e6_sector_card
example : Fintype.card MixedSectorA = 81 := mixed_sector_a_card
example : Fintype.card MixedSectorB = 81 := mixed_sector_b_card
example : Fintype.card A2Sector = 6 := a2_sector_card
example : Fintype.card SelectedLineSector = 3 := selected_line_sector_card

example : Fintype.card (TaggedSector .e6) = 72 := tagged_e6_card
example : Fintype.card (TaggedSector .mixedA) = 81 := tagged_mixed_a_card
example : Fintype.card (TaggedSector .mixedB) = 81 := tagged_mixed_b_card
example : Fintype.card (TaggedSector .a2) = 6 := tagged_a2_card
example : Fintype.card (TaggedSector .selectedLine) = 3 := tagged_selected_line_card

example : Fintype.card F3Five = 72 + 81 + 81 + 6 + 3 := full_branching_count
example : 240 = 72 + 81 + 81 + 6 := selected_line_removed_count

example : ∀ z, exactlyOneBranchSector z := branch_sector_total
example : selectedAffineLineDisjointFromOldDiagonal := selected_line_disjoint_old_diagonal

example : canonicalBoundary.exact243BranchingCountPaid = true := rfl
example : canonicalBoundary.exactTaggedPartitionPaid = true := rfl
example : canonicalBoundary.exact240AfterSelectedLineRemovalPaid = true := rfl
example : canonicalBoundary.branchingCountsCreateE8Recognition = false := rfl
example : canonicalBoundary.selectedLineEqualsOldDiagonalCut = false := rfl

end Integration.E8E6A2TernaryBranchingCandidateRegression

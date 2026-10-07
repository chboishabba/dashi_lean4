import Integration.E6F4WeylFold

namespace Integration.E6F4WeylFoldRegression

open Integration.E6F4WeylFold

example : foldedGeneratedSet.card = 1152 := folded_generated_card_1152
example : matrixOrbitN 25 = foldedGeneratedSet := folded_generated_stable
example : foldedNonzero24.card = 24 := folded_nonzero_card_24
example : foldedZero3.card = 3 := folded_zero_card_3
example : minusculeOmega5Set = foldedNonzero24 ∪ foldedZero3 :=
  omega5_eq_folded_24_union_3
example : foldedNonzeroLabelSet.card = 24 := folded_nonzero_labels_card_24
example : (0 : FoldedLabel) ∉ foldedNonzeroLabelSet := folded_nonzero_labels_exclude_zero
example : foldedOmega5LabelSet.card = 25 := folded_omega5_distinct_label_card_25
example : canonicalBoundary.continuousF4AutJordanPaidHere = false := rfl
example : canonicalBoundary.zeroWeightSpaceSplitTwoPlusOnePaidHere = false := rfl

end Integration.E6F4WeylFoldRegression

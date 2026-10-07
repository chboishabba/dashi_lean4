import Integration.E6F4ShortRootRecognition

namespace Integration.E6F4ShortRootRecognitionRegression

open Integration.E6F4ShortRootRecognition
open Integration.E6F4WeylFold

example : f4ShortRootSet.card = 24 := f4_short_root_card_24
example : f4LongRootSet.card = 24 := f4_long_root_card_24
example : f4RootSet.card = 48 := f4_root_card_48
example : foldedNonzeroLabelSet = f4ShortRootSet :=
  restricted_minuscule_nonzero_eq_f4_short_roots
example : foldedOmega5LabelSet = insert 0 f4ShortRootSet :=
  restricted_minuscule_distinct_weights_are_short_roots_plus_zero
example : canonicalBoundary.continuousAutJordanEqualsF4PaidHere = false := rfl

end Integration.E6F4ShortRootRecognitionRegression

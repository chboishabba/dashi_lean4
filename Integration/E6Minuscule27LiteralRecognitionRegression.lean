import Integration.E6Minuscule27LiteralRecognition

namespace Integration.E6Minuscule27LiteralRecognitionRegression

open Integration.E6Minuscule27LiteralRecognition

example : minusculeOmega0Set.card = 27 := minuscule_omega0_card
example : minusculeOmega5Set.card = 27 := minuscule_omega5_card
example : plus0LabelSet = minusculeOmega5Set := plus0_labels_eq_omega5
example : minus0LabelSet = minusculeOmega0Set := minus0_labels_eq_omega0
example : canonicalBoundary.plusThreeFibresRecognizedAsOmega5WeightOrbit = true := rfl
example : canonicalBoundary.minusThreeFibresRecognizedAsOmega0WeightOrbit = true := rfl
example : canonicalBoundary.albertJordanProductPaid = false := rfl
example : canonicalBoundary.bareTernary27SameObjectRecognitionPaid = false := rfl

end Integration.E6Minuscule27LiteralRecognitionRegression

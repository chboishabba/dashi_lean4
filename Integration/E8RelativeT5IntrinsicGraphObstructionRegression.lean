import Integration.E8RelativeT5IntrinsicGraphObstruction

namespace Integration.E8RelativeT5IntrinsicGraphObstructionRegression

open Integration.E8RelativeT5IntrinsicGraphObstruction

example : Fintype.card E8ScaledRoot = 240 := e8_scaled_root_card
example : ∀ r : E8ScaledRoot, Fintype.card (E8RootNeighbor r) = 56 :=
  e8_root_graph_degree

example : Fintype.card (RelativeOrthogonalNeighbor ternaryWitness) = 77 :=
  ternary_witness_orthogonal_degree

example : ¬ IntrinsicGraphRecognition :=
  intrinsic_graph_recognition_impossible

example : canonicalBoundary.e8RootGraphUniformDegree56Paid = true := rfl
example : canonicalBoundary.ternaryOrthogonalityWitnessDegree77Paid = true := rfl
example : canonicalBoundary.naiveOrthogonalityGraphRecognitionBlocked = true := rfl
example : canonicalBoundary.allPossibleTernaryE8RecognitionsBlocked = false := rfl

end Integration.E8RelativeT5IntrinsicGraphObstructionRegression

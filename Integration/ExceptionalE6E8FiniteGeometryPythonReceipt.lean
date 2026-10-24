import Integration.ExceptionalE6Mod3FiniteGeometry

/-!
# Local Python finite-geometry receipt

Evidence record only. None of the booleans below are promoted to Lean theorems
about E6/E8 actions. They record the exact finite computations reproduced after
the theorem target surface was written.
-/

namespace Integration.ExceptionalE6E8FiniteGeometryPythonReceipt

structure E6WeylComputationReceipt where
  generatedWeylMatrices : Nat
  expectedWeylOrder : Nat
  simpleReflectionNullFixedCount : Nat
  allSixSimpleReflectionsHaveSameNullFixedCount : Bool
  rootLineOrthogonalNeighborhoodSize : Nat
  orthogonalNeighborhoodIsKG62 : Bool
  localPythonReproduced : Bool
  provenance : String
  deriving Repr

def canonicalE6WeylComputationReceipt : E6WeylComputationReceipt where
  generatedWeylMatrices := 51840
  expectedWeylOrder := 51840
  simpleReflectionNullFixedCount := 20
  allSixSimpleReflectionsHaveSameNullFixedCount := true
  rootLineOrthogonalNeighborhoodSize := 15
  orthogonalNeighborhoodIsKG62 := true
  localPythonReproduced := true
  provenance := "six standard E6 simple reflections; mod-3 quotient BFS and graph isomorphism checked locally"

structure E8OrderThreeComputationReceipt where
  e8RootCount : Nat
  fixedRoots : Nat
  orderThreeOrbitCount : Nat
  orbitSize : Nat
  smithUnitFactors : Nat
  smithThreeFactors : Nat
  quotientDimensionOverF3 : Nat
  nonzeroQuotientClasses : Nat
  rootsPerNonzeroClass : Nat
  allNonzeroClassesHit : Bool
  localPythonReproduced : Bool
  provenance : String
  deriving Repr

def canonicalE8OrderThreeComputationReceipt : E8OrderThreeComputationReceipt where
  e8RootCount := 240
  fixedRoots := 0
  orderThreeOrbitCount := 80
  orbitSize := 3
  smithUnitFactors := 4
  smithThreeFactors := 4
  quotientDimensionOverF3 := 4
  nonzeroQuotientClasses := 80
  rootsPerNonzeroClass := 3
  allNonzeroClassesHit := true
  localPythonReproduced := true
  provenance := "fixed-point-free order-three E8 Weyl element built from four orthogonal A2 Coxeter factors; SNF(1-w)=1^4,3^4"

structure DualGeneralizedQuadrangleComputationReceipt where
  e6NullProjectivePoints : Nat
  e8SymplecticProjectivePoints : Nat
  e8SymplecticLines : Nat
  e6NullPointGraphIsomorphicToE8PointGraph : Bool
  e6NullPointGraphIsomorphicToE8LineIntersectionGraph : Bool
  localPythonReproduced : Bool
  provenance : String
  deriving Repr

def canonicalDualGeneralizedQuadrangleComputationReceipt :
    DualGeneralizedQuadrangleComputationReceipt where
  e6NullProjectivePoints := 40
  e8SymplecticProjectivePoints := 40
  e8SymplecticLines := 40
  e6NullPointGraphIsomorphicToE8PointGraph := false
  e6NullPointGraphIsomorphicToE8LineIntersectionGraph := true
  localPythonReproduced := true
  provenance := "Q(4,3) point graph matches the W(3,3) line-intersection graph, not its point graph"

structure T4LinearObstructionComputationReceipt where
  e6SimpleReflectionFixedSignedNullStates : Nat
  possibleLinearF3FourNonzeroFixedCounts : List Nat
  observedCountOccursInLinearList : Bool
  naiveLinearT4IdentificationSurvives : Bool
  provenance : String
  deriving Repr

def canonicalT4LinearObstructionComputationReceipt :
    T4LinearObstructionComputationReceipt where
  e6SimpleReflectionFixedSignedNullStates := 20
  possibleLinearF3FourNonzeroFixedCounts := [0,2,8,26,80]
  observedCountOccursInLinearList := false
  naiveLinearT4IdentificationSurvives := false
  provenance := "fixed vectors of a linear F3^4 map form a d-dimensional subspace, giving 3^d-1 nonzero fixed vectors"

end Integration.ExceptionalE6E8FiniteGeometryPythonReceipt

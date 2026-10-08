import Mathlib

/-!
# E8 root branching bridge to E6/Albert and E7/Freudenthal lanes

The standard E8 root system admits the familiar root-level splittings
corresponding to the maximal subgroups E6 x A2 and E7 x A1.  A dependency-free
Python audit in the Agda repository constructs the standard doubled-coordinate
240-root set and checks the literal sector sizes.

This owner records those exact execution results and keeps the representation
promotion boundary explicit: a 27-root or 56-root fibre is not automatically an
Albert 27 or Freudenthal 56 representation.  Action/intertwining still has to be
provided by the existing exceptional-recognition machinery.
-/

namespace Integration.E8ExceptionalBranchingBridge

structure E6A2RootSplit where
  e6Roots : Nat
  a2Roots : Nat
  positiveMixed : Nat
  negativeMixed : Nat
  fibresPerSign : Nat
  fibreSize : Nat
  deriving Repr

def canonicalE6A2 : E6A2RootSplit where
  e6Roots := 72
  a2Roots := 6
  positiveMixed := 81
  negativeMixed := 81
  fibresPerSign := 3
  fibreSize := 27

structure E7A1RootSplit where
  e7Roots : Nat
  a1Roots : Nat
  positiveMixed : Nat
  negativeMixed : Nat
  deriving Repr

def canonicalE7A1 : E7A1RootSplit where
  e7Roots := 126
  a1Roots := 2
  positiveMixed := 56
  negativeMixed := 56

 theorem e6_a2_root_arithmetic :
    240 = 72 + 6 + 3 * 27 + 3 * 27 := by norm_num

 theorem e6_a2_adjoint_arithmetic :
    248 = 78 + 8 + 3 * 27 + 3 * 27 := by norm_num

 theorem e7_a1_root_arithmetic :
    240 = 126 + 2 + 56 + 56 := by norm_num

 theorem e7_a1_adjoint_arithmetic :
    248 = 133 + 3 + 56 + 56 := by norm_num

structure Boundary where
  e6Root72SectorExecutable : Bool
  a2Root6SectorExecutable : Bool
  threeBy27FibresPerSignExecutable : Bool
  e7Root126SectorExecutable : Bool
  a1Root2SectorExecutable : Bool
  two56MixedFibresExecutable : Bool
  rootFibre27IsAlbertRepresentationHere : Bool
  rootFibre56IsFreudenthalRepresentationHere : Bool
  branchingCountCreatesExceptionalAction : Bool
  pythonExecutionCountsAsLeanKernelProof : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  e6Root72SectorExecutable := true
  a2Root6SectorExecutable := true
  threeBy27FibresPerSignExecutable := true
  e7Root126SectorExecutable := true
  a1Root2SectorExecutable := true
  two56MixedFibresExecutable := true
  rootFibre27IsAlbertRepresentationHere := false
  rootFibre56IsFreudenthalRepresentationHere := false
  branchingCountCreatesExceptionalAction := false
  pythonExecutionCountsAsLeanKernelProof := false

end Integration.E8ExceptionalBranchingBridge

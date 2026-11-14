import Synthesis.HolographicIndependentBellTree

namespace Synthesis.HolographicIndependentBellTreeRegression

open Synthesis.HolographicIndependentBellTree

example (k : ℕ) : Fintype.card (BitBasis k) = 2 ^ k := bitBasis_card k
example (k : ℕ) : Fintype.card (TreeCutBond k) = k := treeCutBond_card k
example (k : ℕ) :
    (canonicalTreeReplacement k).actualEntropy =
      (canonicalTreeReplacement k).actualCutEntropy := canonicalIndependentBellTreeRT k
example : concreteCorrectedTreeImplementationOwned = true := rfl
example : sourceModelInstantiationClosedForCorrectedTree = true := rfl

end Synthesis.HolographicIndependentBellTreeRegression

import Synthesis.HolographicUpstreamTensorSourceNoGo

namespace Synthesis.HolographicUpstreamTensorSourceNoGoRegression

open Synthesis.HolographicUpstreamTensorSourceNoGo

example : inspectedCanonicalTensor 0 (0,0) = 1 := by decide
example : inspectedCanonicalTensor 0 (0,1) = 0 := by decide
example : inspectedCanonicalTensor 1 (1,0) = 1 := by decide
example : inspectedCanonicalTensor 1 (1,1) = 0 := by decide

example (k child0 child1 : Fin 2) :
    inspectedCanonicalTensor k (child0, child1) ≠ 0 → child1 = 0 :=
  secondChildFixedZero

example : localTensorEntanglingSupportAbsent = true := rfl
example : upstreamTensorReplacementRequired = true := rfl

end Synthesis.HolographicUpstreamTensorSourceNoGoRegression

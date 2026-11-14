import Mathlib

namespace Synthesis.HolographicUpstreamTensorSourceNoGo

/-- Exact support pattern of the inspected upstream `canonicalQubitTensor`,
with coefficients projected to `Nat` because this module audits support rather
than complex amplitudes:

  T[(child0,child1), parent] = 1 iff child0 = parent and child1 = 0.

Hence the second output leg is fixed to the basis state zero whenever the tensor
has nonzero support. -/
def inspectedCanonicalTensor (parent : Fin 2) (children : Fin 2 × Fin 2) : ℕ :=
  if children.1 = parent ∧ children.2 = 0 then 1 else 0

/-- Any nonzero tensor coefficient forces the second child leg to zero. -/
theorem secondChildFixedZero
    (parent child0 child1 : Fin 2)
    (h : inspectedCanonicalTensor parent (child0, child1) ≠ 0) :
    child1 = 0 := by
  by_contra h1
  simp [inspectedCanonicalTensor, h1] at h

/-- Any nonzero tensor coefficient also copies the parent label only to the
first child. -/
theorem firstChildEqualsParent
    (parent child0 child1 : Fin 2)
    (h : inspectedCanonicalTensor parent (child0, child1) ≠ 0) :
    child0 = parent := by
  by_contra h0
  simp [inspectedCanonicalTensor, h0] at h

/-- The support therefore factorizes through a fixed second output basis leg.
This is an isometric embedding into `first-child ⊗ |0>` support, not a local
source of two-child Schmidt entanglement. -/
theorem supportFactorization
    (parent child0 child1 : Fin 2)
    (h : inspectedCanonicalTensor parent (child0, child1) ≠ 0) :
    child0 = parent ∧ child1 = 0 :=
  ⟨firstChildEqualsParent parent child0 child1 h,
   secondChildFixedZero parent child0 child1 h⟩

/-- Source-audit status.  This theorem does not claim that every possible tree
built from other tensors is non-entangling.  It says the particular inspected
canonical tensor has fixed-zero support on its second child and therefore cannot
by itself supply the `k` independent Schmidt bonds of the corrected RT model. -/
def localTensorEntanglingSupportAbsent : Bool := true

def inspectedCanonicalTensorIsOnlyParentChildIsometry : Bool := true

def upstreamTensorReplacementRequired : Bool := true

def correctedKBondNetworkStillDistinctFromInspectedTensor : Bool := true

end Synthesis.HolographicUpstreamTensorSourceNoGo

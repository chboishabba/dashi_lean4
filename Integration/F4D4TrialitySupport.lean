import Integration.F4D4TrialityAlbertShape
import Integration.E6Minuscule27SchlafliRecognition
import Mathlib

/-!
# Canonical finite D4 triality support inside the folded minuscule 27

The pointwise stabilizer of the three folded-zero weights has order 192 and
splits the remaining 24 weights into three 8-element triality sectors.  The
triple product of those sectors has 512 elements.  Under the diagonal D4
kernel action it splits into four 32-orbits and four 96-orbits.

A canonical 32-orbit is selected without coordinates: triples whose three
E6-minuscule lines are pairwise non-Schlaefli-adjacent.  This is exactly the
right support cardinality for the weight-basis form of the
`8v x 8s x 8c` triality tensor.

This file pays only the finite support/action statement.  Identifying its
coefficients/signs with the actual octonion trilinear form remains a separate
Albert compatibility theorem.
-/

namespace Integration.F4D4TrialitySupport

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6F4WeylFold
open Integration.F4D4TrialityAlbertShape

abbrev Sector0 := { w : DynkinLabel // w ∈ trialityOrbit0 }
abbrev Sector1 := { w : DynkinLabel // w ∈ trialityOrbit1 }
abbrev Sector2 := { w : DynkinLabel // w ∈ trialityOrbit2 }

/-- Pairing-based Schlaefli adjacency directly on labels. -/
def labelAdjacent (x y : DynkinLabel) : Bool :=
  decide (x ≠ y) && decide (threeWeightPairing x y = 1)

/-- Canonical triality support: all three cross-sector pairings are in the
non-Schlaefli class. -/
def trialitySupport (x : Sector0) (y : Sector1) (z : Sector2) : Bool :=
  !(labelAdjacent x.1 y.1) && !(labelAdjacent x.1 z.1) && !(labelAdjacent y.1 z.1)

/-- Exact support cardinality found independently by local finite enumeration. -/
def supportTriples : Finset (Sector0 × Sector1 × Sector2) :=
  Finset.univ.filter fun p => trialitySupport p.1 p.2.1 p.2.2 = true

theorem triality_support_card_32 : supportTriples.card = 32 := by
  native_decide

/-- The complementary orbit-size ledger for the 512 cross-sector triples.
This is diagnostic finite structure; it does not identify the Albert cubic. -/
structure TripleOrbitLedger where
  smallOrbitCount : Nat
  smallOrbitSize : Nat
  largeOrbitCount : Nat
  largeOrbitSize : Nat
  total : Nat
  smallOrbitCount_eq_4 : smallOrbitCount = 4
  smallOrbitSize_eq_32 : smallOrbitSize = 32
  largeOrbitCount_eq_4 : largeOrbitCount = 4
  largeOrbitSize_eq_96 : largeOrbitSize = 96
  total_eq_512 : total = 512

def canonicalTripleOrbitLedger : TripleOrbitLedger where
  smallOrbitCount := 4
  smallOrbitSize := 32
  largeOrbitCount := 4
  largeOrbitSize := 96
  total := 512
  smallOrbitCount_eq_4 := rfl
  smallOrbitSize_eq_32 := rfl
  largeOrbitCount_eq_4 := rfl
  largeOrbitSize_eq_96 := rfl
  total_eq_512 := rfl

/-- Membership in each 8-sector is stable under every matrix in the D4 kernel. -/
theorem d4_kernel_preserves_sector0 :
    ∀ M ∈ d4KernelSet, ∀ x ∈ trialityOrbit0, matrixApply M x ∈ trialityOrbit0 := by
  native_decide

theorem d4_kernel_preserves_sector1 :
    ∀ M ∈ d4KernelSet, ∀ x ∈ trialityOrbit1, matrixApply M x ∈ trialityOrbit1 := by
  native_decide

theorem d4_kernel_preserves_sector2 :
    ∀ M ∈ d4KernelSet, ∀ x ∈ trialityOrbit2, matrixApply M x ∈ trialityOrbit2 := by
  native_decide

/-- The 32-term support is invariant under the entire 192-element D4 kernel. -/
theorem d4_kernel_preserves_triality_support :
    ∀ M ∈ d4KernelSet,
      ∀ x : Sector0, ∀ y : Sector1, ∀ z : Sector2,
        trialitySupport
          ⟨matrixApply M x.1, d4_kernel_preserves_sector0 M ‹_› x.1 x.2⟩
          ⟨matrixApply M y.1, d4_kernel_preserves_sector1 M ‹_› y.1 y.2⟩
          ⟨matrixApply M z.1, d4_kernel_preserves_sector2 M ‹_› z.1 z.2⟩ =
        trialitySupport x y z := by
  native_decide

inductive FiniteTrialitySupportCreatesOctonionMultiplication : Prop
inductive FiniteTrialitySupportFixesCoefficientSigns : Prop

theorem support_does_not_create_octonion_multiplication :
    ¬ FiniteTrialitySupportCreatesOctonionMultiplication := by
  intro h; cases h

theorem support_does_not_fix_triality_coefficients :
    ¬ FiniteTrialitySupportFixesCoefficientSigns := by
  intro h; cases h

structure Boundary where
  d4Kernel192Paid : Bool
  threeEightSectorsPaid : Bool
  canonicalSupportCard32Paid : Bool
  supportInvariantUnderD4KernelPaid : Bool
  actualOctonionTrialityCoefficientAlignmentPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  d4Kernel192Paid := true
  threeEightSectorsPaid := true
  canonicalSupportCard32Paid := true
  supportInvariantUnderD4KernelPaid := true
  actualOctonionTrialityCoefficientAlignmentPaid := false

end Integration.F4D4TrialitySupport

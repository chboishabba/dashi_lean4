import Mathlib
import Integration.TriadicPAdicKernel
import Integration.OggSSPP2BalancedTernaryPuncturedPlane
import Integration.OggSSPP2PuncturedKernel2Bidi

/-!
# p=2 target <-> trialectic nine-observer reconciliation

The p=2 ten-state target collapses to a two-trit nine carrier.  The pre-RH
trialectic local observer also targets a two-trit nine carrier.  This module
pays the shared finite theorem on this branch without importing the newer
trialectic observer implementation:

  Kernel 2 ≃ PhaseNine := Trit × Trit

and identifies the punctured p=2 conjugate fibre with the noncentral
PhaseNine subtype.

Global sign inversion intertwines exactly.
-/

namespace Integration.OggSSPP2TrialecticNineObserverReconciliation

open Integration.BalancedTernaryAntipodal369OrbitHierarchy
open Integration.TriadicPAdicKernel
open Integration.OggSSPP2BalancedTernaryPuncturedPlane
open Integration.OggSSPP2PuncturedKernel2Bidi

abbrev PhaseNine := Trit × Trit

def kernel2ToPhaseNine (x : Kernel2) : PhaseNine :=
  (x 0, x 1)

def phaseNineToKernel2 (x : PhaseNine) : Kernel2 :=
  ![x.1, x.2]

theorem kernel_phase_roundtrip (x : Kernel2) :
    phaseNineToKernel2 (kernel2ToPhaseNine x) = x := by
  funext i
  fin_cases i <;> rfl

theorem phase_kernel_roundtrip (x : PhaseNine) :
    kernel2ToPhaseNine (phaseNineToKernel2 x) = x := by
  rcases x with ⟨a,b⟩
  rfl

def kernel2EquivPhaseNine : Kernel2 ≃ PhaseNine where
  toFun := kernel2ToPhaseNine
  invFun := phaseNineToKernel2
  left_inv := kernel_phase_roundtrip
  right_inv := phase_kernel_roundtrip

def duplicatedCentreToPhaseNine :
    DuplicatedCentreNineSheet → PhaseNine :=
  collapseDuplicatedCentre

theorem both_centres_become_phase_origin :
    duplicatedCentreToPhaseNine .lowerCentre =
      duplicatedCentreToPhaseNine .upperCentre := rfl

theorem lower_centre_becomes_zero_zero :
    duplicatedCentreToPhaseNine .lowerCentre = (.zero,.zero) := rfl

theorem upper_centre_becomes_zero_zero :
    duplicatedCentreToPhaseNine .upperCentre = (.zero,.zero) := rfl

def PuncturedPhaseNine :=
  {x : PhaseNine // x ≠ (.zero,.zero)}

def puncturedKernel2ToPhaseNine
    (x : PuncturedKernel2) : PuncturedPhaseNine :=
  ⟨kernel2ToPhaseNine x.1, by
    intro h
    apply x.2
    apply kernel_phase_roundtrip x.1 ▸ congrArg phaseNineToKernel2 h
  ⟩

def puncturedPhaseNineToKernel2
    (x : PuncturedPhaseNine) : PuncturedKernel2 :=
  ⟨phaseNineToKernel2 x.1, by
    intro h
    apply x.2
    have := congrArg kernel2ToPhaseNine h
    simpa [origin, kernel2ToPhaseNine] using this
  ⟩

theorem punctured_kernel_phase_roundtrip
    (x : PuncturedKernel2) :
    puncturedPhaseNineToKernel2 (puncturedKernel2ToPhaseNine x) = x := by
  apply Subtype.ext
  exact kernel_phase_roundtrip x.1

theorem punctured_phase_kernel_roundtrip
    (x : PuncturedPhaseNine) :
    puncturedKernel2ToPhaseNine (puncturedPhaseNineToKernel2 x) = x := by
  apply Subtype.ext
  exact phase_kernel_roundtrip x.1

def puncturedKernel2EquivPuncturedPhaseNine :
    PuncturedKernel2 ≃ PuncturedPhaseNine where
  toFun := puncturedKernel2ToPhaseNine
  invFun := puncturedPhaseNineToKernel2
  left_inv := punctured_kernel_phase_roundtrip
  right_inv := punctured_phase_kernel_roundtrip

def negatePhaseNine (x : PhaseNine) : PhaseNine :=
  (antipode x.1, antipode x.2)

theorem kernel2_phase_negation_intertwines (x : Kernel2) :
    kernel2ToPhaseNine (invert x) =
      negatePhaseNine (kernel2ToPhaseNine x) := by
  rfl

theorem negate_phase_nine_involutive (x : PhaseNine) :
    negatePhaseNine (negatePhaseNine x) = x := by
  rcases x with ⟨a,b⟩
  cases a <;> cases b <;> rfl

structure Boundary where
  kernel2ToPhaseNineBidiPaid : Bool
  duplicatedCentreTenCollapsesToPhaseNine : Bool
  puncturedKernel2EqualsNoncentralPhaseSector : Bool
  signedC2IntertwinerPaid : Bool
  arithmeticRecognitionClaimed : Bool
  monsterOrFrickeRecognitionClaimed : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  kernel2ToPhaseNineBidiPaid := true
  duplicatedCentreTenCollapsesToPhaseNine := true
  puncturedKernel2EqualsNoncentralPhaseSector := true
  signedC2IntertwinerPaid := true
  arithmeticRecognitionClaimed := false
  monsterOrFrickeRecognitionClaimed := false

end Integration.OggSSPP2TrialecticNineObserverReconciliation

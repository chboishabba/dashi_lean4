import Mathlib
import CondensedMatter.MajoranaOperatorKernelExact
import CondensedMatter.MajoranaParityQubitExact

/-!
# Charged Dirac U(1) sector versus four-Majorana parity code

DASHI physical-source guard: the two fermionic occupations in the abstract
four-Majorana even-parity basis |00>,|11> have distinct U(1) charges 0 and 2
if modeled by two ordinary charged complex Dirac modes. Fermion-parity
conservation is weaker than charged-sector coherence.

A charge-half-turn θ=π/2 acts as diag(1,-1) on that even-parity basis.
A U(1)-invariant reduced density matrix consequently has no coherence between
the charge-0 and charge-2 basis states. This is a mathematical conditional
superselection/charge-reference observation; NOT proof that superconducting
Majorana systems cannot supply a compensating condensate/reference.

The one-particle dual-rail basis |10>,|01> instead has total charge 1 in both
components, so an ordinary global gauge phase acts by a common scalar.
No physical MMP spin-c state, detector or gravitating topology is inferred.
-/

namespace MMPQuantumChannel

open CondensedMatter

/-- A selected U(1) element on ordinary charged complex-fermion Fock
logical states |00>,|11>, whose relative charges differ by two. -/
def chargedEvenHalfTurn : CMatrix2 := ⟨1, 0, 0, -1⟩

def chargedEvenHalfTurnConjugate (rho : CMatrix2) : CMatrix2 :=
  CMatrix2.mul (CMatrix2.mul chargedEvenHalfTurn rho) chargedEvenHalfTurn

theorem chargedEvenHalfTurn_offDiagonal (rho : CMatrix2) :
    (chargedEvenHalfTurnConjugate rho).a12 = -rho.a12 := by
  simp [chargedEvenHalfTurnConjugate, chargedEvenHalfTurn, CMatrix2.mul]

/-- One *necessary* U(1) covariance test: invariance under the
charge-half-turn already forces coherence between |00> and |11> to vanish.
Unlike a flag-only status claim, the conclusion is exact complex arithmetic. -/
theorem chargedEvenHalfTurn_invariant_offDiagonal_zero
    (rho : CMatrix2)
    (h : chargedEvenHalfTurnConjugate rho = rho) :
    rho.a12 = 0 := by
  have hh : -rho.a12 = rho.a12 := by
    calc
      -rho.a12 = (chargedEvenHalfTurnConjugate rho).a12 :=
        (chargedEvenHalfTurn_offDiagonal rho).symm
      _ = rho.a12 := congrArg CMatrix2.a12 h
  have htwo : (-2 : ℂ) * rho.a12 = 0 := by
    calc
      (-2 : ℂ) * rho.a12 = -rho.a12 - rho.a12 := by ring
      _ = 0 := sub_eq_zero.mpr hh
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The same selected U(1) phase is a *common* phase on both one-particle
dual-rail |10>,|01> basis states, and so preserves their relative coherence. -/
theorem equalChargeDualRail_coherence_preserved (z : ℂ) :
    (-1 : ℂ) * z * (-1) = z := by ring

/-- A named observer distinguishes abstract parity geometry from source
charge-gauge realizability. No field-theoretic Gauss-law representation or
physical charge reservoir is constructed by this small exact theorem. -/
structure ChargePromotionBoundary where
  mergedMajoranaParityBasisMathematics : Bool := true
  ordinaryDiracChargeDifferenceTwo : Bool := true
  selectedChargeHalfTurnNoCoherence : Bool := true
  physicalChargeReferenceOrDressingConstructed : Bool := false
  sameObjectMMPSpinCChargeOperator : Bool := false
  physicalFourDimensionalFockScattering : Bool := false
  deriving Repr

def canonicalChargeBoundary : ChargePromotionBoundary := {}

theorem actualChargeReferenceOpen :
    canonicalChargeBoundary.physicalChargeReferenceOrDressingConstructed =
      false := rfl

end MMPQuantumChannel

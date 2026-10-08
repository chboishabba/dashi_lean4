import Integration.F4D4TrialitySupport
import Integration.F4MinusculeOnePlus26
import Mathlib

/-!
# Finite Albert cubic tensor on the minuscule weight basis

Using only already-paid finite data, define the commutative degree-three
coefficient tensor with the Albert shape

  abc - a ||8v||^2 - b ||8c||^2 - c ||8s||^2 + 2 T(8v,8s,8c).

The pairing of the three diagonal folded-zero lines with the three triality
sectors is forced by equivariance under the two S3 generators:

  zero0 <-> sector0,
  zero1 <-> sector2,
  zero2 <-> sector1.

`T` uses the canonical 32-term D4 triality support.  The object below is only a
finite coefficient tensor.  Equality with the actual octonionic Albert cubic is
still an explicit same-object normalization/sign theorem.
-/

namespace Integration.F4FiniteAlbertCubicTensor

open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6F4WeylFold
open Integration.F4MinusculeOnePlus26
open Integration.F4D4TrialityAlbertShape
open Integration.F4D4TrialitySupport

abbrev MonomialKey := Omega5Weight → Fin 4

/-- Commutative monomial key for degree three, represented by multiplicities. -/
def monomial3 (a b c : Omega5Weight) : MonomialKey := fun w =>
  ⟨(if w = a then 1 else 0) + (if w = b then 1 else 0) +
      (if w = c then 1 else 0), by
    omega⟩

structure CubicTerm where
  coefficient : Int
  monomial : MonomialKey
  deriving DecidableEq

/-- The unique diagonal cubic monomial. -/
def diagonalTerm : CubicTerm :=
  ⟨1, monomial3 zeroWeight0 zeroWeight1 zeroWeight2⟩

/-- Norm terms paired equivariantly with the three zero-weight lines. -/
def normTerm0 (w : Sector0) : CubicTerm :=
  ⟨-1, monomial3 zeroWeight0 ⟨w.1, by native_decide⟩ ⟨w.1, by native_decide⟩⟩

def normTerm1 (w : Sector1) : CubicTerm :=
  ⟨-1, monomial3 zeroWeight2 ⟨w.1, by native_decide⟩ ⟨w.1, by native_decide⟩⟩

def normTerm2 (w : Sector2) : CubicTerm :=
  ⟨-1, monomial3 zeroWeight1 ⟨w.1, by native_decide⟩ ⟨w.1, by native_decide⟩⟩

/-- One coefficient-two triality monomial. -/
def trialityTerm (p : Sector0 × Sector1 × Sector2) : CubicTerm :=
  ⟨2, monomial3
      ⟨p.1.1, by native_decide⟩
      ⟨p.2.1.1, by native_decide⟩
      ⟨p.2.2.1, by native_decide⟩⟩

/-- Complete finite coefficient tensor. -/
def finiteAlbertCubicTerms : Finset CubicTerm :=
  {diagonalTerm} ∪
  Finset.univ.image normTerm0 ∪
  Finset.univ.image normTerm1 ∪
  Finset.univ.image normTerm2 ∪
  supportTriples.image trialityTerm

/-- One diagonal + 24 norm + 32 triality monomials. -/
theorem finite_albert_cubic_term_card_57 : finiteAlbertCubicTerms.card = 57 := by
  native_decide

/-- Folded action on a commutative monomial key.  All four generators are
involutions on the minuscule carrier, so pullback is the same as pushforward. -/
def foldMonomial (g : FoldGenerator) (m : MonomialKey) : MonomialKey :=
  fun w => m (foldOmega5 g w)

def foldTerm (g : FoldGenerator) (t : CubicTerm) : CubicTerm :=
  ⟨t.coefficient, foldMonomial g t.monomial⟩

/-- Exact coefficient-level invariance of the full finite cubic tensor under
all four folded F4 generators. -/
theorem folded_generators_preserve_finite_cubic_terms :
    ∀ g, finiteAlbertCubicTerms.image (foldTerm g) = finiteAlbertCubicTerms := by
  native_decide

/-- The diagonal/sector pairing used above is itself the unique bijection of the
three diagonal lines with the three 8-sectors compatible with both triality
transpositions. -/
def diagonalSectorPairing : Fin 3 → Fin 3 := ![0,2,1]

theorem diagonal_sector_pairing_equivariant :
    (∀ i, diagonalSectorPairing (zeroPerm .g05 i) =
      (![2,1,0] : Fin 3 → Fin 3) (diagonalSectorPairing i)) ∧
    (∀ i, diagonalSectorPairing (zeroPerm .g24 i) =
      (![0,2,1] : Fin 3 → Fin 3) (diagonalSectorPairing i)) := by
  native_decide

inductive FiniteCubicTensorIsActualAlbertCubic : Prop

theorem finite_tensor_not_promoted_to_actual_albert_cubic :
    ¬ FiniteCubicTensorIsActualAlbertCubic := by
  intro h; cases h

structure Boundary where
  finiteCubicCoefficientTensorPaid : Bool
  termCount57Paid : Bool
  fourFoldedGeneratorCoefficientInvariancePaid : Bool
  diagonalSectorEquivariantPairingPaid : Bool
  actualOctonionCoefficientAlignmentPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteCubicCoefficientTensorPaid := true
  termCount57Paid := true
  fourFoldedGeneratorCoefficientInvariancePaid := true
  diagonalSectorEquivariantPairingPaid := true
  actualOctonionCoefficientAlignmentPaid := false

end Integration.F4FiniteAlbertCubicTensor

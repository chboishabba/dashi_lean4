import Integration.T5E8RelativeComplementCandidate
import Mathlib

/-!
# Projective five-trit geometry versus E8 root-line geometry

DASHI finite obstruction layer.

Quotienting the 240 non-diagonal five-trit states by sign gives 120 canonical
projective representatives.  E8 likewise has 120 root lines after identifying
`r ~ -r`.  Cardinality still does not identify the geometries.

The most immediate native ternary candidate is a rotation-invariant symmetric
bilinear form on `F_3^5`.  Every such circulant form is determined by three
coefficients `(a,b,c)`, hence there are exactly 27.  This file exhausts all 27
forms on the literal projective T5 carrier and checks both natural adjacency
relations, `B(x,y)=0` and `B(x,y)≠0`.

The E8 root-line nonorthogonality graph has valency 56.  No member of this entire
27-form family makes either relation 56-regular on ProjectiveRelativeT5.  Thus
the missing E8 geometry cannot be obtained merely by choosing a symmetric C5-
invariant bilinear form over the already-existing five balanced ternary digits.
-/

namespace Integration.T5E8ProjectiveGeometry

open Integration.TrialecticDyadicLocalComplement
open Integration.TernaryHub
open Integration.T5E8RelativeComplementCandidate

/-- Canonical sign representative: the first nonzero trit is positive. -/
def firstNonzeroPositive : T5Carrier → Bool
  | ⟨.negOne, _, _, _, _⟩ => false
  | ⟨.posOne, _, _, _, _⟩ => true
  | ⟨.zero, .negOne, _, _, _⟩ => false
  | ⟨.zero, .posOne, _, _, _⟩ => true
  | ⟨.zero, .zero, .negOne, _, _⟩ => false
  | ⟨.zero, .zero, .posOne, _, _⟩ => true
  | ⟨.zero, .zero, .zero, .negOne, _⟩ => false
  | ⟨.zero, .zero, .zero, .posOne, _⟩ => true
  | ⟨.zero, .zero, .zero, .zero, .negOne⟩ => false
  | ⟨.zero, .zero, .zero, .zero, .posOne⟩ => true
  | ⟨.zero, .zero, .zero, .zero, .zero⟩ => false

/-- One representative from every sign pair in the non-diagonal T5 carrier. -/
def ProjectiveRelativeT5 :=
  {x : RelativeT5Carrier // firstNonzeroPositive x.1 = true}

instance : Fintype ProjectiveRelativeT5 := inferInstance
instance : DecidableEq ProjectiveRelativeT5 := inferInstance

theorem projective_relative_t5_count :
    Fintype.card ProjectiveRelativeT5 = 120 := by
  native_decide

/-- All symmetric 5x5 circulant matrices over F3.  The first row is
`(a,b,c,c,b)`. -/
structure SymmetricCirculant5 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  deriving DecidableEq, Repr, Fintype

theorem symmetric_circulant5_count :
    Fintype.card SymmetricCirculant5 = 27 := by
  native_decide

private def q4 (x : ProjectiveRelativeT5) : ZMod 3 := balSSP x.1.1.d4
private def q3 (x : ProjectiveRelativeT5) : ZMod 3 := balSSP x.1.1.d3
private def q2 (x : ProjectiveRelativeT5) : ZMod 3 := balSSP x.1.1.d2
private def q1 (x : ProjectiveRelativeT5) : ZMod 3 := balSSP x.1.1.d1
private def q0 (x : ProjectiveRelativeT5) : ZMod 3 := balSSP x.1.1.d0

/-- The complete symmetric C5-invariant bilinear family on the five balanced
coordinates. -/
def circulantPairing
    (m : SymmetricCirculant5)
    (x y : ProjectiveRelativeT5) : ZMod 3 :=
  m.a *
      (q4 x * q4 y + q3 x * q3 y + q2 x * q2 y + q1 x * q1 y + q0 x * q0 y)
  + m.b *
      (q4 x * (q3 y + q0 y)
       + q3 x * (q2 y + q4 y)
       + q2 x * (q1 y + q3 y)
       + q1 x * (q0 y + q2 y)
       + q0 x * (q4 y + q1 y))
  + m.c *
      (q4 x * (q2 y + q1 y)
       + q3 x * (q1 y + q0 y)
       + q2 x * (q0 y + q4 y)
       + q1 x * (q4 y + q3 y)
       + q0 x * (q3 y + q2 y))

def zeroRelationDegree
    (m : SymmetricCirculant5) (x : ProjectiveRelativeT5) : Nat :=
  (Finset.univ.filter fun y : ProjectiveRelativeT5 =>
    y ≠ x ∧ circulantPairing m x y = 0).card

def nonzeroRelationDegree
    (m : SymmetricCirculant5) (x : ProjectiveRelativeT5) : Nat :=
  (Finset.univ.filter fun y : ProjectiveRelativeT5 =>
    y ≠ x ∧ circulantPairing m x y ≠ 0).card

/-- The exact finite obstruction discovered by the Python preflight and stated
here on the literal carrier: no symmetric circulant F3 bilinear form has either
its orthogonality or nonorthogonality graph 56-regular. -/
def noCirculantCandidateHasE8Valency : Prop :=
  ∀ m : SymmetricCirculant5,
    ¬ ((∀ x : ProjectiveRelativeT5, zeroRelationDegree m x = 56) ∨
       (∀ x : ProjectiveRelativeT5, nonzeroRelationDegree m x = 56))

theorem no_circulant_candidate_has_e8_valency :
    noCirculantCandidateHasE8Valency := by
  native_decide

inductive CirculantBilinearFormCreatesE8Geometry : Prop

theorem circulantBilinearFormCannotCreateE8Geometry :
    ¬ CirculantBilinearFormCreatesE8Geometry := by
  intro h
  cases h

structure Boundary where
  projectiveRelativeCount120Paid : Bool
  symmetricCirculantFamily27Typed : Bool
  exhaustiveValencyObstructionSourceWritten : Bool
  pythonExhaustiveAuditPassed : Bool
  e8Valency56CandidateFound : Bool
  simpleCirculantBilinearGeometrySurvives : Bool
  fullE8GeometryRecognized : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  projectiveRelativeCount120Paid := true
  symmetricCirculantFamily27Typed := true
  exhaustiveValencyObstructionSourceWritten := true
  pythonExhaustiveAuditPassed := true
  e8Valency56CandidateFound := false
  simpleCirculantBilinearGeometrySurvives := false
  fullE8GeometryRecognized := false

end Integration.T5E8ProjectiveGeometry

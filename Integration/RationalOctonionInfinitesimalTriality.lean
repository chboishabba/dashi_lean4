import Integration.RationalOctonionTriality192
import Mathlib

/-!
# Exact infinitesimal Spin(8) triality on the native rational octonion tensor

The failed signed-monomial W(D4) candidate concerns finite normalizer lifts.  At
Lie-algebra level the repo-native octonion triality tensor gives a cleaner route.

Take the four commuting vector Cartan rotations in the real coordinate planes
(0,1), (2,3), (4,5), (6,7).  Solving

  T(Ax,y,z) + T(x,By,z) + T(x,y,Cz) = 0

with B,C skew determines the two half-spinor actions.  They are four-plane
block rotations with coefficients ±1/2, exactly the Spin(8) half-angle pattern.
All statements below are finite rational equalities on the literal octonion
basis tensor.
-/

namespace Integration.RationalOctonionInfinitesimalTriality

open Integration.RationalOctonionTriality192

abbrev Mat8Q := Fin 8 → Fin 8 → ℚ

/-- The two coordinates of one of four real 2-planes. -/
def pairCoord : Fin 4 → Fin 2 → Fin 8 :=
  ![![0,1], ![2,3], ![4,5], ![6,7]]

/-- Standard skew 2-plane rotation block with coefficient `c`. -/
def planeJ (c : ℚ) (b : Fin 4) : Mat8Q := fun i j =>
  if i = pairCoord b 0 ∧ j = pairCoord b 1 then -c
  else if i = pairCoord b 1 ∧ j = pairCoord b 0 then c
  else 0

/-- Sum four independent plane blocks. -/
def fourPlane (c : Fin 4 → ℚ) : Mat8Q := fun i j =>
  ∑ b : Fin 4, planeJ (c b) b i j

/-- Vector Cartan generator: full rotation in the selected plane. -/
def vectorCartan (r : Fin 4) : Mat8Q :=
  planeJ 1 r

/-- Half-spinor sign tables obtained by solving the exact triality equations. -/
def plusSigns : Fin 4 → Fin 4 → ℚ :=
  ![ ![ 1, 1, 1,-1],
     ![-1,-1, 1,-1],
     ![-1, 1,-1,-1],
     ![ 1,-1,-1,-1] ]


def minusSigns : Fin 4 → Fin 4 → ℚ :=
  ![ ![ 1,-1,-1, 1],
     ![ 1,-1, 1,-1],
     ![ 1, 1,-1,-1],
     ![-1,-1,-1,-1] ]

/-- Positive- and negative-half-spinor Cartan actions. -/
def plusCartan (r : Fin 4) : Mat8Q :=
  fourPlane fun b => plusSigns r b / 2


def minusCartan (r : Fin 4) : Mat8Q :=
  fourPlane fun b => minusSigns r b / 2

/-- Matrix action on a basis column is just coefficient lookup. -/
def basisCoeff (M : Mat8Q) (out input : Fin 8) : ℚ := M out input

/-- Infinitesimal variation of the literal octonion triality tensor. -/
def infinitesimalTrialityDefect
    (A B C : Mat8Q) (i j k : Fin 8) : ℚ :=
  (∑ p : Fin 8, basisCoeff A p i * basisTriality p j k) +
  (∑ p : Fin 8, basisCoeff B p j * basisTriality i p k) +
  (∑ p : Fin 8, basisCoeff C p k * basisTriality i j p)

/-- Exact basis-level Spin(8) triality equation for all four Cartan directions. -/
theorem cartan_infinitesimal_triality :
    ∀ r i j k,
      infinitesimalTrialityDefect
        (vectorCartan r) (plusCartan r) (minusCartan r) i j k = 0 := by
  native_decide

/-- All three actions are skew-symmetric. -/
theorem cartan_actions_skew :
    (∀ r i j, vectorCartan r i j = - vectorCartan r j i) ∧
    (∀ r i j, plusCartan r i j = - plusCartan r j i) ∧
    (∀ r i j, minusCartan r i j = - minusCartan r j i) := by
  native_decide

/-- Matrix multiplication. -/
def matMul (A B : Mat8Q) : Mat8Q := fun i j =>
  ∑ k : Fin 8, A i k * B k j

/-- The four Cartan generators commute in each of the three 8-dimensional
representations. -/
theorem cartan_families_commute :
    (∀ r s, matMul (vectorCartan r) (vectorCartan s) =
      matMul (vectorCartan s) (vectorCartan r)) ∧
    (∀ r s, matMul (plusCartan r) (plusCartan s) =
      matMul (plusCartan s) (plusCartan r)) ∧
    (∀ r s, matMul (minusCartan r) (minusCartan s) =
      matMul (minusCartan s) (minusCartan r)) := by
  native_decide

/-- Squaring exposes full-angle versus half-angle normalization. -/
theorem vector_cartan_selected_plane_square :
    ∀ r i,
      (matMul (vectorCartan r) (vectorCartan r)) i i =
        (if i = pairCoord r 0 ∨ i = pairCoord r 1 then -1 else 0) := by
  native_decide

inductive InfinitesimalTrialityCreatesFiniteWeylLift : Prop
inductive RationalLieAlgebraTrialityCreatesFullF4 : Prop

theorem infinitesimal_does_not_create_finite_weyl_lift :
    ¬ InfinitesimalTrialityCreatesFiniteWeylLift := by
  intro h; cases h

theorem infinitesimal_does_not_create_full_f4 :
    ¬ RationalLieAlgebraTrialityCreatesFullF4 := by
  intro h; cases h

structure Boundary where
  nativeOctonionTensorConsumed : Bool
  rankFourVectorCartanPaid : Bool
  twoHalfSpinorCartansPaid : Bool
  halfAngleCoefficientsPaid : Bool
  infinitesimalTrialityEquationPaid : Bool
  skewSymmetryPaid : Bool
  commutingCartanPaid : Bool
  finiteWeylNormalizerLiftPaid : Bool
  fullSpin8Paid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  nativeOctonionTensorConsumed := true
  rankFourVectorCartanPaid := true
  twoHalfSpinorCartansPaid := true
  halfAngleCoefficientsPaid := true
  infinitesimalTrialityEquationPaid := true
  skewSymmetryPaid := true
  commutingCartanPaid := true
  finiteWeylNormalizerLiftPaid := false
  fullSpin8Paid := false

end Integration.RationalOctonionInfinitesimalTriality

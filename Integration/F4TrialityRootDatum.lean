import Integration.AlbertRationalF4DerivationReceipt
import Mathlib

/-!
# Finite F4 root datum adapted to the Albert triality decomposition

The companion Albert derivation producer gives the exact decomposition

  52 = 28 + 8 + 8 + 8

with an so8 sector and vector / two chiral half-spin eight-dimensional sectors.
The corresponding standard F4 root decomposition is

  48 = 24(D4 roots) + 8(vector weights) + 8(spin+) + 8(spin-),

with rank four Cartan.  This file constructs that finite root datum directly,
independently of the Albert executable, and closes its four simple reflections.

The resulting generated reflection image has exact order 1152, the Weyl-group
order of F4.  This is a finite root-system theorem; it does not by itself turn
the cross-kernel Albert derivation receipt into a Lean proof of an isomorphism
of Lie algebras or algebraic groups.
-/

namespace Integration.F4TrialityRootDatum

inductive HalfCoord
  | mOne | mHalf | zero | pHalf | pOne
  deriving DecidableEq, Repr, Fintype

def coordRat : HalfCoord → ℚ
  | .mOne => -1
  | .mHalf => -(1/2 : ℚ)
  | .zero => 0
  | .pHalf => (1/2 : ℚ)
  | .pOne => 1

abbrev Code4 := Fin 4 → HalfCoord
abbrev V4 := Fin 4 → ℚ


def countCoord (p : HalfCoord → Bool) (v : Code4) : Nat :=
  (Finset.univ.filter fun i : Fin 4 => p (v i) = true).card


def isAbsOne : HalfCoord → Bool
  | .mOne | .pOne => true
  | _ => false


def isHalf : HalfCoord → Bool
  | .mHalf | .pHalf => true
  | _ => false


def isZero : HalfCoord → Bool
  | .zero => true
  | _ => false

/-- D4 long roots: two ±1 coordinates and two zero coordinates. -/
def isLongCode (v : Code4) : Bool :=
  decide (countCoord isAbsOne v = 2 ∧ countCoord isZero v = 2)

/-- Vector short roots: one ±1 coordinate and three zeros. -/
def isVectorCode (v : Code4) : Bool :=
  decide (countCoord isAbsOne v = 1 ∧ countCoord isZero v = 3)

/-- Half-spin roots: all four coordinates are ±1/2. -/
def isSpinCode (v : Code4) : Bool :=
  decide (countCoord isHalf v = 4)


def isF4RootCode (v : Code4) : Bool :=
  isLongCode v || isVectorCode v || isSpinCode v

abbrev F4Root := {v : Code4 // isF4RootCode v = true}
instance : Fintype F4Root := inferInstance


def rootVector (r : F4Root) : V4 := fun i => coordRat (r.1 i)

def dot (x y : V4) : ℚ := ∑ i : Fin 4, x i * y i

def normSq (x : V4) : ℚ := dot x x

 theorem f4_root_count : Fintype.card F4Root = 48 := by
  native_decide

 theorem f4_root_lengths :
    ∀ r : F4Root, normSq (rootVector r) = 1 ∨ normSq (rootVector r) = 2 := by
  native_decide

 theorem f4_long_root_count :
    (Finset.univ.filter fun r : F4Root => normSq (rootVector r) = 2).card = 24 := by
  native_decide

 theorem f4_short_root_count :
    (Finset.univ.filter fun r : F4Root => normSq (rootVector r) = 1).card = 24 := by
  native_decide

/-! ## Triality partition of the 24 short roots. -/

def signParityProduct (v : Code4) : Int :=
  ∏ i : Fin 4,
    match v i with
    | .mHalf => -1
    | .pHalf => 1
    | _ => 0

 theorem vector_weight_count :
    (Finset.univ.filter fun r : F4Root => isVectorCode r.1 = true).card = 8 := by
  native_decide

 theorem spin_plus_weight_count :
    (Finset.univ.filter fun r : F4Root =>
      isSpinCode r.1 = true ∧ signParityProduct r.1 = 1).card = 8 := by
  native_decide

 theorem spin_minus_weight_count :
    (Finset.univ.filter fun r : F4Root =>
      isSpinCode r.1 = true ∧ signParityProduct r.1 = -1).card = 8 := by
  native_decide

 theorem triality_root_ledger : 48 = 24 + 8 + 8 + 8 := by norm_num
 theorem derivation_dimension_ledger : 52 = 4 + 48 := by norm_num

/-! ## Simple roots and Cartan matrix. -/

inductive F4Simple
  | a1 | a2 | a3 | a4
  deriving DecidableEq, Repr, Fintype


def simpleRoot : F4Simple → V4
  | .a1 => ![0, 1, -1, 0]
  | .a2 => ![0, 0, 1, -1]
  | .a3 => ![0, 0, 0, 1]
  | .a4 => ![(1/2 : ℚ), -(1/2 : ℚ), -(1/2 : ℚ), -(1/2 : ℚ)]

/-- Cartan convention `A_ij = 2 (alpha_i,alpha_j)/(alpha_j,alpha_j)`. -/
def cartanEntry (i j : F4Simple) : ℚ :=
  2 * dot (simpleRoot i) (simpleRoot j) / normSq (simpleRoot j)


def expectedCartan : F4Simple → F4Simple → ℚ
  | .a1,.a1 | .a2,.a2 | .a3,.a3 | .a4,.a4 => 2
  | .a1,.a2 | .a2,.a1 => -1
  | .a2,.a3 => -2
  | .a3,.a2 => -1
  | .a3,.a4 | .a4,.a3 => -1
  | _,_ => 0

 theorem simple_cartan_is_f4 : ∀ i j, cartanEntry i j = expectedCartan i j := by
  native_decide

/-! ## Reflection matrices and exact Weyl closure. -/

abbrev Mat4 := Fin 4 → Fin 4 → ℚ


def identityMatrix : Mat4 := fun i j => if i = j then 1 else 0


def matrixComp (A B : Mat4) : Mat4 :=
  fun i j => ∑ k : Fin 4, A i k * B k j


def matrixApply (A : Mat4) (x : V4) : V4 :=
  fun i => ∑ j : Fin 4, A i j * x j


def reflectionMatrix (a : V4) : Mat4 :=
  fun i j => (if i = j then 1 else 0) -
    (2 * a i * a j / normSq a)


def generatorMatrix (s : F4Simple) : Mat4 := reflectionMatrix (simpleRoot s)

 theorem simple_generators_involutive :
    ∀ s, matrixComp (generatorMatrix s) (generatorMatrix s) = identityMatrix := by
  native_decide

/-- Every simple reflection permutes the independently enumerated 48 roots. -/
theorem simple_reflections_preserve_root_set :
    ∀ s r : F4Simple × F4Root,
      ∃ r' : F4Root,
        matrixApply (generatorMatrix s.1) (rootVector r.2) = rootVector r' := by
  native_decide


def expandMatrices (S : Finset Mat4) : Finset Mat4 :=
  S ∪ S.image (matrixComp (generatorMatrix .a1)) ∪
      S.image (matrixComp (generatorMatrix .a2)) ∪
      S.image (matrixComp (generatorMatrix .a3)) ∪
      S.image (matrixComp (generatorMatrix .a4))


def matrixOrbitN : Nat → Finset Mat4
  | 0 => {identityMatrix}
  | n + 1 => expandMatrices (matrixOrbitN n)

/-- Local exact preflight finds maximal simple-generator word distance 24. -/
def generatedWeylSet : Finset Mat4 := matrixOrbitN 24

 theorem generated_weyl_order : generatedWeylSet.card = 1152 := by
  native_decide

 theorem generated_weyl_stable : matrixOrbitN 25 = generatedWeylSet := by
  native_decide

structure Boundary where
  independentRootSet48Paid : Bool
  long24Short24Paid : Bool
  trialityShortSplitEightEightEightPaid : Bool
  f4CartanPaid : Bool
  simpleReflectionsPreserve48Paid : Bool
  weylOrder1152Paid : Bool
  weylClosureFixedPointPaid : Bool
  albertDerivationRootIntertwinerPaid : Bool
  fullF4AlgebraicGroupPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  independentRootSet48Paid := true
  long24Short24Paid := true
  trialityShortSplitEightEightEightPaid := true
  f4CartanPaid := true
  simpleReflectionsPreserve48Paid := true
  weylOrder1152Paid := true
  weylClosureFixedPointPaid := true
  albertDerivationRootIntertwinerPaid := false
  fullF4AlgebraicGroupPaid := false

end Integration.F4TrialityRootDatum

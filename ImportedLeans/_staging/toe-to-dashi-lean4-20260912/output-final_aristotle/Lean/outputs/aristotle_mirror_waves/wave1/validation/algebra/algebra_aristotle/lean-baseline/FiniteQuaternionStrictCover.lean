import Mathlib

/-!
# Lean mirror of `DASHI/Algebra/FiniteQuaternionStrictCover.agda`

The assigned strict surface depends on the exact finite `Q8 → V4` producer from
`FiniteQuaternionDoubleCover.agda`, which had no previous Lean mirror.  The
finite producer and the shared cover interfaces are therefore included here as
supporting declarations.  This remains only a finite model; it does not assert
a continuous Spin/Lorentz theorem.
-/

namespace AgdaMirror.FiniteQuaternionStrictCover

structure Preimage {A B : Type} (map : A → B) (target : B) where
  witness : A
  mapsToTarget : map witness = target

structure TwoElementFiber {A B : Type} (map : A → B) (target : B) where
  first : A
  second : A
  firstMaps : map first = target
  secondMaps : map second = target
  distinct : first ≠ second
  exhaustive : ∀ candidate, map candidate = target →
    candidate = first ∨ candidate = second

structure SpinDoubleCoverProof where
  Spin : Type
  SO : Type
  rho : Spin → SO
  spinIdentity : Spin
  soIdentity : SO
  plusOne : Spin
  minusOne : Spin
  SpinProduct : Spin → Spin → Spin
  SOProduct : SO → SO → SO
  rhoHomomorphism : ∀ a b, rho (SpinProduct a b) = SOProduct (rho a) (rho b)
  SurjectiveWitness : SO → Type
  rhoSurjective : ∀ rotation, SurjectiveWitness rotation
  kernelCharacterization : ∀ s,
    rho s = soIdentity ↔ (s = plusOne ∨ s = minusOne)
  fiberIsTwoElement : ∀ rotation, TwoElementFiber rho rotation

structure StrictSpinDoubleCoverProof where
  base : SpinDoubleCoverProof
  exactSurjectivity : ∀ rotation, Preimage base.rho rotation
  fiberProofAgreesWithSurjectivity : ∀ rotation,
    base.rho (base.fiberIsTwoElement rotation).first = rotation

inductive Sign | positiveSign | negativeSign
  deriving DecidableEq, Repr

inductive QuaternionBasis | basisOne | basisI | basisJ | basisK
  deriving DecidableEq, Repr

structure Q8 where
  sign : Sign
  basis : QuaternionBasis
  deriving DecidableEq, Repr

structure SignedBasis where
  productSign : Sign
  productBasis : QuaternionBasis

open Sign QuaternionBasis

def signMultiply : Sign → Sign → Sign
  | .positiveSign, right => right
  | .negativeSign, .positiveSign => .negativeSign
  | .negativeSign, .negativeSign => .positiveSign

def basisMultiply : QuaternionBasis → QuaternionBasis → SignedBasis
  | .basisOne, right => ⟨.positiveSign, right⟩
  | .basisI, .basisOne => ⟨.positiveSign, .basisI⟩
  | .basisI, .basisI => ⟨.negativeSign, .basisOne⟩
  | .basisI, .basisJ => ⟨.positiveSign, .basisK⟩
  | .basisI, .basisK => ⟨.negativeSign, .basisJ⟩
  | .basisJ, .basisOne => ⟨.positiveSign, .basisJ⟩
  | .basisJ, .basisI => ⟨.negativeSign, .basisK⟩
  | .basisJ, .basisJ => ⟨.negativeSign, .basisOne⟩
  | .basisJ, .basisK => ⟨.positiveSign, .basisI⟩
  | .basisK, .basisOne => ⟨.positiveSign, .basisK⟩
  | .basisK, .basisI => ⟨.positiveSign, .basisJ⟩
  | .basisK, .basisJ => ⟨.negativeSign, .basisI⟩
  | .basisK, .basisK => ⟨.negativeSign, .basisOne⟩

def q8Multiply (left right : Q8) : Q8 :=
  let result := basisMultiply left.basis right.basis
  ⟨signMultiply (signMultiply left.sign right.sign) result.productSign,
    result.productBasis⟩

def plusOne : Q8 := ⟨.positiveSign, .basisOne⟩
def minusOne : Q8 := ⟨.negativeSign, .basisOne⟩
def plusI : Q8 := ⟨.positiveSign, .basisI⟩
def minusI : Q8 := ⟨.negativeSign, .basisI⟩
def plusJ : Q8 := ⟨.positiveSign, .basisJ⟩
def minusJ : Q8 := ⟨.negativeSign, .basisJ⟩
def plusK : Q8 := ⟨.positiveSign, .basisK⟩
def minusK : Q8 := ⟨.negativeSign, .basisK⟩

inductive V4Rotation
  | identityRotation | halfTurnX | halfTurnY | halfTurnZ
  deriving DecidableEq, Repr

open V4Rotation

def basisRotation : QuaternionBasis → V4Rotation
  | .basisOne => .identityRotation
  | .basisI => .halfTurnX
  | .basisJ => .halfTurnY
  | .basisK => .halfTurnZ

def rho (q : Q8) : V4Rotation := basisRotation q.basis

def rotationMultiply : V4Rotation → V4Rotation → V4Rotation
  | .identityRotation, right => right
  | .halfTurnX, .identityRotation => .halfTurnX
  | .halfTurnX, .halfTurnX => .identityRotation
  | .halfTurnX, .halfTurnY => .halfTurnZ
  | .halfTurnX, .halfTurnZ => .halfTurnY
  | .halfTurnY, .identityRotation => .halfTurnY
  | .halfTurnY, .halfTurnX => .halfTurnZ
  | .halfTurnY, .halfTurnY => .identityRotation
  | .halfTurnY, .halfTurnZ => .halfTurnX
  | .halfTurnZ, .identityRotation => .halfTurnZ
  | .halfTurnZ, .halfTurnX => .halfTurnY
  | .halfTurnZ, .halfTurnY => .halfTurnX
  | .halfTurnZ, .halfTurnZ => .identityRotation

theorem rhoHomomorphism (left right : Q8) :
    rho (q8Multiply left right) = rotationMultiply (rho left) (rho right) := by
  cases left with
  | mk ls lb => cases ls <;> cases lb <;> cases right with
    | mk rs rb => cases rs <;> cases rb <;> rfl

def chosenPreimage : V4Rotation → Q8
  | .identityRotation => plusOne
  | .halfTurnX => plusI
  | .halfTurnY => plusJ
  | .halfTurnZ => plusK

theorem chosenPreimage_maps (r : V4Rotation) : rho (chosenPreimage r) = r := by
  cases r <;> rfl

theorem kernelCharacterization (q : Q8) :
    rho q = .identityRotation ↔ (q = plusOne ∨ q = minusOne) := by
  cases q with
  | mk s b => cases s <;> cases b <;> simp [rho, basisRotation, plusOne, minusOne]

def firstFiber : V4Rotation → Q8
  | .identityRotation => plusOne
  | .halfTurnX => plusI
  | .halfTurnY => plusJ
  | .halfTurnZ => plusK

def secondFiber : V4Rotation → Q8
  | .identityRotation => minusOne
  | .halfTurnX => minusI
  | .halfTurnY => minusJ
  | .halfTurnZ => minusK

theorem fiber_first_maps (r : V4Rotation) : rho (firstFiber r) = r := by cases r <;> rfl
theorem fiber_second_maps (r : V4Rotation) : rho (secondFiber r) = r := by cases r <;> rfl
theorem fiber_distinct (r : V4Rotation) : firstFiber r ≠ secondFiber r := by
  cases r <;> simp [firstFiber, secondFiber, plusOne, minusOne, plusI, minusI,
    plusJ, minusJ, plusK, minusK]

theorem fiber_exhaustive (r : V4Rotation) (q : Q8) (h : rho q = r) :
    q = firstFiber r ∨ q = secondFiber r := by
  cases q with
  | mk s b => cases s <;> cases b <;> cases r <;>
      simp_all [rho, basisRotation, firstFiber, secondFiber, plusOne, minusOne,
        plusI, minusI, plusJ, minusJ, plusK, minusK]

def rhoFiberIsTwoElement (r : V4Rotation) : TwoElementFiber rho r where
  first := firstFiber r
  second := secondFiber r
  firstMaps := fiber_first_maps r
  secondMaps := fiber_second_maps r
  distinct := fiber_distinct r
  exhaustive := fiber_exhaustive r

def finiteQuaternionSpinCover : SpinDoubleCoverProof where
  Spin := Q8
  SO := V4Rotation
  rho := rho
  spinIdentity := plusOne
  soIdentity := .identityRotation
  plusOne := plusOne
  minusOne := minusOne
  SpinProduct := q8Multiply
  SOProduct := rotationMultiply
  rhoHomomorphism := rhoHomomorphism
  SurjectiveWitness := fun r => Preimage rho r
  rhoSurjective := fun r => ⟨chosenPreimage r, chosenPreimage_maps r⟩
  kernelCharacterization := kernelCharacterization
  fiberIsTwoElement := rhoFiberIsTwoElement

/-- The exact preimage-producing strict wrapper requested by the Agda surface. -/
def exactPreimage (rotation : V4Rotation) : Preimage rho rotation :=
  ⟨chosenPreimage rotation, chosenPreimage_maps rotation⟩

theorem fiberAgrees (rotation : V4Rotation) :
    rho (rhoFiberIsTwoElement rotation).first = rotation :=
  (rhoFiberIsTwoElement rotation).firstMaps

def finiteQuaternionStrictSpinCover : StrictSpinDoubleCoverProof where
  base := finiteQuaternionSpinCover
  exactSurjectivity := exactPreimage
  fiberProofAgreesWithSurjectivity := fiberAgrees

/-- This finite result does not promote itself to a continuous cover. -/
def continuousSpinPromotion : Bool := false

end AgdaMirror.FiniteQuaternionStrictCover

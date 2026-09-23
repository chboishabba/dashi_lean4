import Mathlib
import Integration.StageTwelveGrothendieckRelation

namespace Integration.JInvariant369JointFibredObserver

open Integration.StageTwelveGrothendieckRelation

/-!
Finite cross-prover mirror of the Agda 369 joint-fibre work.

This module proves only the finite action-system statements:
* SSP coarse C3 cycle/antipode is equivariantly equivalent to level-3
  translation/inversion;
* signed multiplicity magnitude does not factor through that coarse C3;
* phase-6, level-27 and signed multiplicity form a joint finite fibre;
* reflection conjugates level translation to inverse translation on the joint
  fibre;
* a base projection forgets level translation.

It does not identify FRACTRAN arithmetic with modular-curve geometry or the
full deck group with these finite cyclic/dihedral actions.
-/

abbrev SSPC3 := ZMod 3
abbrev Level3 := ZMod 3
abbrev Phase6 := ZMod 6
abbrev Level27 := ZMod 27

def sspCycle (x : SSPC3) : SSPC3 := x + 1
def sspAntipode (x : SSPC3) : SSPC3 := -x

def level3Translate (x : Level3) : Level3 := x + 1
def level3Invert (x : Level3) : Level3 := -x

def sspToLevel3 (x : SSPC3) : Level3 := x
def level3ToSSP (x : Level3) : SSPC3 := x

theorem ssp_level3_roundtrip (x : SSPC3) :
    level3ToSSP (sspToLevel3 x) = x := rfl

theorem level3_ssp_roundtrip (x : Level3) :
    sspToLevel3 (level3ToSSP x) = x := rfl

theorem sspCycle_intertwines_level3Translation (x : SSPC3) :
    sspToLevel3 (sspCycle x) = level3Translate (sspToLevel3 x) := rfl

theorem sspAntipode_intertwines_level3Inversion (x : SSPC3) :
    sspToLevel3 (sspAntipode x) = level3Invert (sspToLevel3 x) := rfl

theorem ssp_dihedral_relation (x : SSPC3) :
    sspAntipode (sspCycle (sspAntipode x)) = x - 1 := by
  simp [sspAntipode, sspCycle]
  ring

/-! Signed FRACTRAN magnitude remains above the coarse C3 carrier. -/

def negateSignedMultiplicity : SignedMultiplicity → SignedMultiplicity
  | .negative n => .positive n
  | .zero => .zero
  | .positive n => .negative n

def signedMultiplicityToC3 : SignedMultiplicity → SSPC3
  | .negative _ => -1
  | .zero => 0
  | .positive _ => 1

def signedMagnitude : SignedMultiplicity → Nat
  | .negative n => n
  | .zero => 0
  | .positive n => n

theorem signedNegation_intertwines_antipode (m : SignedMultiplicity) :
    signedMultiplicityToC3 (negateSignedMultiplicity m)
      = sspAntipode (signedMultiplicityToC3 m) := by
  cases m <;> simp [negateSignedMultiplicity, signedMultiplicityToC3,
    sspAntipode]

theorem positiveOneTwo_sameCoarseC3 :
    signedMultiplicityToC3 (.positive 1)
      = signedMultiplicityToC3 (.positive 2) := rfl

theorem positiveOneTwo_differentMagnitude :
    signedMagnitude (.positive 1) ≠ signedMagnitude (.positive 2) := by
  decide

theorem signedMagnitude_not_sufficient_through_C3 :
    ¬ ConsumerSufficient signedMultiplicityToC3 signedMagnitude := by
  intro h
  exact positiveOneTwo_differentMagnitude
    (h (.positive 1) (.positive 2) positiveOneTwo_sameCoarseC3)

theorem signedMagnitude_cannot_factor_through_C3 :
    ¬ FactorsThrough signedMultiplicityToC3 signedMagnitude := by
  intro h
  apply signedMagnitude_not_sufficient_through_C3
  intro left right same
  calc
    signedMagnitude left = h.factor (signedMultiplicityToC3 left) := h.law left
    _ = h.factor (signedMultiplicityToC3 right) := by rw [same]
    _ = signedMagnitude right := (h.law right).symm

/-! First-class joint finite fibre. -/

structure Joint369FiniteFibre where
  phase6 : Phase6
  level27 : Level27
  signedSSP : SignedMultiplicity
  deriving DecidableEq, Repr

def translateJoint (x : Joint369FiniteFibre) : Joint369FiniteFibre where
  phase6 := x.phase6
  level27 := x.level27 + 1
  signedSSP := x.signedSSP

def translateJointInverse (x : Joint369FiniteFibre) : Joint369FiniteFibre where
  phase6 := x.phase6
  level27 := x.level27 - 1
  signedSSP := x.signedSSP

def reflectJoint (x : Joint369FiniteFibre) : Joint369FiniteFibre where
  phase6 := -x.phase6
  level27 := -x.level27
  signedSSP := negateSignedMultiplicity x.signedSSP

theorem negateSignedMultiplicity_involutive (m : SignedMultiplicity) :
    negateSignedMultiplicity (negateSignedMultiplicity m) = m := by
  cases m <;> rfl

theorem joint_RTR (x : Joint369FiniteFibre) :
    reflectJoint (translateJoint (reflectJoint x))
      = translateJointInverse x := by
  cases x with
  | mk phase level signed =>
      cases signed <;>
        simp [reflectJoint, translateJoint, translateJointInverse,
          negateSignedMultiplicity]
      <;> ring

def jointLevel9 (x : Joint369FiniteFibre) : ZMod 9 :=
  x.level27.castHom (by norm_num)

def jointLevel3 (x : Joint369FiniteFibre) : ZMod 3 :=
  x.level27.castHom (by norm_num)

/-!
Generic lifted state: translation changes level data while the declared base
surface is literally unchanged.
-/

structure JointLift (Base : Type) where
  base : Base
  fibre : Joint369FiniteFibre

def translateJointLift {Base : Type} (x : JointLift Base) : JointLift Base where
  base := x.base
  fibre := translateJoint x.fibre

def baseObserver {Base : Type} (x : JointLift Base) : Base := x.base
def level27Consumer {Base : Type} (x : JointLift Base) : Level27 := x.fibre.level27

theorem translation_invisible_to_base {Base : Type} (x : JointLift Base) :
    baseObserver (translateJointLift x) = baseObserver x := rfl

theorem level27_does_not_factor_through_base
    {Base : Type} (base : Base) :
    ¬ FactorsThrough
      (baseObserver : JointLift Base → Base)
      (level27Consumer : JointLift Base → Level27) := by
  intro h
  let x0 : JointLift Base :=
    ⟨base, ⟨0, 0, .zero⟩⟩
  let x1 : JointLift Base :=
    ⟨base, ⟨0, 1, .zero⟩⟩
  have sameBase : baseObserver x0 = baseObserver x1 := rfl
  have sameLevel :=
    calc
      level27Consumer x0 = h.factor (baseObserver x0) := h.law x0
      _ = h.factor (baseObserver x1) := by rw [sameBase]
      _ = level27Consumer x1 := (h.law x1).symm
  norm_num [x0, x1, level27Consumer] at sameLevel

structure Joint369Boundary where
  sspLevel3CarrierEquivalence : Bool
  c3GeneratorIntertwiner : Bool
  c2GeneratorIntertwiner : Bool
  finiteDihedralLaw : Bool
  signedMagnitudeFactorsThroughC3 : Bool
  jointFibreConstructed : Bool
  level27FactorsThroughBase : Bool
  fractranEqualsModularGeometry : Bool
  fullDeckGroupEqualsFiniteDihedral : Bool
  deriving Repr

def canonicalBoundary : Joint369Boundary where
  sspLevel3CarrierEquivalence := true
  c3GeneratorIntertwiner := true
  c2GeneratorIntertwiner := true
  finiteDihedralLaw := true
  signedMagnitudeFactorsThroughC3 := false
  jointFibreConstructed := true
  level27FactorsThroughBase := false
  fractranEqualsModularGeometry := false
  fullDeckGroupEqualsFiniteDihedral := false

end Integration.JInvariant369JointFibredObserver

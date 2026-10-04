import Mathlib.Tactic
import NSBControl.Rational345RealInitialState

/-!
# Round71 canonical physical radius-four carrier

Agda Round63/71 stores exactly one representative of each nonzero reality
orbit `{k,-k}`: inspect coordinates in x,y,z order and keep the mode whose
first nonzero coordinate is positive.  This file installs the same carrier on
the Lean radius-four mode cube.

A `CanonicalState` therefore stores only positive representatives.  `decode`
reconstructs the zero mode as zero and negative representatives by complex
conjugation.  Fourier reality is structural rather than an invariant field on
an ambient state.
-/

namespace NSBControl
namespace Rational345Round71PhysicalCarrier

open Rational345RealRadius4
open Rational345RealInitialState

/-- Coordinate negation inside the fixed `[-4,4]` encoding `Fin 9`. -/
def negateAxis (i : Fin 9) : Fin 9 :=
  ⟨8 - i.1, by omega⟩

/-- Fourier mode negation on the fixed radius-four cube. -/
def negateMode (k : Mode) : Mode :=
  ⟨negateAxis k.x, negateAxis k.y, negateAxis k.z⟩

@[simp] theorem negateAxis_involutive (i : Fin 9) :
    negateAxis (negateAxis i) = i := by
  apply Fin.ext
  simp [negateAxis]
  omega

@[simp] theorem negateMode_involutive (k : Mode) :
    negateMode (negateMode k) = k := by
  cases k
  simp [negateMode]

@[simp] theorem kInt_negate (k : Mode) (j : Fin 3) :
    kInt (negateMode k) j = - kInt k j := by
  fin_cases j <;>
    simp [kInt, negateMode, negateAxis, axisInt] <;> omega

/-- Exact Lean mirror of Agda Round63 `leadingPositive`: first nonzero
coordinate in x,y,z order is positive. -/
def leadingPositive (k : Mode) : Prop :=
  0 < kInt k 0 ∨
  (kInt k 0 = 0 ∧
    (0 < kInt k 1 ∨
      (kInt k 1 = 0 ∧ 0 < kInt k 2)))

instance (k : Mode) : Decidable (leadingPositive k) := inferInstance

/-- The encoded zero Fourier mode. -/
def zeroMode : Mode := ⟨4, 4, 4⟩

@[simp] theorem kInt_zeroMode (j : Fin 3) : kInt zeroMode j = 0 := by
  fin_cases j <;> norm_num [zeroMode, kInt, axisInt]

@[simp] theorem zeroMode_isZero : isZeroMode zeroMode := by
  intro j
  exact kInt_zeroMode j

@[simp] theorem zeroMode_not_leadingPositive : ¬ leadingPositive zeroMode := by
  simp [leadingPositive]

/-- A selected canonical mode is necessarily nonzero. -/
theorem leadingPositive_nonzero {k : Mode} (hk : leadingPositive k) :
    ¬ isZeroMode k := by
  intro hz
  have hx := hz (0 : Fin 3)
  have hy := hz (1 : Fin 3)
  have hz' := hz (2 : Fin 3)
  unfold leadingPositive at hk
  omega

/-- A nonzero mode has at least one nonzero coordinate. -/
theorem nonzero_coordinate {k : Mode} (hk : ¬ isZeroMode k) :
    kInt k 0 ≠ 0 ∨ kInt k 1 ≠ 0 ∨ kInt k 2 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hk
  intro j
  fin_cases j <;> simp_all

/-- Negation preserves nonzeroness. -/
theorem negate_nonzero {k : Mode} (hk : ¬ isZeroMode k) :
    ¬ isZeroMode (negateMode k) := by
  intro hz
  apply hk
  intro j
  have h := hz j
  rw [kInt_negate] at h
  omega

/-- Exactly one member of each nonzero reality orbit is selected. -/
theorem leadingPositive_negate_iff_not {k : Mode} (hk : ¬ isZeroMode k) :
    leadingPositive k ↔ ¬ leadingPositive (negateMode k) := by
  have hcoord := nonzero_coordinate hk
  simp only [leadingPositive, kInt_negate]
  omega

/-- The opposite of an unselected nonzero mode is selected. -/
theorem leadingPositive_negate_of_not {k : Mode}
    (hk : ¬ isZeroMode k) (hnot : ¬ leadingPositive k) :
    leadingPositive (negateMode k) := by
  have hnz := negate_nonzero hk
  have h := leadingPositive_negate_iff_not (k := negateMode k) hnz
  rw [negateMode_involutive] at h
  exact (not_congr h).mp (not_not_intro hnot)

/-- One representative per nonzero `{k,-k}` reality orbit. -/
abbrev CanonicalMode := {k : Mode // leadingPositive k}

/-- Independent physical coordinates. -/
abbrev CanonicalState := CanonicalMode → Vec3

/-- Decode independent coordinates to the full Fourier cube.  Reality and the
zero-mode condition are built into this function. -/
def decode (a : CanonicalState) : State := fun k =>
  if hz : isZeroMode k then 0
  else if hp : leadingPositive k then a ⟨k, hp⟩
  else vecConj (a ⟨negateMode k, leadingPositive_negate_of_not hz hp⟩)

@[simp] theorem decode_zero (a : CanonicalState) :
    decode a zeroMode = 0 := by
  simp [decode]

@[simp] theorem decode_positive (a : CanonicalState) (k : CanonicalMode) :
    decode a k.1 = a k := by
  have hnz : ¬ isZeroMode k.1 := leadingPositive_nonzero k.2
  simp [decode, hnz, k.2]

@[simp] theorem decode_negative (a : CanonicalState) (k : CanonicalMode) :
    decode a (negateMode k.1) = vecConj (a k) := by
  have hnz : ¬ isZeroMode k.1 := leadingPositive_nonzero k.2
  have hnzNeg : ¬ isZeroMode (negateMode k.1) := negate_nonzero hnz
  have hneg : ¬ leadingPositive (negateMode k.1) :=
    (leadingPositive_negate_iff_not hnz).mp k.2
  simp only [decode, hnzNeg, hneg, dite_false]
  congr 2
  apply Subtype.ext
  simp

/-- Structural Fourier reality: decoded opposite modes are conjugates. -/
theorem decode_reality (a : CanonicalState) (k : Mode) :
    decode a (negateMode k) = vecConj (decode a k) := by
  by_cases hz : isZeroMode k
  · have hkzero : k = zeroMode := by
      apply Mode.ext <;> simp only [zeroMode]
      · have := hz (0 : Fin 3)
        simp [kInt, axisInt] at this
        omega
      · have := hz (1 : Fin 3)
        simp [kInt, axisInt] at this
        omega
      · have := hz (2 : Fin 3)
        simp [kInt, axisInt] at this
        omega
    subst k
    simp [decode, vecConj]
  · by_cases hp : leadingPositive k
    · let ck : CanonicalMode := ⟨k, hp⟩
      simpa [ck] using decode_negative a ck
    · have hpn : leadingPositive (negateMode k) :=
        leadingPositive_negate_of_not hz hp
      have hnz := negate_nonzero hz
      simp [decode, hz, hp, hnz, hpn, vecConj]

/-- This is the same one-representative-per-reality-orbit architecture as
Agda Round63/71; no negative Fourier coordinate is independently stored. -/
def round71RealityStructural : Bool := true

end Rational345Round71PhysicalCarrier
end NSBControl

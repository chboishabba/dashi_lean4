import Mathlib
import AgdaMirror.HalfTrit

/-!
# Lean mirror of `DASHI/Algebra/Trit/HalfTritIndexed.agda` (genuine core)

An indexed `HalfTrit` coordinate code that preserves the five half-trit cases
exactly: the `Fin 5` index with both round-trips (`indexedToFin`/`finToIndexed`),
the no-duplicate value list, and the genuinely injective coordinate embedding
`embedIndexed : HalfTrit → HalfTritIndexed` (companion to the *non*-injective
`embedTrit` of `HalfTrit`).  The receipt scaffolding (residual E8 obligations,
promotion flags) is omitted; everything below is fully proved.
-/

namespace AgdaMirror.HalfTritIndexedMod

open AgdaMirror.HalfTritMod (HalfTrit)

/-- The five indexed half-trit coordinates. -/
inductive HalfTritIndexed
  | indexedNegOne | indexedNegHalf | indexedZero | indexedPosHalf | indexedPosOne
  deriving DecidableEq, Repr

open HalfTritIndexed

/-- Index into `Fin 5`. -/
def indexedToFin : HalfTritIndexed → Fin 5
  | indexedNegOne => 0
  | indexedNegHalf => 1
  | indexedZero => 2
  | indexedPosHalf => 3
  | indexedPosOne => 4

/-- Recover the coordinate from its `Fin 5` index. -/
def finToIndexed : Fin 5 → HalfTritIndexed
  | 0 => indexedNegOne
  | 1 => indexedNegHalf
  | 2 => indexedZero
  | 3 => indexedPosHalf
  | 4 => indexedPosOne

/-- Round-trip: coordinate → index → coordinate. -/
theorem indexedToFinToIndexed (x : HalfTritIndexed) : finToIndexed (indexedToFin x) = x := by
  cases x <;> rfl

/-- Round-trip: index → coordinate → index. -/
theorem finToIndexedToFin (i : Fin 5) : indexedToFin (finToIndexed i) = i := by
  fin_cases i <;> rfl

/-- The five values in order. -/
def allHalfTritIndexedValues : List HalfTritIndexed :=
  [indexedNegOne, indexedNegHalf, indexedZero, indexedPosHalf, indexedPosOne]

theorem allHalfTritIndexedValuesLengthIsFive :
    allHalfTritIndexedValues.length = 5 := rfl

theorem allHalfTritIndexedValuesNoDuplicates :
    allHalfTritIndexedValues.Nodup := by decide

/-- The coordinate embedding from `HalfTrit`. -/
def embedIndexed : HalfTrit → HalfTritIndexed
  | .negOne => indexedNegOne
  | .negHalf => indexedNegHalf
  | .zero => indexedZero
  | .posHalf => indexedPosHalf
  | .posOne => indexedPosOne

/-- The coordinate embedding is injective (unlike the forgetful `embedTrit`). -/
theorem embedIndexed_injective (x y : HalfTrit) (h : embedIndexed x = embedIndexed y) : x = y := by
  cases x <;> cases y <;> simp_all [embedIndexed]

end AgdaMirror.HalfTritIndexedMod

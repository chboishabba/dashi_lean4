import Mathlib

/-!
# Lean mirror of `Base369.agda` (genuine, fully proved)

Faithful transcription of `Base369.agda`: three cyclic "truth" universes
`ℤ/3`, `ℤ/6`, `ℤ/9` with a generic iterated rotation `spin`, a "spin" XOR
(repeated rotation) and a "closed" XOR (addition mod `k`), the agreement of the
two definitions, the order of the rotation (`rot^k = id`), the left identity,
and (for the ternary case) associativity.  All proofs are by case analysis,
exactly mirroring the Agda `refl` enumerations.
-/

namespace AgdaMirror.Base369

/-- Generic iterated rotation. -/
def spin {A : Type} : Nat → (A → A) → A → A
  | 0,     _,   x => x
  | n + 1, rot, x => rot (spin n rot x)

/-! ## Ternary universe `ℤ/3` -/

inductive TriTruth | low | mid | high deriving DecidableEq

def triIndex : TriTruth → Nat | .low => 0 | .mid => 1 | .high => 2
def fromTriIndex (n : Nat) : TriTruth :=
  match n % 3 with | 0 => .low | 1 => .mid | _ => .high
def rotateTri : TriTruth → TriTruth | .low => .mid | .mid => .high | .high => .low

def triXorSpin (carrier target : TriTruth) : TriTruth :=
  spin (triIndex carrier) rotateTri target
def triXor (carrier target : TriTruth) : TriTruth :=
  fromTriIndex (triIndex carrier + triIndex target)

theorem triXor_spin_correct (a b : TriTruth) : triXorSpin a b = triXor a b := by
  cases a <;> cases b <;> rfl
theorem rotateTri_cubed (t : TriTruth) : rotateTri (rotateTri (rotateTri t)) = t := by
  cases t <;> rfl
theorem triXor_idL (t : TriTruth) : triXor .low t = t := by cases t <;> rfl
theorem triXor_assoc (a b c : TriTruth) :
    triXor a (triXor b c) = triXor (triXor a b) c := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## Hexadic universe `ℤ/6` -/

inductive HexTruth | h0 | h1 | h2 | h3 | h4 | h5 deriving DecidableEq

def hexIndex : HexTruth → Nat
  | .h0 => 0 | .h1 => 1 | .h2 => 2 | .h3 => 3 | .h4 => 4 | .h5 => 5
def fromHexIndex (n : Nat) : HexTruth :=
  match n % 6 with
  | 0 => .h0 | 1 => .h1 | 2 => .h2 | 3 => .h3 | 4 => .h4 | _ => .h5
def rotateHex : HexTruth → HexTruth
  | .h0 => .h1 | .h1 => .h2 | .h2 => .h3 | .h3 => .h4 | .h4 => .h5 | .h5 => .h0

def hexXorSpin (carrier target : HexTruth) : HexTruth :=
  spin (hexIndex carrier) rotateHex target
def hexXor (carrier target : HexTruth) : HexTruth :=
  fromHexIndex (hexIndex carrier + hexIndex target)

theorem hexXor_spin_correct (a b : HexTruth) : hexXorSpin a b = hexXor a b := by
  cases a <;> cases b <;> rfl
theorem rotateHex_sixth (h : HexTruth) : spin 6 rotateHex h = h := by cases h <;> rfl
theorem hexXor_idL (h : HexTruth) : hexXor .h0 h = h := by cases h <;> rfl

/-! ## Nonary universe `ℤ/9` -/

inductive NonaryTruth | n0 | n1 | n2 | n3 | n4 | n5 | n6 | n7 | n8 deriving DecidableEq

def nonaryIndex : NonaryTruth → Nat
  | .n0 => 0 | .n1 => 1 | .n2 => 2 | .n3 => 3 | .n4 => 4
  | .n5 => 5 | .n6 => 6 | .n7 => 7 | .n8 => 8
def fromNonaryIndex (n : Nat) : NonaryTruth :=
  match n % 9 with
  | 0 => .n0 | 1 => .n1 | 2 => .n2 | 3 => .n3 | 4 => .n4
  | 5 => .n5 | 6 => .n6 | 7 => .n7 | _ => .n8
def rotateNonary : NonaryTruth → NonaryTruth
  | .n0 => .n1 | .n1 => .n2 | .n2 => .n3 | .n3 => .n4 | .n4 => .n5
  | .n5 => .n6 | .n6 => .n7 | .n7 => .n8 | .n8 => .n0

def nonaryXorSpin (carrier target : NonaryTruth) : NonaryTruth :=
  spin (nonaryIndex carrier) rotateNonary target
def nonaryXor (carrier target : NonaryTruth) : NonaryTruth :=
  fromNonaryIndex (nonaryIndex carrier + nonaryIndex target)

theorem nonaryXor_spin_correct (a b : NonaryTruth) : nonaryXorSpin a b = nonaryXor a b := by
  cases a <;> cases b <;> rfl
theorem rotateNonary_ninth (n : NonaryTruth) : spin 9 rotateNonary n = n := by cases n <;> rfl
theorem nonaryXor_idL (n : NonaryTruth) : nonaryXor .n0 n = n := by cases n <;> rfl

end AgdaMirror.Base369

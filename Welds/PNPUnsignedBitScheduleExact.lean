import Mathlib

namespace PNPUnsignedBitSchedule

def bit (b : Bool) : Nat := if b then 1 else 0

def xorGate (a b : Bool) : Bool := (a || b) && !(a && b)

def fullAdder (a b c : Bool) : Bool × Bool :=
  let u := xorGate a b
  (xorGate u c,(a && b) || (u && c))

theorem fullAdder_exact (a b c : Bool) :
    bit (fullAdder a b c).1 + 2*bit (fullAdder a b c).2 =
      bit a+bit b+bit c := by
  cases a <;> cases b <;> cases c <;> decide

def fullSubtract (a b c : Bool) : Bool × Bool :=
  let u := xorGate a b
  (xorGate u c,(!a && b) || (!u && c))

theorem fullSubtract_exact (a b c : Bool) :
    bit a + 2*bit (fullSubtract a b c).2 =
      bit (fullSubtract a b c).1+bit b+bit c := by
  cases a <;> cases b <;> cases c <;> decide

def value : List Bool → Nat
  | [] => 0
  | b::bs => bit b+2*value bs

-- Pairing includes explicit zero padding; final carry remains present.
def addPairs : List (Bool × Bool) → Bool → List Bool
  | [],c => [c]
  | (a,b)::xs,c => (fullAdder a b c).1 :: addPairs xs (fullAdder a b c).2

theorem addPairs_exact (xs : List (Bool × Bool)) (c : Bool) :
    value (addPairs xs c) =
      value (xs.map Prod.fst)+value (xs.map Prod.snd)+bit c := by
  induction xs generalizing c with
  | nil => simp [addPairs,value]
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    simp only [addPairs,List.map_cons,value]
    rw [ih]
    have h := fullAdder_exact a b c
    omega

theorem addPairs_length (xs : List (Bool × Bool)) (c : Bool) :
    (addPairs xs c).length = xs.length+1 := by
  induction xs generalizing c with
  | nil => rfl
  | cons ab xs ih =>
    rcases ab with ⟨a,b⟩
    simp [addPairs,ih]

-- Per-bit expression in the actual Python schedule: two four-gate XORs,
-- two ANDs and one OR for carry. This is a register-gate count, not a
-- single tape head movement or whole-program clock theorem.
def addGateCount (xs : List (Bool × Bool)) : Nat := 11*xs.length

theorem addGateCount_cons (ab : Bool × Bool) (xs : List (Bool × Bool)) :
    addGateCount (ab::xs) = 11+addGateCount xs := by
  simp [addGateCount]
  omega

end PNPUnsignedBitSchedule

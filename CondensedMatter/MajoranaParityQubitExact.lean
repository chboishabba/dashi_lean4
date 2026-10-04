import Mathlib

namespace CondensedMatter

/-!
Exact four-Majorana parity-qubit combinatorics.

Four Majoranas are paired into occupations (n12,n34).  Even total fermion
parity leaves exactly |00> and |11>, giving a two-state logical carrier.
This is a mathematical encoding theorem, not a YbSb2 experimental claim.
-/

inductive OccupationBit
  | zero
  | one
  deriving DecidableEq, Repr

def OccupationBit.xor : OccupationBit → OccupationBit → OccupationBit
  | .zero, b => b
  | .one, .zero => .one
  | .one, .one => .zero

structure PairOccupation where
  n12 : OccupationBit
  n34 : OccupationBit
  deriving DecidableEq, Repr

def PairOccupation.totalParity (p : PairOccupation) : OccupationBit :=
  p.n12.xor p.n34

structure EvenParityState where
  occupation : PairOccupation
  evenWitness : occupation.totalParity = .zero

inductive LogicalQubit
  | logicalZero
  | logicalOne
  deriving DecidableEq, Repr

def encodeLogical : LogicalQubit → EvenParityState
  | .logicalZero => ⟨⟨.zero, .zero⟩, rfl⟩
  | .logicalOne => ⟨⟨.one, .one⟩, rfl⟩

def decodeLogical : EvenParityState → LogicalQubit
  | ⟨⟨.zero, .zero⟩, _⟩ => .logicalZero
  | ⟨⟨.one, .one⟩, _⟩ => .logicalOne
  | ⟨⟨.zero, .one⟩, h⟩ => by simp [PairOccupation.totalParity, OccupationBit.xor] at h
  | ⟨⟨.one, .zero⟩, h⟩ => by simp [PairOccupation.totalParity, OccupationBit.xor] at h

theorem decode_encode (q : LogicalQubit) :
    decodeLogical (encodeLogical q) = q := by
  cases q <;> rfl

theorem encode_decode_occupation (s : EvenParityState) :
    (encodeLogical (decodeLogical s)).occupation = s.occupation := by
  rcases s with ⟨⟨a,b⟩, h⟩
  cases a <;> cases b <;>
    simp [PairOccupation.totalParity, OccupationBit.xor] at h ⊢

theorem logical_basis_distinct :
    LogicalQubit.logicalZero ≠ LogicalQubit.logicalOne := by
  decide

end CondensedMatter

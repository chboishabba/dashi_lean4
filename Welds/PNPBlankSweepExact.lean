import Welds.PNPActualInventoryClosureExact
import Welds.PNPIntrinsicRecurrenceWireDemandExact

namespace PNPBlankSweep
open PNPStackEmittedList PNPActualPackedMacro PNPActualMacroBlock
open PNPActualInstructionLedger PNPActualPrimeRun PNPActualPrimeLayout
open PNPActualInventoryClosure

-- In a right-only blank suffix the scanned symbol is always zero.
-- Retain the original written digits, left stack and both extents.
def appendWrites (B : Nat) (l : Nat) : List Nat → Nat
  | [] => l
  | b::bs => appendWrites B (B*l+b) bs

theorem appendWrites_append (B l : Nat) (xs ys : List Nat) :
    appendWrites B l (xs++ys) = appendWrites B (appendWrites B l xs) ys := by
  induction xs generalizing l with
  | nil => rfl
  | cons b bs ih => exact ih (B*l+b)

theorem blankBlock (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (hA : 0<A) (hq : q<Q) (legal : LegalTable Q A table)
    (i : Instruction) (hi : table q 0=some i) (hm : i.move=.right)
    (l ll rr : Nat) (hr : 0<rr) :
    let B := max 2 A
    stepToFractionBlock Q A table q (lanes l 0 0 ll rr) =
      some (⟨mainTag (.q i.target),lanes (B*l+i.write) 0 0 (ll+1) (max 1 (rr-1))⟩,
        commonRaw 0 l B + (if 2≤rr then 2 else 1)) := by
  have hp := (legal q 0 i hq hA hi).1
  simpa using rightBlock Q A q 0 0 l ll rr table i hq hA hp hr hi hm

-- A sweep carries actual source rule receipts for every represented
-- step, but its control path ignores the growing left value only while
-- the right suffix is blank and no reversal or stay is admitted.
inductive Sweep (table : Nat → Nat → Option Instruction) :
    Nat → List Nat → Nat → Prop where
  | done (q : Nat) : Sweep table q [] q
  | step {q p : Nat} {bs : List Nat} (i : Instruction)
      (rule : table q 0=some i) (right : i.move=.right)
      (rest : Sweep table i.target bs p) : Sweep table q (i.write::bs) p

theorem sweep_append {table : Nat → Nat → Option Instruction}
    {q p t : Nat} {xs ys : List Nat}
    (a : Sweep table q xs p) (b : Sweep table p ys t) :
    Sweep table q (xs++ys) t := by
  induction a with
  | done => exact b
  | step i rule right rest ih => exact Sweep.step i rule right ih

def rawCount (B l rr : Nat) : List Nat → Nat
  | [] => 0
  | b::bs => (commonRaw 0 l B + (if 2≤rr then 2 else 1)) +
      rawCount B (B*l+b) (max 1 (rr-1)) bs

theorem sweep_raw {Q A : Nat} {table : Nat → Nat → Option Instruction}
    (legal : LegalTable Q A table) (hA : 0<A)
    {q p : Nat} {bs : List Nat} (s : Sweep table q bs p) (hq : q<Q)
    (l ll rr : Nat) (hr : 0<rr) :
    run (compile Q A table) (rawCount (max 2 A) l rr bs)
      ⟨mainTag (.q q),lanes l 0 0 ll rr⟩ =
    some ⟨mainTag (.q p),lanes (appendWrites (max 2 A) l bs) 0 0
      (ll+bs.length) (max 1 (rr-bs.length))⟩ := by
  induction s generalizing l ll rr with
  | done q =>
    have e : max 1 rr = rr := by omega
    simp [rawCount,appendWrites,run,e]
  | step i rule right rest ih =>
    have h := blankBlock Q A _ table hA hq legal i rule right l ll rr hr
    have hrun := stepToFractionBlock_sound Q A table _ _ _ _ h
    have nextBound := (legal _ 0 i hq hA rule).1
    have tail := ih nextBound (max 2 A*l+i.write) (ll+1) (max 1 (rr-1)) (by omega)
    have extent : max 1 (max 1 (rr-1)-List.length _) =
        max 1 (rr-(List.length _+1)) := by omega
    simp only [rawCount,appendWrites,List.length_cons]
    rw [run_append,hrun]
    simpa [extent,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tail

-- Native receipt retains the original run length. A compressed word
-- representation for repeated writes is not itself a physical clock.
def repeatedWrites (bs : List Nat) : Nat → List Nat
  | 0 => []
  | k+1 => bs++repeatedWrites bs k

theorem sweep_cycle {table : Nat → Nat → Option Instruction}
    {q : Nat} {bs : List Nat} (loop : Sweep table q bs q) (k : Nat) :
    Sweep table q (repeatedWrites bs k) q := by
  induction k with
  | zero => exact Sweep.done q
  | succ k ih => exact sweep_append loop ih

theorem sweep_prefix_cycle_suffix {table : Nat → Nat → Option Instruction}
    {q p t : Nat} {xs bs ys : List Nat}
    (prefix : Sweep table q xs p) (loop : Sweep table p bs p)
    (suffix : Sweep table p ys t) (k : Nat) :
    Sweep table q (xs++repeatedWrites bs k++ys) t := by
  rw [List.append_assoc]
  exact sweep_append prefix (sweep_append (sweep_cycle loop k) suffix)

theorem sweep_prime {Q A : Nat} {table : Nat → Nat → Option Instruction}
    (legal : LegalTable Q A table) (hA : 0<A)
    {q p : Nat} {bs : List Nat} (s : Sweep table q bs p) (hq : q<Q)
    (l ll rr : Nat) (hr : 0<rr) :
    integerRun Q A (compile Q A table) (rawCount (max 2 A) l rr bs)
      (integerState Q A ⟨mainTag (.q q),lanes l 0 0 ll rr⟩) =
    some (integerState Q A ⟨mainTag (.q p),lanes
      (appendWrites (max 2 A) l bs) 0 0 (ll+bs.length) (max 1 (rr-bs.length))⟩) := by
  rw [compiled_primeRunExact,sweep_raw legal hA s hq l ll rr hr]
  rfl

end PNPBlankSweep

import Welds.PNPActualDigitDispatchExact
import Welds.RecursiveHyperfabricQuotientExact

namespace PNPActualMacroBlock
open PNPStackEmittedList
open PNPActualInstructionLedger

-- A real phase advances by its maximal native transfer and one actual
-- priority-selected exit. Return the RAW edge count, not a macro clock.
def phaseAdvance (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (v : Data) : Option (State × Nat) :=
  if mainTag p ∈ inventory Q A then
    match transfer (max 2 A) table p with
    | none => (step (compile Q A table) ⟨mainTag p,v⟩).map (fun w => (w,1))
    | some t =>
      if midTag p ∈ inventory Q A then
        let k := v t.x / t.a
        (step (compile Q A table)
          ⟨mainTag p,PNPStackFiveLane.moveData t k v⟩).map (fun w => (w,2*k+1))
      else none
  else none

theorem phaseAdvance_sound (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (v : Data) (w : State) (n : Nat)
    (h : phaseAdvance Q A table p v = some (w,n)) :
    run (compile Q A table) n ⟨mainTag p,v⟩ = some w := by
  by_cases hm : mainTag p ∈ inventory Q A
  · cases ht : transfer (max 2 A) table p with
    | none =>
      cases he : step (compile Q A table) ⟨mainTag p,v⟩ with
      | none => simp [phaseAdvance,hm,ht,he] at h
      | some u =>
        simp [phaseAdvance,hm,ht,he] at h
        rcases h with ⟨rfl,rfl⟩
        simp [run,he]
    | some t =>
      by_cases hh : midTag p ∈ inventory Q A
      · cases he : step (compile Q A table)
          ⟨mainTag p,PNPStackFiveLane.moveData t (v t.x/t.a) v⟩ with
        | none => simp [phaseAdvance,hm,ht,hh,he] at h
        | some u =>
          simp [phaseAdvance,hm,ht,hh,he] at h
          rcases h with ⟨rfl,rfl⟩
          exact PNPActualTransferCompose.maximal_then_exit Q A table p t v u hm hh ht he
      · simp [phaseAdvance,hm,ht,hh] at h
  · simp [phaseAdvance,hm] at h

def terminalPhase : Phase → Bool
  | .q _ => true
  | .halt _ => true
  | _ => false

-- Start at a canonical control boundary and advance at least one phase.
-- A bounded private-phase walk must refuse if it cannot reach a boundary.
def runMacroBlock (Q A : Nat) (table : Nat → Nat → Option Instruction) :
    Nat → Phase → Data → Option (State × Nat)
  | 0,_,_ => none
  | fuel+1,p,v =>
      (phaseAdvance Q A table p v).bind fun (w,n) =>
        if w.tag.mid then none
        else if terminalPhase w.tag.phase then some (w,n)
        else (runMacroBlock Q A table fuel w.tag.phase w.data).map
          (fun (z,k) => (z,n+k))

theorem main_of_not_mid (s : State) (h : s.tag.mid = false) :
    (⟨mainTag s.tag.phase,s.data⟩ : State) = s := by
  cases s with
  | mk tag data =>
    cases tag with
    | mk phase mid =>
      cases mid <;> simp [mainTag] at *

theorem runMacroBlock_sound (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (fuel : Nat) (p : Phase) (v : Data) (w : State) (n : Nat)
    (h : runMacroBlock Q A table fuel p v = some (w,n)) :
    run (compile Q A table) n ⟨mainTag p,v⟩ = some w := by
  induction fuel generalizing p v w n with
  | zero => simp [runMacroBlock] at h
  | succ fuel ih =>
    cases he : phaseAdvance Q A table p v with
    | none => simp [runMacroBlock,he] at h
    | some pair =>
      rcases pair with ⟨u,k⟩
      have hu := phaseAdvance_sound Q A table p v u k he
      cases hm : u.tag.mid with
      | true => simp [runMacroBlock,he,hm] at h
      | false =>
        cases ht : terminalPhase u.tag.phase with
        | true =>
          simp [runMacroBlock,he,hm,ht] at h
          rcases h with ⟨rfl,rfl⟩
          exact hu
        | false =>
          cases hr : runMacroBlock Q A table fuel u.tag.phase u.data with
          | none => simp [runMacroBlock,he,hm,ht,hr] at h
          | some tail =>
            rcases tail with ⟨z,j⟩
            have hz := ih u.tag.phase u.data z j hr
            rw [main_of_not_mid u hm] at hz
            simp [runMacroBlock,he,hm,ht,hr] at h
            rcases h with ⟨rfl,rfl⟩
            exact compose_phases _ _ _ _ _ _ hu hz

def stepToFractionBlock (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (q : Nat) (v : Data) :=
  runMacroBlock Q A table 12 (.q q) v

theorem stepToFractionBlock_sound (Q A : Nat)
    (table : Nat → Nat → Option Instruction) (q : Nat) (v : Data)
    (w : State) (n : Nat) (h : stepToFractionBlock Q A table q v = some (w,n)) :
    run (compile Q A table) n ⟨mainTag (.q q),v⟩ = some w :=
  runMacroBlock_sound Q A table 12 (.q q) v w n h

-- A useful actual extent branch: the original priority list must
-- consume two right-extent units before the one-unit restoration.
theorem rightLen_long (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hm : mainTag (.rightLen q) ∈ inventory Q A)
    (h : 2 ≤ v rlen) :
    step (compile Q A table) ⟨mainTag (.rightLen q),v⟩ =
      some ⟨mainTag (.rightRestore q),fun i => v i-lane rlen 2 i+lane llen 1 i⟩ := by
  have en : enabled ⟨mainTag (.rightLen q),takeGive (.rightRestore q) rlen 2 llen 1⟩
      ⟨mainTag (.rightLen q),v⟩ := by
    refine ⟨rfl,?_⟩
    intro i
    by_cases hi : i=rlen
    · subst i; simpa [takeGive,lane] using h
    · simp [takeGive,lane,hi]
  unfold step
  rw [compiled_first Q A table _ hm]
  simp [phaseList,transfer,mainTag,exits,tagged,first,en,takeGive]

-- Soundness of a returned block is not total endpoint bisimulation.
-- Prove fuel suffices and compute the result on every valid packed
-- candidate, then attach the original decodedEndpoint and prime basis.

end PNPActualMacroBlock

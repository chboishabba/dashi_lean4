import Welds.PNPActualPackedMacroExact

namespace PNPActualWordBisim
open PNPStackEmittedList PNPActualMacroBlock PNPActualPackedMacro
open PNPStackFractran (Config Packed pack push encode rightMove leftMove stay)

def dataOf (B : Nat) (c : Config) : Data :=
  let p := pack B c
  lanes p.L p.R 0 p.llen p.rlen

def sourceResult (B q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Config) : State :=
  match table q c.scanned with
  | none => ⟨mainTag (.halt q),dataOf B c⟩
  | some i =>
    match i.move with
    | .stay => ⟨mainTag (.q i.target),dataOf B (stay c i.write)⟩
    | .right => ⟨mainTag (.q i.target),dataOf B (rightMove c i.write)⟩
    | .left => ⟨mainTag (.q i.target),dataOf B (leftMove c i.write)⟩

theorem dataOf_explicit (B : Nat) (ls : List Nat) (a : Nat) (rs : List Nat) :
    dataOf B ⟨ls,a,rs⟩ =
      lanes (encode B ls) (a+B*encode B rs) 0 ls.length (rs.length+1) := rfl

-- Original normalized digits and explicit blank extents, including the
-- single-symbol case, are retained. A missing transition produces a halt
-- tag, rather than pretending to be a new source step.
theorem step_bisim (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Config) (hA : 0<A) (hq : q<Q) (ha : c.scanned<A)
    (hl : ∀ d ∈ c.left, d<A)
    (htarget : ∀ i, table q c.scanned=some i → i.target<Q) :
    ∃ raw, stepToFractionBlock Q A table q (dataOf (max 2 A) c) =
      some (sourceResult (max 2 A) q table c,raw) := by
  let B := max 2 A
  have hB : 0<B := by dsimp [B]; omega
  cases c with
  | mk ls a rs =>
    have hab : a<B := lt_of_lt_of_le ha (by dsimp [B]; omega)
    have hlb : ∀ d ∈ ls,d<B := fun d hd =>
      lt_of_lt_of_le (hl d hd) (by dsimp [B]; omega)
    have hp := PNPStackFractran.pop_push B a (encode B rs) hB hab
    rw [show max 2 A=B from rfl,dataOf_explicit]
    cases he : table q a with
    | none =>
      refine ⟨commonRaw (encode B rs) (encode B rs) B,?_⟩
      simp only [sourceResult,he,dataOf_explicit]
      simpa [B,Nat.add_comm] using haltBlock Q A q a (encode B rs)
        (encode B ls) ls.length (rs.length+1) table hq ha he
    | some i =>
      have hqi := htarget i he
      cases hm : i.move with
      | stay =>
        refine ⟨commonRaw (encode B rs) (encode B rs) B,?_⟩
        simp only [sourceResult,he,hm]
        have hdata : dataOf B (stay ⟨ls,a,rs⟩ i.write) =
            lanes (encode B ls) (B*encode B rs+i.write) 0 ls.length (rs.length+1) := by
          simp [dataOf,stay,pack,encode,push,Nat.add_comm]
        rw [hdata]
        exact stayBlock Q A q a (encode B rs) (encode B ls)
          ls.length (rs.length+1) table i hq ha he hm
      | right =>
        refine ⟨commonRaw (encode B rs) (encode B ls) B +
          (if 2≤rs.length+1 then 2 else 1),?_⟩
        simp only [sourceResult,he,hm]
        have hdata : dataOf B (rightMove ⟨ls,a,rs⟩ i.write) =
            lanes (B*encode B ls+i.write) (encode B rs) 0
              (ls.length+1) (max 1 (rs.length+1-1)) := by
          unfold dataOf
          rw [PNPStackFractran.moveRight B hB _ i.write hab]
          simp [pack,encode,push,hp.2,Nat.add_comm]
        rw [hdata]
        exact rightBlock Q A q a (encode B rs) (encode B ls)
          ls.length (rs.length+1) table i hq ha hqi (by omega) he hm
      | left =>
        let e := ls.headD 0
        let t := encode B (ls.drop 1)
        have el : encode B ls = e+B*t := by
          cases ls <;> simp [e,t,encode,push]
        have ea : e<A := by
          cases ls with
          | nil => simpa [e] using hA
          | cons d ds => exact hl d (by simp)
        have eb : e<B := lt_of_lt_of_le ea (by dsimp [B]; omega)
        have pl := PNPStackFractran.pop_push B e t hB eb
        refine ⟨leftRaw (encode B rs) t (B*encode B rs+i.write) B,?_⟩
        simp only [sourceResult,he,hm]
        have hdata : dataOf B (leftMove ⟨ls,a,rs⟩ i.write) =
            lanes t (B*(B*encode B rs+i.write)+e) 0
              (ls.length-1) (rs.length+1+1) := by
          unfold dataOf
          rw [PNPStackFractran.moveLeft B hB _ i.write hab hlb]
          simp [pack,encode,push,hp.2,el,pl.1,pl.2,Nat.add_comm]
        rw [hdata,el]
        exact leftBlock Q A q a (encode B rs) e t ls.length
          (rs.length+1) table i hq ha ea hqi he hm

theorem raw_step_bisim (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (c : Config) (hA : 0<A) (hq : q<Q) (ha : c.scanned<A)
    (hl : ∀ d ∈ c.left,d<A)
    (htarget : ∀ i, table q c.scanned=some i → i.target<Q) :
    ∃ n, PNPActualInstructionLedger.run (compile Q A table) n
      ⟨mainTag (.q q),dataOf (max 2 A) c⟩ =
      some (sourceResult (max 2 A) q table c) := by
  obtain ⟨n,h⟩ := step_bisim Q A q table c hA hq ha hl htarget
  exact ⟨n,stepToFractionBlock_sound Q A table q _ _ n h⟩

-- Source-written, pending kernel. Actual Agda candidate program table
-- normalization and prime-factor interpretation remain separate owners.
end PNPActualWordBisim

import Welds.PNPActualPhaseRouteExact

namespace PNPActualPackedMacro
open PNPStackEmittedList PNPActualMacroBlock PNPActualPhaseEndpoint

def lanes (l r u ll rr : Nat) : Data := ![l,r,u,ll,rr]

@[simp] theorem lanes_L (l r u ll rr : Nat) : lanes l r u ll rr L = l := rfl
@[simp] theorem lanes_R (l r u ll rr : Nat) : lanes l r u ll rr R = r := rfl
@[simp] theorem lanes_U (l r u ll rr : Nat) : lanes l r u ll rr U = u := rfl
@[simp] theorem lanes_llen (l r u ll rr : Nat) : lanes l r u ll rr llen = ll := rfl
@[simp] theorem lanes_rlen (l r u ll rr : Nat) : lanes l r u ll rr rlen = rr := rfl

-- Arithmetic of the actual five lanes, with scratch restored to zero.
theorem readData (B d t l ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨R,B,U,1⟩ t (lanes l (d+B*t) 0 ll rr) =
      lanes l d t ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,L,R,U] <;> omega

theorem leftPopData (B d t r ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨L,B,U,1⟩ t (lanes (d+B*t) r 0 ll rr) =
      lanes d r t ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,L,R,U] <;> omega

theorem moveUR (l r u ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨U,1,R,1⟩ u (lanes l r u ll rr) =
      lanes l (r+u) 0 ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,U,R]

theorem moveUL (l r u ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨U,1,L,1⟩ u (lanes l r u ll rr) =
      lanes (l+u) r 0 ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,U,L]

theorem moveRU (B l r ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨R,1,U,B⟩ r (lanes l r 0 ll rr) =
      lanes l 0 (B*r) ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,R,U]

theorem moveLU (B l r ll rr : Nat) :
    PNPStackFiveLane.moveData ⟨L,1,U,B⟩ l (lanes l r 0 ll rr) =
      lanes 0 r (B*l) ll rr := by
  funext i
  fin_cases i <;> simp [lanes,PNPStackFiveLane.moveData,lane,L,U]

theorem readExit (q l d t ll rr : Nat) :
    applyBody (lanes l d t ll rr) ⟨mainTag (.quot q d),lane R d,0⟩ =
      ⟨mainTag (.quot q d),lanes l 0 t ll rr⟩ := by
  unfold applyBody
  congr 1
  funext i
  fin_cases i <;> simp [lanes,lane,R]

theorem leftPopExit (q d r t ll rr : Nat) :
    applyBody (lanes d r t ll rr) (takeGive (.leftQuot q d) L d R d) =
      ⟨mainTag (.leftQuot q d),lanes 0 (r+d) t ll rr⟩ := by
  unfold applyBody takeGive
  congr 1
  funext i
  fin_cases i <;> simp [lanes,lane,L,R]

theorem addRight (p : Phase) (b l r u ll rr : Nat) :
    applyBody (lanes l r u ll rr) ⟨mainTag p,0,lane R b⟩ =
      ⟨mainTag p,lanes l (r+b) u ll rr⟩ := by
  unfold applyBody
  congr 1
  funext i
  fin_cases i <;> simp [lanes,lane,R]

theorem addLeft (p : Phase) (b l r u ll rr : Nat) :
    applyBody (lanes l r u ll rr) ⟨mainTag p,0,lane L b⟩ =
      ⟨mainTag p,lanes (l+b) r u ll rr⟩ := by
  unfold applyBody
  congr 1
  funext i
  fin_cases i <;> simp [lanes,lane,L]

-- Bridge the existing digit-dispatch receipts to canonical lane arithmetic.
theorem readPacked (Q A q d t l ll rr : Nat) (table : Nat → Nat → Option Instruction)
    (hq : q<Q) (hd : d<A) :
    phaseAdvance Q A table (.read q) (lanes l (d+max 2 A*t) 0 ll rr) =
      some (⟨mainTag (.quot q d),lanes l 0 t ll rr⟩,2*t+1) := by
  have hb : 0<max 2 A := by omega
  have hda : d<max 2 A := lt_of_lt_of_le hd (le_max_right _ _)
  have h := PNPStackFractran.pop_push (max 2 A) d t hb hda
  have hr : (d+max 2 A*t) % max 2 A = d := h.1
  have ht : (d+max 2 A*t) / max 2 A = t := h.2
  have e := phase_read Q A q table (lanes l (d+max 2 A*t) 0 ll rr) hq
    (by simpa [hr] using hd)
  simpa [hr,ht,readData,readExit] using e

theorem leftPopPacked (Q A q d t r ll rr : Nat) (table : Nat → Nat → Option Instruction)
    (hq : q<Q) (hd : d<A) :
    phaseAdvance Q A table (.leftPop q) (lanes (d+max 2 A*t) r 0 ll rr) =
      some (⟨mainTag (.leftQuot q d),lanes 0 (r+d) t ll rr⟩,2*t+1) := by
  have hb : 0<max 2 A := by omega
  have hda : d<max 2 A := lt_of_lt_of_le hd (le_max_right _ _)
  have h := PNPStackFractran.pop_push (max 2 A) d t hb hda
  have hr : (d+max 2 A*t) % max 2 A = d := h.1
  have ht : (d+max 2 A*t) / max 2 A = t := h.2
  have e := phase_leftPop Q A q table (lanes (d+max 2 A*t) r 0 ll rr) hq
    (by simpa [hr] using hd)
  simpa [hr,ht,leftPopData,leftPopExit] using e

-- Closed raw edge ledger (not a bit-time bound).
def commonRaw (t stack B : Nat) : Nat := 5+4*t+2*stack+2*B*stack
def leftRaw (t lq w B : Nat) : Nat :=
  commonRaw t t B + 5 + 2*w + 2*B*w + 4*lq

theorem stayBlock (Q A q d t l ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (i : Instruction)
    (hq : q<Q) (hd : d<A) (hi : table q d = some i) (hm : i.move = .stay) :
    stepToFractionBlock Q A table q (lanes l (d+max 2 A*t) 0 ll rr) =
      some (⟨mainTag (.q i.target),lanes l (max 2 A*t+i.write) 0 ll rr⟩,
        commonRaw t t (max 2 A)) := by
  simp [stepToFractionBlock,runMacroBlock,phase_q Q A q table _ hq,
    readPacked Q A q d t l ll rr table hq hd,
    phase_quot Q A q d table _ hq hd,phase_action Q A q d table _ hq hd,
    phase_restoreAction Q A q d table _ hq hd,
    moveUR,moveRU,actionSpec,hi,hm,addRight,terminalPhase,mainTag,commonRaw]
  <;> ring

theorem haltBlock (Q A q d t l ll rr : Nat)
    (table : Nat → Nat → Option Instruction)
    (hq : q<Q) (hd : d<A) (hi : table q d = none) :
    stepToFractionBlock Q A table q (lanes l (d+max 2 A*t) 0 ll rr) =
      some (⟨mainTag (.halt q),lanes l (max 2 A*t+d) 0 ll rr⟩,
        commonRaw t t (max 2 A)) := by
  simp [stepToFractionBlock,runMacroBlock,phase_q Q A q table _ hq,
    readPacked Q A q d t l ll rr table hq hd,
    phase_quot Q A q d table _ hq hd,phase_action Q A q d table _ hq hd,
    phase_restoreAction Q A q d table _ hq hd,
    moveUR,moveRU,actionSpec,hi,addRight,terminalPhase,mainTag,commonRaw]
  <;> ring

theorem rightExtent (Q A p l r ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (hp : p<Q) :
    phaseAdvance Q A table (.rightLen p) (lanes l r 0 ll rr) =
      if 2≤rr then some (⟨mainTag (.rightRestore p),lanes l r 0 (ll+1) (rr-2)⟩,1)
      else some (⟨mainTag (.q p),lanes l r 0 (ll+1) rr⟩,1) := by
  have inv := (inventory_tags Q A (.rightLen p)
    (phase_mem_control Q A p hp _ (by simp))).1
  by_cases h : 2≤rr
  · have e := rightLen_long Q A p table (lanes l r 0 ll rr) inv (by simpa using h)
    have ed : (fun j => lanes l r 0 ll rr j - lane rlen 2 j + lane llen 1 j) =
        lanes l r 0 (ll+1) (rr-2) := by
      funext j
      fin_cases j <;> simp [lanes,lane,rlen,llen]
    simp [phaseAdvance,inv,transfer,e,ed,h]
  · have e := rightLen_short Q A p table (lanes l r 0 ll rr) hp (by simpa using (Nat.lt_of_not_ge h))
    have ed : applyBody (lanes l r 0 ll rr) ⟨mainTag (.q p),0,lane llen 1⟩ =
        ⟨mainTag (.q p),lanes l r 0 (ll+1) rr⟩ := by
      unfold applyBody
      congr 1
      funext j
      fin_cases j <;> simp [lanes,lane,llen]
    simp [phaseAdvance,inv,transfer,e,ed,h]

theorem restoreExtent (Q A p l r ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (hp : p<Q) :
    phaseAdvance Q A table (.rightRestore p) (lanes l r 0 ll rr) =
      some (⟨mainTag (.q p),lanes l r 0 ll (rr+1)⟩,1) := by
  have ed : applyBody (lanes l r 0 ll rr) ⟨mainTag (.q p),0,lane rlen 1⟩ =
      ⟨mainTag (.q p),lanes l r 0 ll (rr+1)⟩ := by
    unfold applyBody
    congr 1
    funext j
    fin_cases j <;> simp [lanes,lane,rlen]
  rw [phase_rightRestore Q A p table _ hp,ed]

theorem leftExtent (Q A p l r ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (hp : p<Q) :
    phaseAdvance Q A table (.leftLen p) (lanes l r 0 ll rr) =
      some (⟨mainTag (.q p),lanes l r 0 (ll-1) (rr+1)⟩,1) := by
  have inv := (inventory_tags Q A (.leftLen p)
    (phase_mem_control Q A p hp _ (by simp))).1
  have e := leftLen_exit Q A p table (lanes l r 0 ll rr) hp
  have ed : (fun j => lanes l r 0 ll rr j - lane llen (min 1 ll) j + lane rlen 1 j) =
      lanes l r 0 (ll-1) (rr+1) := by
    funext j
    fin_cases j <;> simp [lanes,lane,llen,rlen] <;> omega
  simp [phaseAdvance,inv,transfer,e,ed]

theorem rightBlock (Q A q d t l ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (i : Instruction)
    (hq : q<Q) (hd : d<A) (hp : i.target<Q) (hr : 0<rr)
    (hi : table q d = some i) (hm : i.move = .right) :
    stepToFractionBlock Q A table q (lanes l (d+max 2 A*t) 0 ll rr) =
      some (⟨mainTag (.q i.target),
        lanes (max 2 A*l+i.write) t 0 (ll+1) (max 1 (rr-1))⟩,
        commonRaw t l (max 2 A) + if 2≤rr then 2 else 1) := by
  by_cases h : 2≤rr
  · have er : rr-2+1=max 1 (rr-1) := by omega
    simp [stepToFractionBlock,runMacroBlock,phase_q Q A q table _ hq,
      readPacked Q A q d t l ll rr table hq hd,
      phase_quot Q A q d table _ hq hd,phase_action Q A q d table _ hq hd,
      phase_restoreAction Q A q d table _ hq hd,moveUR,moveLU,moveUL,
      actionSpec,hi,hm,addLeft,terminalPhase,mainTag,
      rightExtent Q A i.target _ _ _ _ table hp,h,
      restoreExtent Q A i.target _ _ _ _ table hp,er,commonRaw] <;> ring
  · have er : rr=max 1 (rr-1) := by omega
    simp [stepToFractionBlock,runMacroBlock,phase_q Q A q table _ hq,
      readPacked Q A q d t l ll rr table hq hd,
      phase_quot Q A q d table _ hq hd,phase_action Q A q d table _ hq hd,
      phase_restoreAction Q A q d table _ hq hd,moveUR,moveLU,moveUL,
      actionSpec,hi,hm,addLeft,terminalPhase,mainTag,
      rightExtent Q A i.target _ _ _ _ table hp,h,er,commonRaw] <;> ring

theorem leftBlock (Q A q d t e lq ll rr : Nat)
    (table : Nat → Nat → Option Instruction) (i : Instruction)
    (hq : q<Q) (hd : d<A) (he : e<A) (hp : i.target<Q)
    (hi : table q d = some i) (hm : i.move = .left) :
    let B := max 2 A
    let w := B*t+i.write
    stepToFractionBlock Q A table q (lanes (e+B*lq) (d+B*t) 0 ll rr) =
      some (⟨mainTag (.q i.target),lanes lq (B*w+e) 0 (ll-1) (rr+1)⟩,
        leftRaw t lq w B) := by
  simp [stepToFractionBlock,runMacroBlock,phase_q Q A q table _ hq,
    readPacked Q A q d t (e+max 2 A*lq) ll rr table hq hd,
    phase_quot Q A q d table _ hq hd,phase_action Q A q d table _ hq hd,
    phase_restoreAction Q A q d table _ hq hd,moveUR,moveRU,moveUL,
    actionSpec,hi,hm,addRight,terminalPhase,mainTag,
    phase_leftShift Q A i.target table _ hp,phase_restoreLeft Q A i.target table _ hp,
    leftPopPacked Q A i.target e lq _ ll rr table hp he,
    phase_leftQuot Q A i.target e table _ hp he,
    leftExtent Q A i.target _ _ _ _ table hp,leftRaw,commonRaw] <;> ring

-- Each theorem computes the actual existing macro fold, with raw edge
-- accounting. Kernel elaboration deferred. Original word-validity and
-- first-rule code correspondence still required at the candidate ABI.
end PNPActualPackedMacro

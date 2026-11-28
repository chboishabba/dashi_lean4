import Welds.PNPActualPhaseEndpointExact

namespace PNPActualPhaseEndpoint
open PNPStackEmittedList PNPActualMacroBlock

theorem phase_leftPop (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (hd : v L % max 2 A < A) :
    let t : Transfer := ⟨L,max 2 A,U,1⟩
    let k := v L / max 2 A
    let u := PNPStackFiveLane.moveData t k v
    phaseAdvance Q A table (.leftPop q) v =
      some (applyBody u (takeGive (.leftQuot q (v L % max 2 A)) L
        (v L % max 2 A) R (v L % max 2 A)),2*k+1) := by
  dsimp
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.leftPop q)
    (phase_mem_control Q A q hq _ (by simp))
  let t : Transfer := ⟨L,max 2 A,U,1⟩
  let u := PNPStackFiveLane.moveData t (v L/max 2 A) v
  have hr : u L = v L % max 2 A :=
    (PNPStackFiveLane.actualMaximal Q A table (.leftPop q) t v hm hh rfl).2.1
  have he := PNPActualDigitDispatch.left_pop_dispatch Q A q table u hm hh (hr.symm ▸ hd)
  rw [hr] at he
  have hs : step (compile Q A table) ⟨mainTag (.leftPop q),u⟩ =
      some (applyBody u (takeGive (.leftQuot q (v L % max 2 A)) L
        (v L % max 2 A) R (v L % max 2 A))) := by
    simp [step,he,applyBody]
  simp [phaseAdvance,hm,hh,transfer,hs,t,u]

theorem phase_q (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) :
    phaseAdvance Q A table (.q q) v = some (⟨mainTag (.read q),v⟩,1) := by
  have hm := (inventory_tags Q A (.q q)
    (phase_mem_control Q A q hq _ (by simp))).1
  have h := singleton_exit Q A table (.q q) v (go (.read q)) hm rfl rfl
  simp [phaseAdvance,hm,transfer,h,applyBody,go]

theorem phase_quot (Q A q a : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (ha : a < A) :
    phaseAdvance Q A table (.quot q a) v =
      some (⟨mainTag (.action q a),PNPStackFiveLane.moveData ⟨U,1,R,1⟩ (v U) v⟩,2*v U+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.quot q a)
    (phase_mem_digit Q A q a hq ha _ (by simp))
  simpa [applyBody,go] using transfer_singleton Q A table (.quot q a)
    ⟨U,1,R,1⟩ v (go (.action q a)) hm hh rfl rfl rfl

theorem phase_action (Q A q a : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (ha : a < A) :
    let x := (actionSpec table q a).1
    phaseAdvance Q A table (.action q a) v =
      some (⟨mainTag (.restoreAction q a),
        PNPStackFiveLane.moveData ⟨x,1,U,max 2 A⟩ (v x) v⟩,2*v x+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.action q a)
    (phase_mem_digit Q A q a hq ha _ (by simp))
  simpa [applyBody,go] using transfer_singleton Q A table (.action q a)
    ⟨(actionSpec table q a).1,1,U,max 2 A⟩ v
    (go (.restoreAction q a)) hm hh rfl rfl rfl

theorem phase_restoreAction (Q A q a : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (ha : a < A) :
    let x := (actionSpec table q a).1
    let b := (actionSpec table q a).2.1
    let dst := (actionSpec table q a).2.2
    phaseAdvance Q A table (.restoreAction q a) v =
      some (applyBody (PNPStackFiveLane.moveData ⟨U,1,x,1⟩ (v U) v)
        ⟨mainTag dst,0,lane x b⟩,2*v U+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.restoreAction q a)
    (phase_mem_digit Q A q a hq ha _ (by simp))
  apply transfer_singleton Q A table (.restoreAction q a)
    ⟨U,1,(actionSpec table q a).1,1⟩ v _ hm hh rfl
  · simp only [exits]
    cases actionSpec table q a with
    | mk x rest => cases rest; rfl
  · rfl

theorem phase_leftShift (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) :
    phaseAdvance Q A table (.leftShift q) v =
      some (⟨mainTag (.restoreLeft q),PNPStackFiveLane.moveData ⟨R,1,U,max 2 A⟩ (v R) v⟩,2*v R+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.leftShift q)
    (phase_mem_control Q A q hq _ (by simp))
  simpa [applyBody,go] using transfer_singleton Q A table (.leftShift q)
    ⟨R,1,U,max 2 A⟩ v (go (.restoreLeft q)) hm hh rfl rfl rfl

theorem phase_restoreLeft (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) :
    phaseAdvance Q A table (.restoreLeft q) v =
      some (⟨mainTag (.leftPop q),PNPStackFiveLane.moveData ⟨U,1,R,1⟩ (v U) v⟩,2*v U+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.restoreLeft q)
    (phase_mem_control Q A q hq _ (by simp))
  simpa [applyBody,go] using transfer_singleton Q A table (.restoreLeft q)
    ⟨U,1,R,1⟩ v (go (.leftPop q)) hm hh rfl rfl rfl

theorem phase_leftQuot (Q A q a : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (ha : a < A) :
    phaseAdvance Q A table (.leftQuot q a) v =
      some (⟨mainTag (.leftLen q),PNPStackFiveLane.moveData ⟨U,1,L,1⟩ (v U) v⟩,2*v U+1) := by
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.leftQuot q a)
    (phase_mem_digit Q A q a hq ha _ (by simp))
  simpa [applyBody,go] using transfer_singleton Q A table (.leftQuot q a)
    ⟨U,1,L,1⟩ v (go (.leftLen q)) hm hh rfl rfl rfl

theorem phase_rightRestore (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) :
    phaseAdvance Q A table (.rightRestore q) v =
      some (applyBody v ⟨mainTag (.q q),0,lane rlen 1⟩,1) := by
  have hm := (inventory_tags Q A (.rightRestore q)
    (phase_mem_control Q A q hq _ (by simp))).1
  have h := singleton_exit Q A table (.rightRestore q) v
    ⟨mainTag (.q q),0,lane rlen 1⟩ hm rfl rfl
  simp [phaseAdvance,hm,transfer,h]

-- The finite actual emitted phases now have explicit endpoint receipts.
-- Compose their arithmetic on canonical packed data, proving normalized
-- digits and target control bounds from the original candidate rule table.

end PNPActualPhaseEndpoint

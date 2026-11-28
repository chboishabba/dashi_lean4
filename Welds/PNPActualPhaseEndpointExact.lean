import Welds.PNPActualMacroBlockExact
import Welds.PNPChangingStabilizerExact

namespace PNPActualPhaseEndpoint
open PNPStackEmittedList PNPActualMacroBlock

-- Reachable finite inventory: each control q and valid normalized digit a
-- has both private tags. No new enumeration or phase ordering.
theorem phase_mem_control (Q A q : Nat) (hq : q < Q) :
    ∀ p ∈ ([.q q,.read q,.leftShift q,.restoreLeft q,.leftPop q,
      .rightLen q,.rightRestore q,.leftLen q,.halt q] : List Phase),
      p ∈ phases Q A := by
  intro p hp
  unfold phases
  apply List.mem_flatMap.mpr
  exact ⟨q,List.mem_range.mpr hq,List.mem_append_left _ hp⟩

theorem phase_mem_digit (Q A q a : Nat) (hq : q < Q) (ha : a < A) :
    ∀ p ∈ ([.quot q a,.action q a,.restoreAction q a,.leftQuot q a] : List Phase),
      p ∈ phases Q A := by
  intro p hp
  unfold phases
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_range.mpr hq,List.mem_append_right _ ?_⟩
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr ha,hp⟩

theorem inventory_tags (Q A : Nat) (p : Phase) (hp : p ∈ phases Q A) :
    mainTag p ∈ inventory Q A ∧ midTag p ∈ inventory Q A := by
  unfold inventory
  constructor <;> rw [List.mem_eraseDups] <;>
    exact List.mem_flatMap.mpr ⟨p,hp,by simp⟩

-- Generic singleton exit, used by q, quotient, action, restore,
-- leftShift, restoreLeft, leftQuot and rightRestore.
def applyBody (v : Data) (b : Body) : State :=
  ⟨b.dst,fun i => v i-b.take i+b.give i⟩

theorem singleton_exit (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (v : Data) (b : Body)
    (hm : mainTag p ∈ inventory Q A)
    (hlist : phaseList (max 2 A) (List.range A).reverse table (mainTag p) = [b])
    (hzero : b.take = 0) :
    step (compile Q A table) ⟨mainTag p,v⟩ = some (applyBody v b) := by
  have he : enabled ⟨mainTag p,b⟩ ⟨mainTag p,v⟩ := by simp [enabled,hzero]
  unfold step
  rw [compiled_first Q A table _ hm]
  simp [hlist,tagged,first,he,applyBody]

theorem transfer_singleton (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data) (b : Body)
    (hm : mainTag p ∈ inventory Q A) (hh : midTag p ∈ inventory Q A)
    (ht : transfer (max 2 A) table p = some t)
    (hexit : exits (List.range A).reverse table p = [b]) (hz : b.take = 0) :
    let k := v t.x/t.a
    phaseAdvance Q A table p v =
      some (applyBody (PNPStackFiveLane.moveData t k v) b,2*k+1) := by
  dsimp
  let u := PNPStackFiveLane.moveData t (v t.x/t.a) v
  have hr : u t.x < t.a := by
    have e := (PNPStackFiveLane.actualMaximal Q A table p t v hm hh ht).2.1
    rw [show u t.x = v t.x % t.a from e]
    exact Nat.mod_lt _ (PNPStackFiveLane.actualTransferGood A table p t ht).2
  have en : enabled ⟨mainTag p,b⟩ ⟨mainTag p,u⟩ := by simp [enabled,hz]
  have he : step (compile Q A table) ⟨mainTag p,u⟩ = some (applyBody u b) := by
    unfold step
    rw [PNPStackFiveLane.selectExit Q A table p t u hm hh ht hr,hexit]
    simp [tagged,first,en,applyBody]
  simp [phaseAdvance,hm,hh,ht,he,u]

theorem phase_read (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (hd : v R % max 2 A < A) :
    let t : Transfer := ⟨R,max 2 A,U,1⟩
    let k := v R / max 2 A
    let u := PNPStackFiveLane.moveData t k v
    phaseAdvance Q A table (.read q) v =
      some (applyBody u ⟨mainTag (.quot q (v R % max 2 A)),lane R (v R % max 2 A),0⟩,2*k+1) := by
  dsimp
  obtain ⟨hm,hh⟩ := inventory_tags Q A (.read q)
    (phase_mem_control Q A q hq _ (by simp))
  let t : Transfer := ⟨R,max 2 A,U,1⟩
  let u := PNPStackFiveLane.moveData t (v R/max 2 A) v
  have hr : u R = v R % max 2 A :=
    (PNPStackFiveLane.actualMaximal Q A table (.read q) t v hm hh rfl).2.1
  have he := PNPActualDigitDispatch.read_dispatch Q A q table u hm hh (hr.symm ▸ hd)
  rw [hr] at he
  have hs : step (compile Q A table) ⟨mainTag (.read q),u⟩ =
      some (applyBody u ⟨mainTag (.quot q (v R % max 2 A)),lane R (v R % max 2 A),0⟩) := by
    simp [step,he,applyBody]
  simp [phaseAdvance,hm,hh,transfer,hs,t,u]

-- Bounded digit range is not implied by < max 2 A when A=1;
-- in that case actual packed words use only normalized digit zero.
theorem singleton_alphabet_remainder (v : Nat) (h : v = 0) :
    v % max 2 1 < 1 := by simp [h]

theorem rightLen_short (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) (h : v rlen < 2) :
    step (compile Q A table) ⟨mainTag (.rightLen q),v⟩ =
      some (applyBody v ⟨mainTag (.q q),0,lane llen 1⟩) := by
  have hm := (inventory_tags Q A (.rightLen q)
    (phase_mem_control Q A q hq _ (by simp))).1
  have hn : ¬ enabled ⟨mainTag (.rightLen q),takeGive (.rightRestore q) rlen 2 llen 1⟩
      ⟨mainTag (.rightLen q),v⟩ := by
    intro he
    have hh := he.2 rlen
    simp [takeGive,lane] at hh
    omega
  unfold step
  rw [compiled_first Q A table _ hm]
  simp [phaseList,transfer,mainTag,exits,tagged,first,hn,takeGive,enabled,applyBody]

theorem leftLen_exit (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hq : q < Q) :
    step (compile Q A table) ⟨mainTag (.leftLen q),v⟩ =
      some ⟨mainTag (.q q),fun i => v i-lane llen (min 1 (v llen)) i+lane rlen 1 i⟩ := by
  have hm := (inventory_tags Q A (.leftLen q)
    (phase_mem_control Q A q hq _ (by simp))).1
  have he : enabled ⟨mainTag (.leftLen q),takeGive (.q q) llen 1 rlen 1⟩
      ⟨mainTag (.leftLen q),v⟩ ↔ 1 ≤ v llen := by
    constructor
    · intro h; simpa [takeGive,lane] using h.2 llen
    · intro h
      refine ⟨rfl,?_⟩
      intro i
      by_cases hi : i=llen
      · subst i; simpa [takeGive,lane] using h
      · simp [takeGive,lane,hi]
  unfold step
  rw [compiled_first Q A table _ hm]
  by_cases h : 1 ≤ v llen
  · simp [phaseList,transfer,mainTag,exits,tagged,first,he,h,takeGive,min_eq_left h]
  · have hz : v llen = 0 := by omega
    simp [phaseList,transfer,mainTag,exits,tagged,first,he,h,hz,enabled,lane]

-- Still needed: instantiate transfer_singleton across the full left/right
-- arithmetic routes, leftPop remainder step, and compare to packed source
-- moves. This is not a claim of total endpoint bisimulation.
end PNPActualPhaseEndpoint

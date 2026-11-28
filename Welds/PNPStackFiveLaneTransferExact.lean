import Mathlib
import Welds.PNPStackEmittedListExact
import Welds.PNPStackPriorityTransportExact

namespace PNPStackFiveLane
open PNPStackEmittedList

-- Full five-lane transport, on the actual natively emitted priority list.
-- The private tag is part of State, and all spectator lanes are retained.
def moveData (t : Transfer) (k : Nat) (v : Data) : Data :=
  fun i => v i - lane t.x (t.a*k) i + lane t.y (t.b*k) i

theorem guard_iff (p : Phase) (t : Transfer) (v : Data) :
    enabled ⟨mainTag p,loopBody p t⟩ ⟨mainTag p,v⟩ ↔ t.a≤v t.x := by
  constructor
  · intro h
    simpa [loopBody,lane] using h.2 t.x
  · intro h
    refine ⟨rfl,?_⟩
    intro i
    by_cases e : i=t.x
    · subst i
      simpa [loopBody,lane] using h
    · simp [loopBody,lane,e]

theorem firstEdge (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t) (ha : t.a≤v t.x) :
    step (compile Q A table) ⟨mainTag p,v⟩ =
      some ⟨midTag p,moveData t 1 v⟩ := by
  have h := (emitted_loop Q A table p t hm hh ht).1
  unfold step
  rw [first_local,show (State.mk (mainTag p) v).tag=mainTag p from rfl,h]
  have en := (guard_iff p t v).mpr ha
  simp [tagged,first,en,loopBody,moveData]

theorem returnEdge (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t) :
    step (compile Q A table) ⟨midTag p,v⟩ = some ⟨mainTag p,v⟩ := by
  have h := (emitted_loop Q A table p t hm hh ht).2
  unfold step
  rw [first_local,show (State.mk (midTag p) v).tag=midTag p from rfl,h]
  simp [tagged,first,enabled,go]

def run (P : List Edge) : Nat → State → Option State
  | 0,s => some s
  | k+1,s => (step P s).bind (run P k)

theorem cycle (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t) (ha : t.a≤v t.x) :
    run (compile Q A table) 2 ⟨mainTag p,v⟩ =
      some ⟨mainTag p,moveData t 1 v⟩ := by
  simp only [run,firstEdge Q A table p t v hm hh ht ha,Option.bind_some,
    returnEdge Q A table p t (moveData t 1 v) hm hh ht]

theorem sourceLane (t : Transfer) (k : Nat) (v : Data) (hxy : t.x≠t.y) :
    moveData t k v t.x = v t.x-t.a*k := by
  simp [moveData,lane,hxy]

theorem spectator (t : Transfer) (k : Nat) (v : Data) (i : Fin 5)
    (hx : i≠t.x) (hy : i≠t.y) :
    moveData t k v i=v i := by simp [moveData,lane,hx,hy]

theorem composeMove (t : Transfer) (v : Data) (k : Nat)
    (hxy : t.x≠t.y) (h : t.a*(k+1)≤v t.x) :
    moveData t k (moveData t 1 v)=moveData t (k+1) v := by
  funext i
  by_cases hx : i=t.x
  · subst i
    simp [moveData,lane,hxy,Nat.mul_succ]
    omega
  · by_cases hy : i=t.y
    · subst i
      simp [moveData,lane,Ne.symm hxy,Nat.mul_succ]
      omega
    · simp [moveData,lane,hx,hy]

theorem repeatExact (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data) (k : Nat)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t)
    (hxy : t.x≠t.y) (h : t.a*k≤v t.x) :
    run (compile Q A table) (2*k) ⟨mainTag p,v⟩ =
      some ⟨mainTag p,moveData t k v⟩ := by
  induction k generalizing v with
  | zero => simp [run,moveData,lane]
  | succ k ih =>
    have ha : t.a≤v t.x := by rw [Nat.mul_succ] at h; omega
    have hk : t.a*k≤moveData t 1 v t.x := by
      rw [sourceLane t 1 v hxy,Nat.mul_one]
      rw [Nat.mul_succ] at h
      omega
    rw [show 2*(k+1)=2*k+2 by omega]
    simp only [run,firstEdge Q A table p t v hm hh ht ha,Option.bind_some,
      returnEdge Q A table p t (moveData t 1 v) hm hh ht]
    rw [ih (moveData t 1 v) hk,composeMove t v k hxy h]

theorem maximalExact (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t)
    (hxy : t.x≠t.y) (ha : 0<t.a) :
    let k := v t.x/t.a
    run (compile Q A table) (2*k) ⟨mainTag p,v⟩ =
      some ⟨mainTag p,moveData t k v⟩ ∧
    moveData t k v t.x=v t.x%t.a ∧
    ¬ enabled ⟨mainTag p,loopBody p t⟩ ⟨mainTag p,moveData t k v⟩ := by
  dsimp
  have h := Nat.div_add_mod (v t.x) t.a
  have hk : t.a*(v t.x/t.a)≤v t.x := by omega
  have he : moveData t (v t.x/t.a) v t.x=v t.x%t.a := by
    rw [sourceLane _ _ _ hxy]
    omega
  refine ⟨repeatExact Q A table p t v _ hm hh ht hxy hk,he,?_⟩
  rw [guard_iff,he]
  exact not_le_of_gt (Nat.mod_lt _ ha)

-- The emitted exit list is now selected after the maximal transfer.
theorem selectExit (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t) (ha : v t.x<t.a) :
    first (compile Q A table) ⟨mainTag p,v⟩ =
      first (tagged (mainTag p) (exits (List.range A).reverse table p)) ⟨mainTag p,v⟩ := by
  rw [first_local,show (State.mk (mainTag p) v).tag=mainTag p from rfl,
    (emitted_loop Q A table p t hm hh ht).1]
  have hn : ¬enabled ⟨mainTag p,loopBody p t⟩ ⟨mainTag p,v⟩ :=
    fun e => (not_le_of_gt ha) ((guard_iff p t v).mp e)
  simp [tagged,first,hn]

-- Full raw-list phase pair now has a native repeat theorem with
-- spectator lanes preserved, not merely the earlier two-lane model.
-- Whole instruction composition (digit dispatch, extent branch, source
-- code and prime valuation bridge) remains separate from this theorem.
-- Every transfer produced by the actual emitter has a positive
-- divisor and distinct source/destination lanes, including action
-- phases whose stack is selected by the candidate rule table.
theorem actionLane (table : Nat → Nat → Option Instruction) (q a : Nat) :
    (actionSpec table q a).1 = L ∨ (actionSpec table q a).1 = R := by
  unfold actionSpec
  split
  · exact Or.inr rfl
  · rename_i i hi
    cases i.move <;> simp

theorem actualTransferGood (A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer)
    (h : transfer (max 2 A) table p=some t) :
    t.x≠t.y ∧ 0<t.a := by
  cases p <;> simp only [transfer,Option.some.injEq] at h
  all_goals try contradiction
  all_goals subst t
  all_goals try (constructor <;> first | decide | omega)
  all_goals rename_i q a
  all_goals rcases actionLane table q a with hl | hr
  all_goals simp [hl,hr,L,R,U]

theorem actualMaximal (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (t : Transfer) (v : Data)
    (hm : mainTag p∈inventory Q A) (hh : midTag p∈inventory Q A)
    (ht : transfer (max 2 A) table p=some t) :
    let k := v t.x/t.a
    run (compile Q A table) (2*k) ⟨mainTag p,v⟩ =
      some ⟨mainTag p,moveData t k v⟩ ∧
    moveData t k v t.x=v t.x%t.a ∧
    ¬ enabled ⟨mainTag p,loopBody p t⟩ ⟨mainTag p,moveData t k v⟩ :=
  maximalExact Q A table p t v hm hh ht
    (actualTransferGood A table p t ht).1 (actualTransferGood A table p t ht).2

end PNPStackFiveLane

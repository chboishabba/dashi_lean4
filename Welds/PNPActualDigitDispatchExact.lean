import Welds.PNPStackFiveLaneTransferExact
import Welds.PNPSignedOrbitBoundaryExact

namespace PNPActualDigitDispatch
open PNPStackEmittedList

-- The emitter uses descending normalized digits. Prove priority
-- directly for the native tagged list, not an unordered digit relation.
theorem descending_first (p : Tag) (body : Nat → Body) (v : Data)
    (x A : Nat)
    (guard : ∀ d, enabled ⟨p,body d⟩ ⟨p,v⟩ ↔ d ≤ x)
    (hx : x < A) :
    first (tagged p ((List.range A).reverse.map body)) ⟨p,v⟩ =
      some ⟨p,body x⟩ := by
  induction A with
  | zero => omega
  | succ A ih =>
    rw [List.range_succ,List.reverse_append]
    simp only [List.reverse_cons,List.reverse_nil,List.nil_append,
      List.singleton_append,List.map_cons,tagged,first]
    by_cases h : A ≤ x
    · have e : A = x := by omega
      simp [guard,h,e]
    · have hlt : x < A := by omega
      simpa [guard,h,tagged] using ih hlt

theorem read_guard (q d : Nat) (v : Data) :
    enabled ⟨mainTag (.read q),⟨mainTag (.quot q d),lane R d,0⟩⟩
      ⟨mainTag (.read q),v⟩ ↔ d ≤ v R := by
  constructor
  · intro h
    simpa [lane] using h.2 R
  · intro h
    refine ⟨rfl,?_⟩
    intro i
    by_cases hi : i = R
    · subst i
      simpa [lane] using h
    · simp [lane,hi]

theorem left_pop_guard (q d : Nat) (v : Data) :
    enabled ⟨mainTag (.leftPop q),takeGive (.leftQuot q d) L d R d⟩
      ⟨mainTag (.leftPop q),v⟩ ↔ d ≤ v L := by
  constructor
  · intro h
    simpa [takeGive,lane] using h.2 L
  · intro h
    refine ⟨rfl,?_⟩
    intro i
    by_cases hi : i = L
    · subst i
      simpa [takeGive,lane] using h
    · simp [takeGive,lane,hi]

-- Exit from the actual read loop after its quotient/remainder transfer.
theorem read_dispatch (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hm : mainTag (.read q) ∈ inventory Q A)
    (hh : midTag (.read q) ∈ inventory Q A)
    (hx : v R < A) :
    first (compile Q A table) ⟨mainTag (.read q),v⟩ =
      some ⟨mainTag (.read q),⟨mainTag (.quot q (v R)),lane R (v R),0⟩⟩ := by
  have hB : v R < max 2 A := lt_of_lt_of_le hx (le_max_right _ _)
  rw [PNPStackFiveLane.selectExit Q A table (.read q)
    ⟨R,max 2 A,U,1⟩ v hm hh rfl hB]
  exact descending_first (mainTag (.read q))
    (fun d => ⟨mainTag (.quot q d),lane R d,0⟩) v (v R) A
    (read_guard q · v) hx

theorem left_pop_dispatch (Q A q : Nat) (table : Nat → Nat → Option Instruction)
    (v : Data) (hm : mainTag (.leftPop q) ∈ inventory Q A)
    (hh : midTag (.leftPop q) ∈ inventory Q A)
    (hx : v L < A) :
    first (compile Q A table) ⟨mainTag (.leftPop q),v⟩ =
      some ⟨mainTag (.leftPop q),takeGive (.leftQuot q (v L)) L (v L) R (v L)⟩ := by
  have hB : v L < max 2 A := lt_of_lt_of_le hx (le_max_right _ _)
  rw [PNPStackFiveLane.selectExit Q A table (.leftPop q)
    ⟨L,max 2 A,U,1⟩ v hm hh rfl hB]
  exact descending_first (mainTag (.leftPop q))
    (fun d => takeGive (.leftQuot q d) L d R d) v (v L) A
    (left_pop_guard q · v) hx

end PNPActualDigitDispatch

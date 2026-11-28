import Welds.PNPActualEmittedNoncancellationExact

namespace PNPActualInventoryClosure
open PNPStackEmittedList PNPActualPrimeLayout PNPActualPrimeRun
open PNPActualPhaseEndpoint PNPPrimeValuationPriority

def PhaseBound (Q A : Nat) : Phase → Prop
  | .q q | .read q | .leftShift q | .restoreLeft q | .leftPop q |
    .rightLen q | .rightRestore q | .leftLen q | .halt q => q<Q
  | .quot q a | .action q a | .restoreAction q a | .leftQuot q a =>
    q<Q ∧ a<A

theorem phaseBound_of_mem (Q A : Nat) (p : Phase) (hp : p ∈ phases Q A) :
    PhaseBound Q A p := by
  unfold phases at hp
  obtain ⟨q,hq,hp⟩ := List.mem_flatMap.mp hp
  have hq' := List.mem_range.mp hq
  rcases List.mem_append.mp hp with hp|hp
  · simp only [List.mem_cons,List.mem_singleton] at hp
    rcases hp with e|e|e|e|e|e|e|e|e <;> subst p <;> simp [PhaseBound,hq']
  · obtain ⟨a,ha,hp⟩ := List.mem_flatMap.mp hp
    have ha' := List.mem_range.mp ha
    simp only [List.mem_cons,List.mem_singleton] at hp
    rcases hp with e|e|e|e <;> subst p <;> simp [PhaseBound,hq',ha']

theorem mem_of_phaseBound (Q A : Nat) (p : Phase) (h : PhaseBound Q A p) :
    p ∈ phases Q A := by
  cases p <;> simp only [PhaseBound] at h
  all_goals first
    | exact phase_mem_control Q A _ h _ (by simp)
    | exact phase_mem_digit Q A _ _ h.1 h.2 _ (by simp)

theorem phase_of_tag (Q A : Nat) (p : Tag) (h : p ∈ inventory Q A) :
    p.phase ∈ phases Q A := by
  unfold inventory at h
  rw [List.mem_eraseDups] at h
  obtain ⟨a,ha,h⟩ := List.mem_flatMap.mp h
  simp at h
  rcases h with h|h <;> subst p <;> exact ha

theorem tag_of_phase (Q A : Nat) (p : Tag) (h : p.phase ∈ phases Q A) :
    p ∈ inventory Q A := by
  rcases p with ⟨phase,mid⟩
  have tags := inventory_tags Q A phase h
  cases mid
  · exact tags.1
  · exact tags.2

def LegalTable (Q A : Nat) (table : Nat → Nat → Option Instruction) : Prop :=
  ∀ q a i, q<Q → a<A → table q a=some i → i.target<Q ∧ i.write<A

theorem exits_dest_bound (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (legal : LegalTable Q A table) (p : Phase) (hp : PhaseBound Q A p)
    (b : Body) (hb : b ∈ exits (List.range A).reverse table p) :
    PhaseBound Q A b.dst.phase := by
  cases p with
  | q q =>
    simp [exits] at hb
    subst b
    exact hp
  | read q =>
    obtain ⟨a,ha,e⟩ := List.mem_map.mp hb
    subst b
    exact ⟨hp,List.mem_range.mp (by simpa using ha)⟩
  | quot q a =>
    simp [exits] at hb
    subst b
    exact hp
  | action q a =>
    simp [exits] at hb
    subst b
    exact hp
  | restoreAction q a =>
    cases ht : table q a with
    | none =>
      simp [exits,actionSpec,ht] at hb
      subst b
      exact hp.1
    | some i =>
      have hi := legal q a i hp.1 hp.2 ht
      cases hm : i.move <;> simp [exits,actionSpec,ht,hm] at hb <;>
        subst b <;> exact hi.1
  | leftShift q =>
    simp [exits] at hb
    subst b
    exact hp
  | restoreLeft q =>
    simp [exits] at hb
    subst b
    exact hp
  | leftPop q =>
    obtain ⟨a,ha,e⟩ := List.mem_map.mp hb
    subst b
    exact ⟨hp,List.mem_range.mp (by simpa using ha)⟩
  | leftQuot q a =>
    simp [exits] at hb
    subst b
    exact hp.1
  | rightLen q =>
    simp [exits] at hb
    rcases hb with e|e <;> subst b <;> exact hp
  | rightRestore q =>
    simp [exits] at hb
    subst b
    exact hp
  | leftLen q =>
    simp [exits] at hb
    rcases hb with e|e <;> subst b <;> exact hp
  | halt q => simp [exits] at hb

theorem phaseList_dest (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (legal : LegalTable Q A table) (p : Tag) (hp : p ∈ inventory Q A)
    (b : Body) (hb : b ∈ phaseList (max 2 A) (List.range A).reverse table p) :
    b.dst ∈ inventory Q A := by
  have bound := phaseBound_of_mem Q A p.phase (phase_of_tag Q A p hp)
  apply tag_of_phase
  apply mem_of_phaseBound
  rcases p with ⟨p,mid⟩
  cases ht : transfer (max 2 A) table p with
  | none =>
    cases mid with
    | false =>
      exact exits_dest_bound Q A table legal p bound b (by simpa [phaseList,ht] using hb)
    | true => simp [phaseList,ht] at hb
  | some t =>
    cases mid with
    | false =>
      have h' : b=loopBody p t ∨ b ∈ exits (List.range A).reverse table p := by
        simpa [phaseList,ht] using hb
      rcases h' with e|h'
      · subst b
        exact bound
      · exact exits_dest_bound Q A table legal p bound b h'
    | true =>
      have e : b=go p := by simpa [phaseList,ht] using hb
      subst b
      exact bound

theorem emit_member (body : Tag → List Body) (ps : List Tag)
    (r : E) (h : r ∈ emit body ps) :
    r.src ∈ ps ∧ r.body ∈ body r.src := by
  induction ps with
  | nil => simp [emit] at h
  | cons p ps ih =>
    simp only [emit,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨b,hb,e⟩ := List.mem_map.mp h
      subst r
      exact ⟨by simp,hb⟩
    · obtain ⟨hs,hb⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hs,hb⟩

theorem compiled_layout (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (legal : LegalTable Q A table) (r : E) (hr : r ∈ compile Q A table) :
    ReducedLayout Q A r := by
  obtain ⟨src,body⟩ := emit_member _ _ r hr
  exact ⟨src,phaseList_dest Q A table legal r.src src r.body body,
    PNPActualEmittedNoncancellation.actual_compiled_separated Q A table r hr⟩

theorem integerState_injective_on_inventory (Q A : Nat) (s t : State)
    (hs : s.tag ∈ inventory Q A) (ht : t.tag ∈ inventory Q A)
    (h : integerState Q A s = integerState Q A t) : s=t := by
  have hv := congrArg Nat.factorization h
  unfold integerState at hv
  rw [factorization_pack _ (valuation_prime Q A _),
      factorization_pack _ (valuation_prime Q A _)] at hv
  have ve (i : Lane Q A) : vector Q A s.data s.tag i =
      vector Q A t.data t.tag i := by
    have e := congrArg (fun v : Valuation => v (lanePrime Q A i)) hv
    simpa only [valuation_at] using e
  have tag : s.tag=t.tag := by
    have e := ve (.inr ⟨s.tag,hs⟩)
    by_contra ne
    simp [vector,ne] at e
  have data : s.data=t.data := funext fun i => ve (.inl i)
  cases s
  cases t
  simp_all

-- A closed legal emitted run retains canonical tags throughout.
theorem step_inventory (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (legal : LegalTable Q A table) (s t : State)
    (h : step (compile Q A table) s = some t) : t.tag ∈ inventory Q A := by
  unfold step at h
  cases he : first (compile Q A table) s with
  | none => simp [he] at h
  | some r =>
    simp [he] at h
    subst t
    exact (compiled_layout Q A table legal r
      (first_spec _ _ _ he).1).2.1

theorem run_inventory (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (legal : LegalTable Q A table) (s t : State) (k : Nat)
    (hs : s.tag ∈ inventory Q A)
    (h : PNPActualInstructionLedger.run (compile Q A table) k s = some t) :
    t.tag ∈ inventory Q A := by
  induction k generalizing s with
  | zero =>
    simp [PNPActualInstructionLedger.run] at h
    subst t
    exact hs
  | succ k ih =>
    simp only [PNPActualInstructionLedger.run] at h
    cases he : step (compile Q A table) s with
    | none => simp [he] at h
    | some u =>
      exact ih u (step_inventory Q A table legal s u he) (by simpa [he] using h)

-- Native source-written proof bodies: kernel execution deferred. The
-- actual candidate rule export still needs its cross-language ABI proof.
end PNPActualInventoryClosure

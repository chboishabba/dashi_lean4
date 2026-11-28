import Welds.PNPActualPrimeRunExact

namespace PNPActualEmittedNoncancellation
open PNPStackEmittedList PNPActualPrimeRun PNPActualPrimeLayout PNPPrimeValuationPriority

theorem lane_disjoint (x y : Fin 5) (a b : Nat) (h : x ≠ y) :
    ∀ i, lane x a i = 0 ∨ lane y b i = 0 := by
  intro i
  by_cases e : i=x
  · right
    subst i
    simp [lane,h]
  · left
    simp [lane,e]

theorem exits_separated (digits : List Nat) (table : Nat → Nat → Option Instruction)
    (p : Phase) (b : Body) (h : b ∈ exits digits table p) :
    Separated ⟨mainTag p,b⟩ := by
  cases p with
  | q q =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | read q =>
    obtain ⟨a,_,e⟩ := List.mem_map.mp h
    subst b
    simp [Separated,mainTag]
  | quot q a =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | action q a =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | restoreAction q a =>
    cases ht : table q a with
    | none =>
      simp [exits,actionSpec,ht] at h
      subst b
      simp [Separated,mainTag]
    | some i =>
      cases hm : i.move <;> simp [exits,actionSpec,ht,hm] at h <;> subst b <;>
        simp [Separated,mainTag]
  | leftShift q =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | restoreLeft q =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | leftPop q =>
    obtain ⟨a,_,e⟩ := List.mem_map.mp h
    subst b
    exact ⟨by simp [takeGive,mainTag],lane_disjoint L R a a (by decide)⟩
  | leftQuot q a =>
    simp [exits] at h
    subst b
    simp [Separated,go,mainTag]
  | rightLen q =>
    simp [exits] at h
    rcases h with h|h
    · subst b
      exact ⟨by simp [takeGive,mainTag],lane_disjoint rlen llen 2 1 (by decide)⟩
    · subst b
      simp [Separated,mainTag]
  | rightRestore q =>
    simp [exits] at h
    subst b
    simp [Separated,mainTag]
  | leftLen q =>
    simp [exits] at h
    rcases h with h|h
    · subst b
      exact ⟨by simp [takeGive,mainTag],lane_disjoint llen rlen 1 1 (by decide)⟩
    · subst b
      simp [Separated,mainTag]
  | halt q => simp [exits] at h

theorem phaseList_separated (A : Nat) (digits : List Nat)
    (table : Nat → Nat → Option Instruction) (p : Tag) (b : Body)
    (h : b ∈ phaseList (max 2 A) digits table p) :
    Separated ⟨p,b⟩ := by
  rcases p with ⟨p,mid⟩
  cases ht : transfer (max 2 A) table p with
  | none =>
    cases mid with
    | false =>
      have h' : b ∈ exits digits table p := by simpa [phaseList,ht] using h
      exact exits_separated digits table p b h'
    | true => simp [phaseList,ht] at h
  | some t =>
    cases mid with
    | false =>
      have h' : b = loopBody p t ∨ b ∈ exits digits table p := by
        simpa [phaseList,ht] using h
      rcases h' with h'|h'
      · subst b
        exact ⟨by simp [loopBody,midTag],lane_disjoint t.x t.y t.a t.b
          (PNPStackFiveLane.actualTransferGood A table p t ht).1⟩
      · exact exits_separated digits table p b h'
    | true =>
      have e : b=go p := by simpa [phaseList,ht] using h
      subst b
      simp [Separated,go,mainTag]

theorem emit_separated (body : Tag → List Body) (ps : List Tag)
    (good : ∀ p b, b ∈ body p → Separated ⟨p,b⟩)
    (r : E) (h : r ∈ emit body ps) : Separated r := by
  induction ps with
  | nil => simp [emit] at h
  | cons p ps ih =>
    simp only [emit,List.mem_append] at h
    rcases h with h|h
    · obtain ⟨b,hb,e⟩ := List.mem_map.mp h
      subst r
      exact good p b hb
    · exact ih h

theorem actual_compiled_separated (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (r : E) (h : r ∈ compile Q A table) : Separated r :=
  emit_separated _ _ (phaseList_separated A _ table) r h

theorem actual_compiled_coprime (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (r : E) (h : r ∈ compile Q A table) :
    Nat.Coprime (pack (fractionEdge Q A r).take) (pack (fractionEdge Q A r).give) :=
  separated_coprime Q A r (actual_compiled_separated Q A table r h)

-- No cancellation of emitted take/give products, including repeated
-- source rule controls, follows from the actual private tags and lanes.
-- Destination inventory membership for legal target tables is a distinct
-- decoding obligation; original Agda parser parity remains cross-language.
end PNPActualEmittedNoncancellation

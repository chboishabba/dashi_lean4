import Welds.PNPActualWordBisimExact
import Welds.PNPHyperfabricOwnedEventsExact

namespace PNPActualPrimeLayout
open PNPStackEmittedList PNPPrimeValuationPriority

-- Exactly five data lanes and the finite actual native tag inventory.
abbrev Lane (Q A : Nat) := Fin 5 ⊕ {t : Tag // t ∈ inventory Q A}

instance tagFinite (Q A : Nat) : Fintype {t : Tag // t ∈ inventory Q A} :=
  Fintype.ofFinset (inventory Q A).toFinset (by intro t; simp)

noncomputable def lanePrime (Q A : Nat) (i : Lane Q A) : Nat :=
  PNPActualLaneAllocation.allocLanePrime ((Fintype.equivFin (Lane Q A)) i).val

theorem lanePrime_injective (Q A : Nat) : Function.Injective (lanePrime Q A) := by
  intro i j h
  apply (Fintype.equivFin (Lane Q A)).injective
  apply Fin.ext
  exact PNPActualLaneAllocation.alloc_injective h

theorem lanePrime_prime (Q A : Nat) (i : Lane Q A) : Nat.Prime (lanePrime Q A i) :=
  PNPActualLaneAllocation.alloc_prime _

noncomputable def valuation (Q A : Nat) (v : Lane Q A → Nat) : Valuation :=
  ∑ i : Lane Q A, Finsupp.single (lanePrime Q A i) (v i)

theorem valuation_at (Q A : Nat) (v : Lane Q A → Nat) (i : Lane Q A) :
    valuation Q A v (lanePrime Q A i) = v i := by
  classical
  simp [valuation,Finsupp.sum_apply,Finsupp.single_apply,
    (lanePrime_injective Q A).eq_iff]

theorem valuation_prime (Q A : Nat) (v : Lane Q A → Nat) :
    PrimeSupported (valuation Q A v) := by
  classical
  intro p hp
  by_contra hn
  have hz : valuation Q A v p = 0 := by
    simp only [valuation,Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have ne : lanePrime Q A i ≠ p := fun e => hn (e ▸ lanePrime_prime Q A i)
    simp [Finsupp.single_apply,ne,Ne.symm ne]
  exact (Finsupp.mem_support_iff.mp hp) hz

theorem valuation_mono_iff (Q A : Nat) (u v : Lane Q A → Nat) :
    valuation Q A u ≤ valuation Q A v ↔ ∀ i,u i≤v i := by
  classical
  constructor
  · intro h i
    have e := h (lanePrime Q A i)
    simpa only [valuation_at] using e
  · intro h p
    simp only [valuation,Finsupp.sum_apply]
    apply Finset.sum_le_sum
    intro i _
    by_cases e : lanePrime Q A i=p
    · simpa [Finsupp.single_apply,e] using h i
    · simp [Finsupp.single_apply,e,Ne.symm e]

def vector (Q A : Nat) (data : Data) (tag : Tag) : Lane Q A → Nat
  | .inl i => data i
  | .inr i => if i.val=tag then 1 else 0

theorem actual_guard (Q A : Nat) (r : PNPStackEmittedList.Edge) (s : State)
    (hr : r.src ∈ inventory Q A) :
    enabled r s ↔
      valuation Q A (vector Q A r.body.take r.src) ≤
        valuation Q A (vector Q A s.data s.tag) := by
  rw [valuation_mono_iff]
  constructor
  · rintro ⟨e,h⟩ i
    cases i with
    | inl i => exact h i
    | inr i => simp [vector,e]
  · intro h
    have t := h (.inr ⟨r.src,hr⟩)
    refine ⟨?_,fun i => h (.inl i)⟩
    by_contra ne
    simp [vector,ne] at t

noncomputable def fractionEdge (Q A : Nat) (r : PNPStackEmittedList.Edge) :
    PNPPrimeValuationPriority.Edge :=
  ⟨valuation Q A (vector Q A r.body.take r.src),
   valuation Q A (vector Q A r.body.give r.body.dst),
   valuation_prime Q A _,valuation_prime Q A _⟩

noncomputable def integerState (Q A : Nat) (s : State) : Nat :=
  pack (valuation Q A (vector Q A s.data s.tag))

theorem literal_guard (Q A : Nat) (r : PNPStackEmittedList.Edge)
    (s : State) (hr : r.src ∈ inventory Q A) :
    enabled r s ↔ pack (fractionEdge Q A r).take ∣ integerState Q A s :=
  (actual_guard Q A r s hr).trans
    (guard_iff_dvd _ _ (fractionEdge Q A r).takePrime (valuation_prime Q A _))

theorem first_literal (Q A : Nat) (P : List PNPStackEmittedList.Edge)
    (s : State) (hP : ∀ r∈P,r.src ∈ inventory Q A) :
    (first P s).map (fractionEdge Q A) =
      firstLiteral (integerState Q A s) (P.map (fractionEdge Q A)) := by
  induction P with
  | nil => rfl
  | cons r rs ih =>
    have h := literal_guard Q A r s (hP r (by simp))
    by_cases en : enabled r s
    · simp [first,firstLiteral,en,h.mp en]
    · have nd := fun d => en (h.mpr d)
      simp [first,firstLiteral,en,nd,ih (fun e he => hP e (by simp [he]))]

-- The actual integer guard is the displayed denominator before any
-- cancellation; disjoint take/give support must be shown for emitted edges.
-- Successor product uses the existing transition_product theorem once
-- the original vector subtraction and destination inventory are proved.
end PNPActualPrimeLayout

import Mathlib
import Welds.PNPStackEmittedListExact

namespace PNPActualInstructionLedger
open PNPStackEmittedList

-- Composition on the original emitted list, not a new program per phase.
def run (P : List Edge) : Nat → State → Option State
  | 0, s => some s
  | n+1, s => (step P s).bind (run P n)

theorem run_append (P : List Edge) (a b : Nat) (s : State) :
    run P (a+b) s = (run P a s).bind (run P b) := by
  induction a generalizing s with
  | zero => simp [run]
  | succ a ih =>
    rw [show a+1+b = (a+b)+1 by omega]
    simp only [run]
    cases h : step P s with
    | none => simp
    | some t => simpa using ih t

theorem compose_phases (P : List Edge) (a b : Nat) (s m t : State)
    (h₁ : run P a s = some m) (h₂ : run P b m = some t) :
    run P (a+b) s = some t := by
  rw [run_append,h₁]
  exact h₂

-- Full finite path composition; each receipt is a real run of P.
inductive Path (P : List Edge) : State → State → Nat → Prop where
  | nil (s : State) : Path P s s 0
  | cons {s m t : State} {a b : Nat}
      (head : run P a s = some m) (tail : Path P m t b) :
      Path P s t (a+b)

theorem path_run {P : List Edge} {s t : State} {n : Nat}
    (h : Path P s t n) : run P n s = some t := by
  induction h with
  | nil => rfl
  | cons head tail ih => exact compose_phases _ _ _ _ _ _ head ih

-- A ledger records all categories, including failure/restart in setup or
-- suffix, and does not assign a unit physical price to a virtual jump.
structure Ledger where
  setup : Nat
  queries : List Nat
  core : List Nat
  resume : Nat
  suffix : Nat

def total (L : Ledger) : Nat :=
  L.setup + L.queries.sum + L.core.sum + L.resume + L.suffix

theorem sum_bound (xs : List Nat) (B : Nat) (h : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul]
    omega

theorem total_bound (L : Ledger) (q c : Nat)
    (hq : ∀ x ∈ L.queries, x ≤ q)
    (hc : ∀ x ∈ L.core, x ≤ c) :
    total L ≤ L.setup + L.queries.length*q + L.core.length*c + L.resume + L.suffix := by
  have a := sum_bound L.queries q hq
  have b := sum_bound L.core c hc
  unfold total
  omega

theorem fits_of_bound (L : Ledger) (T q c : Nat)
    (hq : ∀ x ∈ L.queries, x ≤ q)
    (hc : ∀ x ∈ L.core, x ≤ c)
    (fit : L.setup + L.queries.length*q + L.core.length*c + L.resume + L.suffix ≤ T) :
    total L ≤ T := le_trans (total_bound L q c hq hc) fit

end PNPActualInstructionLedger

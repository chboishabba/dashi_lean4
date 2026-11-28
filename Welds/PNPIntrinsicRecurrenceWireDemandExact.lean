import Welds.PNPActualPrimeRunExact
import Welds.PNPChangingStabilizerExact
import Welds.PNPQuotientDemandBoundaryExact

namespace PNPIntrinsicRecurrence
open PNPStackEmittedList PNPActualInstructionLedger

-- The original emitted run is a partial deterministic transition.
-- A genuine full-state loop can be repeated, with the original length.
theorem repeatRun (P : List PNPStackEmittedList.Edge) (s : State)
    (period : Nat) (h : run P period s = some s) (k : Nat) :
    run P (k*period) s = some s := by
  induction k with
  | zero => simp [run]
  | succ k ih =>
    rw [Nat.succ_mul,run_append,ih]
    exact h

theorem periodSuffix (P : List PNPStackEmittedList.Edge)
    (s t : State) (period k tail : Nat)
    (loop : run P period s = some s)
    (finish : run P tail s = some t) :
    run P (k*period+tail) s = some t := by
  rw [run_append,repeatRun P s period loop k]
  exact finish

theorem primePeriodSuffix (Q A : Nat) (table : Nat → Nat → Option Instruction)
    (s t : State) (period k tail : Nat)
    (loop : run (compile Q A table) period s = some s)
    (finish : run (compile Q A table) tail s = some t) :
    PNPActualPrimeRun.integerRun Q A (compile Q A table) (k*period+tail)
      (PNPActualPrimeLayout.integerState Q A s) =
      some (PNPActualPrimeLayout.integerState Q A t) := by
  rw [PNPActualPrimeRun.compiled_primeRunExact,
    periodSuffix _ _ _ period k tail loop finish]
  rfl

-- Exact quotient dynamics may reduce observation work, but it does not
-- change the physical run length in periodSuffix. Repeated local rule
-- templates do not imply the full-state premise.
end PNPIntrinsicRecurrence

namespace PNPExplicitWireDemand
open scoped BigOperators

-- Each Boolean wire is its full truth vector on a finite probe domain.
-- This is NOT the communication matrix rank of a single Boolean output.
abbrev Wire (D : Type*) := D → ZMod 2

noncomputable def space {D : Type*} (xs : List (Wire D)) :
    Submodule (ZMod 2) (Wire D) :=
  Submodule.span (ZMod 2) {f | f ∈ xs}

noncomputable def rank {D : Type*} [Fintype D] (xs : List (Wire D)) : Nat :=
  Module.finrank (ZMod 2) (space xs)

theorem rank_append_one {D : Type*} [Fintype D]
    (xs : List (Wire D)) (w : Wire D) :
    rank (w::xs) ≤ rank xs+1 := by
  classical
  have eq : space (w::xs) =
      Submodule.span (ZMod 2) {w} ⊔ space xs := by
    unfold space
    rw [← Submodule.span_union]
    congr 1
    ext x
    simp
  have h₁ : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ({w} : Set (Wire D))) ≤ 1 := by
    exact?
  have h₂ : Module.finrank (ZMod 2)
      (Submodule.span (ZMod 2) ({w} : Set (Wire D)) ⊔ space xs) ≤
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({w} : Set (Wire D))) +
        Module.finrank (ZMod 2) (space xs) := by
    exact?
  unfold rank
  rw [eq]
  omega

theorem rank_paid {D : Type*} [Fintype D]
    (base new : List (Wire D)) :
    rank (new++base) ≤ rank base+new.length := by
  induction new with
  | nil => simp
  | cons w ws ih =>
    have h := rank_append_one (ws++base) w
    simp only [List.cons_append,List.length_cons]
    omega

-- A mandatory OUTPUT family must actually lie in the span of base
-- wires and generated wires. This is a genuine lower bound for the
-- explicit multi-output interface, not a premise automatically true
-- of the single-bit SAT decision interface.
theorem demanded_rank_bound {D : Type*} [Fintype D]
    (base new demanded : List (Wire D))
    (mustProduce : space demanded ≤ space (new++base)) :
    rank demanded ≤ rank base+new.length := by
  have h : rank demanded ≤ rank (new++base) := by
    unfold rank
    exact Submodule.finrank_mono mustProduce
  exact h.trans (rank_paid base new)

-- Any claim that an arbitrary SAT algorithm must expose a large
-- demanded family needs its own semantic inevitability theorem.
-- Exponentially many rival vectors or high matrix/tensor rank alone
-- do not inhabit mustProduce.
end PNPExplicitWireDemand

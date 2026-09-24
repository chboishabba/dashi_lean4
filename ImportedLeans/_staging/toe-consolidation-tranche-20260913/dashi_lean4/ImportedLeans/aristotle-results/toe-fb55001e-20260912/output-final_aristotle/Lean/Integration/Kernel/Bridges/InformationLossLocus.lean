import Integration.Kernel.Quotient

/-!
# Bridge: process stacks ↔ where information is first lost along a chain

Another deliberately narrow bridge.  A chain of processing stages is a sequence
of maps; the question the donor lane keeps asking is *at which stage* a
distinction that mattered stopped being visible.  This file gives that question
a definition and proves the two facts that make it worth asking.

## What is proved

* `run` — the state after `n` stages.
* **`collapse_persists`** — once two inputs agree at some stage they agree at
  every later stage: no downstream stage restores a distinction that an upstream
  stage destroyed.  So "where was it first lost?" is a well-posed question with
  a single answer.
* `firstLoss` — the first stage index (up to a bound) at which the two inputs
  become indistinguishable, and `firstLoss_spec`: at the returned index the
  states really do agree.
* **`locus_is_pair_relative`** — the answer is a property of the pair being
  distinguished, not of the stack: on one stack two different pairs are lost at
  two different stages, so no function of the stack alone reports where
  information is lost.

**Claim boundary.**  Stages are arbitrary endomaps of a finite carrier chosen
here.  Nothing models any real pipeline, instrument or codec.
-/

namespace Integration.Kernel.Bridges.InformationLossLocus

open Integration.Kernel.Quotient

universe u

variable {X : Type u}

/-! ## §1 A stack and its runs -/

/-- The state after `n` stages of the stack `f`. -/
def run (f : ℕ → X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => f n (run f n x)

@[simp] theorem run_zero (f : ℕ → X → X) (x : X) : run f 0 x = x := rfl

@[simp] theorem run_succ (f : ℕ → X → X) (n : ℕ) (x : X) :
    run f (n + 1) x = f n (run f n x) := rfl

/-- **No stage restores a lost distinction.**  If two inputs are already
indistinguishable after `n` stages, they are indistinguishable after every later
stage. -/
theorem collapse_persists {f : ℕ → X → X} {a b : X} {n : ℕ} (h : run f n a = run f n b) :
    ∀ m, n ≤ m → run f m a = run f m b := by
  intro m hm
  induction m with
  | zero =>
      obtain rfl : n = 0 := Nat.le_zero.1 hm
      exact h
  | succ m ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 (Nat.lt_succ_of_le hm) with hlt | rfl
      · rw [run_succ, run_succ, ih (Nat.lt_succ_iff.1 hlt)]
      · exact h

/-- The first stage (searched up to `bound`) at which the two inputs have become
indistinguishable. -/
def firstLoss [DecidableEq X] (f : ℕ → X → X) (a b : X) (bound : ℕ) : Option ℕ :=
  (List.range (bound + 1)).find? (fun n => decide (run f n a = run f n b))

theorem firstLoss_spec [DecidableEq X] {f : ℕ → X → X} {a b : X} {bound n : ℕ}
    (h : firstLoss f a b bound = some n) : run f n a = run f n b := by
  have := List.find?_some h
  simpa using this

/-! ## §2 The locus is a property of the pair -/

/-- The carrier: four distinguishable inputs. -/
abbrev Datum := Fin 4

/-- Stage `0` merges `0` with `1`; stage `1` merges `2` with `3`; later stages
do nothing. -/
def stack : ℕ → Datum → Datum
  | 0 => fun d => if d = 1 then 0 else d
  | 1 => fun d => if d = 3 then 2 else d
  | _ => id

theorem pair01_lost_at_one : firstLoss stack 0 1 3 = some 1 := by decide

theorem pair23_lost_at_two : firstLoss stack 2 3 3 = some 2 := by decide

/-- **Where information is lost depends on which distinction you cared about.**
On one and the same stack the two pairs are lost at different stages, so no
function of the stack alone answers the question. -/
theorem locus_is_pair_relative :
    firstLoss stack 0 1 3 ≠ firstLoss stack 2 3 3 := by decide

/-- And the distinction really is gone downstream, not merely absent at the
first index found. -/
theorem pair01_stays_lost : ∀ m, 1 ≤ m → run stack m 0 = run stack m 1 :=
  collapse_persists (by decide)

end Integration.Kernel.Bridges.InformationLossLocus

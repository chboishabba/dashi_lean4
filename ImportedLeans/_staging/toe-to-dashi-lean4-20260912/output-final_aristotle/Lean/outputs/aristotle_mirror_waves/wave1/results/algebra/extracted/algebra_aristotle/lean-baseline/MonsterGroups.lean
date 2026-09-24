import Mathlib
import AgdaMirror.MonsterWalk

/-!
# Lean mirror of `MonsterGroups.agda` (genuine, fully proved)

A boundary predicate marks states that end a group; `countGroups` counts the
groups in a trace (`0` for the empty trace, else `1 +` the boundaries hit in the
tail).  We prove the genuine combinatorial laws: the empty/singleton counts, the
positivity of any nonempty count, and the upper bound by the trace length.
-/

namespace AgdaMirror.MonsterGroups

open AgdaMirror.MonsterWalk

/-- A boundary predicate: does this state end a group? -/
abbrev Boundary := State → Bool

/-- Count boundaries hit in a trace tail. -/
def countBoundaries (b : Boundary) : List State → Nat
  | [] => 0
  | t :: ts => (if b t then 1 else 0) + countBoundaries b ts

/-- Count groups in a trace: `0` for empty, else `1 +` the tail boundaries. -/
def countGroups (b : Boundary) : List State → Nat
  | [] => 0
  | _ :: ss => 1 + countBoundaries b ss

@[simp] theorem countGroups_nil (b : Boundary) : countGroups b [] = 0 := rfl

@[simp] theorem countGroups_singleton (b : Boundary) (s : State) :
    countGroups b [s] = 1 := rfl

/-- Any nonempty trace has at least one group. -/
theorem countGroups_cons_pos (b : Boundary) (s : State) (ss : List State) :
    1 ≤ countGroups b (s :: ss) := by
  simp [countGroups]

/-- The boundary count is bounded by the tail length. -/
theorem countBoundaries_le_length (b : Boundary) (ts : List State) :
    countBoundaries b ts ≤ ts.length := by
  induction ts with
  | nil => simp [countBoundaries]
  | cons t ts ih =>
    simp only [countBoundaries, List.length_cons]
    by_cases h : b t <;> simp [h] <;> omega

/-- The group count is bounded by the trace length. -/
theorem countGroups_le_length (b : Boundary) (ss : List State) :
    countGroups b ss ≤ ss.length := by
  cases ss with
  | nil => simp
  | cons s ss =>
    simp only [countGroups, List.length_cons]
    have := countBoundaries_le_length b ss
    omega

end AgdaMirror.MonsterGroups

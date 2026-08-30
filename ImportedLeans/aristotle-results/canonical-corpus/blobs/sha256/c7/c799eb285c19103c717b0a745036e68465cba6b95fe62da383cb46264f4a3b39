import RequestProject.MoonshineAddress

/-!
# FractranWalk: lifting a FRACTRAN program into the moonshine coordinate system

This module realises the next move: take a concrete computational process — a
**FRACTRAN program** (Conway's Turing-complete language of fraction lists) — and
watch its state trajectory *walk across the 194 irrep biomes* of the moonshine
lattice built in `MoonshineAddress`.

## FRACTRAN semantics

A program is a list of fractions `(a, b)` (numerator, denominator).  From state
`n`, the machine takes the **first** fraction `a/b` in the list for which `n·a/b`
is an integer (`b ∣ n·a`), and moves to `n·a/b`.  If no fraction applies, the
machine halts (the state is a fixed point).

* `fractranStep P n` — one step (or `none` if halted).
* `fractranState P start t` — the state after `t` steps (halted states persist).
* `trajectory P start steps` — the first `steps` states as a list.

## The lift into moonshine space

`fractranLift P start t = moonshinePoint (fractranState P start t)` sends each
time `t` to the program's point in ℤ^(194×104).  The **biome** of a state is the
irrep it primarily occupies, `biomeOf n = n % 194`.

## Worked example

`mulProgram = [(3, 2)]` started at `8 = 2³` rewrites every factor of 2 into a 3:
`8 → 12 → 18 → 27` and then halts at `27 = 3³`.  Its biome trajectory is
`[8, 12, 18, 27, …]` — four distinct biomes — so the program genuinely walks
across the moonshine landscape:

* `mul_trajectory`           — the trace is `[8, 12, 18, 27, 27, 27]` (verified).
* `mul_walks_biomes`         — successive biomes `8 ≠ 12 ≠ 18 ≠ 27` are distinct.
* `mul_visits_four_biomes`   — at least four distinct biomes are visited.
* `mul_moves_in_moonshine`   — the moonshine coordinate genuinely changes on the
  first step (witnessed at irrep 0, page 0, via `separation_local`).
-/

namespace FractranWalk

open MoonshineAddress

/-! ## FRACTRAN syntax and semantics -/

/-- A FRACTRAN program: an ordered list of fractions `(numerator, denominator)`. -/
abbrev FractranProgram := List (Nat × Nat)

/-- One FRACTRAN step from state `n`: take the first fraction `a/b` with
`b ∣ n·a` (so `n·a/b` is an integer) and move to `n·a/b`; `none` if halted. -/
def fractranStep (P : FractranProgram) (n : Nat) : Option Nat :=
  P.findSome? (fun f =>
    if f.2 ≠ 0 ∧ (n * f.1) % f.2 = 0 then some (n * f.1 / f.2) else none)

/-- The state after `t` FRACTRAN steps starting from `start`.  A halted state is
a fixed point, so the trajectory is well defined for all `t`. -/
def fractranState (P : FractranProgram) (start : Nat) : Nat → Nat
  | 0 => start
  | t + 1 =>
    match fractranStep P (fractranState P start t) with
    | some m => m
    | none => fractranState P start t

/-- The first `steps` states of the trajectory, as a list. -/
def trajectory (P : FractranProgram) (start steps : Nat) : List Nat :=
  (List.range steps).map (fractranState P start)

/-! ## The lift into the moonshine coordinate system -/

/-- **The FRACTRAN lift.**  Send each time `t` to the program's point in the
20 176-dimensional moonshine lattice ℤ^(194×104). -/
def fractranLift (P : FractranProgram) (start : Nat) (t : Nat) :
    Fin 194 × Fin numPages → Int :=
  moonshinePoint (fractranState P start t)

/-- The biome (primary irrep) of a state: `n % 194`. -/
def biomeOf (n : Nat) : Fin 194 := ⟨n % 194, Nat.mod_lt _ (by decide)⟩

/-- The biome the program occupies at time `t`. -/
def fractranBiome (P : FractranProgram) (start : Nat) (t : Nat) : Fin 194 :=
  biomeOf (fractranState P start t)

/-! ## Worked example: the multiplication program `[(3,2)]` -/

/-- `mulProgram = [(3, 2)]` rewrites factors of 2 into factors of 3. -/
def mulProgram : FractranProgram := [(3, 2)]

/-- Started at `8 = 2³`, the trajectory is `8 → 12 → 18 → 27` and then halts. -/
theorem mul_trajectory : trajectory mulProgram 8 6 = [8, 12, 18, 27, 27, 27] := by
  native_decide

/-- The program walks: successive biomes are pairwise distinct over the active
part of the run. -/
theorem mul_walks_biomes :
    fractranBiome mulProgram 8 0 ≠ fractranBiome mulProgram 8 1 ∧
    fractranBiome mulProgram 8 1 ≠ fractranBiome mulProgram 8 2 ∧
    fractranBiome mulProgram 8 2 ≠ fractranBiome mulProgram 8 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The program visits at least four distinct biomes. -/
theorem mul_visits_four_biomes :
    ((List.range 4).map (fractranBiome mulProgram 8)).Nodup := by
  native_decide

/-- **The lift genuinely moves.**  On the first step the moonshine coordinate at
irrep `0`, page `0` changes — the program does not stay put in moonshine space.
Proved via the `separation_local` theorem (states `8` and `12` differ modulo the
Monster prime `71 = mp 0`). -/
theorem mul_moves_in_moonshine :
    fractranLift mulProgram 8 0 (⟨0, by decide⟩, ⟨0, by decide⟩) ≠
    fractranLift mulProgram 8 1 (⟨0, by decide⟩, ⟨0, by decide⟩) := by
  have h0 : fractranState mulProgram 8 0 = 8 := by native_decide
  have h1 : fractranState mulProgram 8 1 = 12 := by native_decide
  show moonshineCoord (fractranState mulProgram 8 0) _ _
     ≠ moonshineCoord (fractranState mulProgram 8 1) _ _
  rw [h0, h1]
  exact separation_local 8 12 ⟨0, by decide⟩ ⟨0, by decide⟩ rfl ⟨0, by decide⟩
    (by decide)

end FractranWalk

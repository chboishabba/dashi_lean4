import RequestProject.Holograms
import RequestProject.AristoTask
import Lean

/-!
# DualAtlas: the dual coordinate atlas and the dual-atlas functor

The *dual atlas* dualizes each prime power `p^e ↦ e^p` of `|𝕄|`:

| Prime power | Dualized | Meaning            |
|-------------|----------|--------------------|
| `2^46`      | `46^2`   | Cognitive manifold |
| `3^20`      | `20^3`   | Semantic triads    |
| `5^9`       | `9^5`    | Muse cycles        |
| `7^6`       | `6^7`    | Heptads            |
| `11^2`      | `2^11`   | Hemispheres        |
| `13^3`      | `3^13`   | Deep recursion     |

It exposes:

* `DualCoordinate` — dual coordinate `(cog, triad, harm)`.
* the cognitive `46×2` grid and semantic `20×3` recursion projections.
* the harmonic cell classifier.
* `#dualstratify` — reflect a declaration into a dual coordinate.
* `#atlas` — combined primal + dual dispatcher.
* `dualFunctor_involutive` — the dual-atlas functor is involutive.
-/

open Lean Meta Elab Command

namespace DualAtlas

/-! ## Data structure -/

/-- Dual coordinate of a declaration. -/
structure DualCoordinate where
  cog   : Nat
  triad : Nat
  harm  : Nat
deriving Repr, DecidableEq

/-! ## Algorithms (cognitive grid, semantic triad, harmonic classifier) -/

/-- §6.1 Cognitive grid projection, mapping a hash into the `46×2` grid. -/
def cogProj (h : Nat) : Nat := (h % 92) + 1

/-- §6.2 Semantic triad projection, mapping a hash into the `20×3` recursion. -/
def triadProj (h : Nat) : Nat := (h % 60) / 3

/-- §6.3 Harmonic cell classifier code, priority `13 > 11 > 7 > 5 > default`. -/
def harmCode (h : Nat) : Nat :=
  if h % 13 == 0 then 13
  else if h % 11 == 0 then 11
  else if h % 7 == 0 then 7
  else if h % 5 == 0 then 5
  else 0

/-- Human-readable harmonic cell label. -/
def harmLabel (h : Nat) : String :=
  if h % 13 == 0 then "Recursion (3^13)"
  else if h % 11 == 0 then "Hemispheres (2^11)"
  else if h % 7 == 0 then "Heptad (6^7)"
  else if h % 5 == 0 then "Muse Cycle (9^5)"
  else "Trivector Default"

/-- Dual projection of a hash into a `DualCoordinate`. -/
def dualCoord (h : Nat) : DualCoordinate :=
  { cog := cogProj h, triad := triadProj h, harm := harmCode h }

/-! ### Range guarantees for the projections -/

/-- The cognitive index lies in the `46×2 = 92`-cell grid, `1 ≤ cog ≤ 92`. -/
theorem cogProj_mem (h : Nat) : 1 ≤ cogProj h ∧ cogProj h ≤ 92 := by
  unfold cogProj
  omega

/-- The semantic triad index lies in the `20×3` recursion, `triad ≤ 19`. -/
theorem triadProj_le (h : Nat) : triadProj h ≤ 19 := by
  unfold triadProj
  omega

/-! ## The dual-atlas functor and its involutivity -/

/-- The primal atlas: the six structured prime powers of `|𝕄|` as `(base, exp)` pairs. -/
def primalAtlas : List (ℕ × ℕ) :=
  [(2, 46), (3, 20), (5, 9), (7, 6), (11, 2), (13, 3)]

/-- The dual-atlas functor: dualize every prime power `p^e ↦ e^p`. -/
def dualFunctor (l : List (ℕ × ℕ)) : List (ℕ × ℕ) := l.map Holograms.dualizePair

/-- The dual atlas, obtained by applying the dual functor to the primal atlas. -/
def dualAtlas : List (ℕ × ℕ) := dualFunctor primalAtlas

/-- **The dual-atlas functor is involutive**: dualizing twice is the identity,
the formal justification that the dual atlas is a faithful re-coordinatisation. -/
theorem dualFunctor_involutive : Function.Involutive dualFunctor := by
  intro l
  simp [dualFunctor, Holograms.dualizePair, List.map_map]

/-- Concretely, the dual atlas is the swapped list of structured prime powers. -/
theorem dualAtlas_eq :
    dualAtlas = [(46, 2), (20, 3), (9, 5), (6, 7), (2, 11), (3, 13)] := by
  decide

/-- Applying the dual functor to the dual atlas recovers the primal atlas. -/
theorem dualFunctor_dualAtlas : dualFunctor dualAtlas = primalAtlas :=
  dualFunctor_involutive primalAtlas

/-! ## Reflection commands -/

/-- `#dualstratify f` reflects declaration `f` into a dual coordinate. -/
syntax (name := dualstratifyCmd) "#dualstratify " ident : command

@[command_elab dualstratifyCmd]
def elabDualstratify : CommandElab := fun stx => do
  match stx with
  | `(#dualstratify $id:ident) => do
    let env ← getEnv
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    match env.find? name with
    | some info =>
      match info.value? with
      | some e =>
        let h := e.hash.toNat
        let c := dualCoord h
        logInfo s!"[Aristo Dual Reflection] Stratifying: {name}\n  ├── Cognitive Index (46×2): {c.cog}\n  ├── Semantic Triad (20×3): {c.triad}\n  └── Harmonic Cell: {harmLabel h}"
      | none => throwError "declaration {name} has no value to reflect"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #dualstratify command"

/-- `#atlas f` is the combined primal + dual dispatcher. -/
syntax (name := atlasCmd) "#atlas " ident : command

@[command_elab atlasCmd]
def elabAtlas : CommandElab := fun stx => do
  match stx with
  | `(#atlas $id:ident) => do
    let env ← getEnv
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    match env.find? name with
    | some info =>
      match info.value? with
      | some e =>
        let h := e.hash.toNat
        let p := AristoTask.primalCoord h
        let d := dualCoord h
        logInfo s!"[Aristo Combined Atlas] {name}\n  ┌ Primal ─ size:{p.size} cell:{p.cell} depth:{p.depth}\n  └ Dual   ─ cog:{d.cog} triad:{d.triad} harm:{harmLabel h}"
      | none => throwError "declaration {name} has no value to reflect"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #atlas command"

/-! ## Test suite -/

#dualstratify Nat.add
#dualstratify List.map
#dualstratify Prod.fst

#atlas Nat.add

end DualAtlas

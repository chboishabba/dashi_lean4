import RequestProject.Holograms
import Lean

/-!
# AristoTask: the primal coordinate atlas

The *primal atlas* assigns to every Lean declaration a coordinate in
`Monster-divisor space`, using the reflected hash of the declaration's value.

* `size`  — index into the `424 488 960`-element divisor space.
* `cell`  — harmonic cell from the prime-signature partition (mod 5/7/11/13).
* `depth` — semantic recursion depth, bounded by the 3-adic depth bound (`≤ 20`).
-/

open Lean Meta Elab Command

namespace AristoTask

/-- Primal coordinate of a declaration. -/
structure AristoCoordinate where
  size  : Nat
  cell  : Nat
  depth : Nat
deriving Repr, DecidableEq

/-- Harmonic cell code from the prime-signature partition, priority `13>11>7>5`. -/
def cellCode (h : Nat) : Nat :=
  if h % 13 == 0 then 13
  else if h % 11 == 0 then 11
  else if h % 7 == 0 then 7
  else if h % 5 == 0 then 5
  else 0

/-- Primal projection of a hash into a `AristoCoordinate`.  The `size` index ranges
over the `424 488 960`-element divisor space; this literal is exactly
`Holograms.monsterOrder.divisors.card` (see `Holograms.monster_divisor_count`) and is
used directly here to keep the projection efficiently computable. -/
def primalCoord (h : Nat) : AristoCoordinate :=
  { size  := h % 424488960
  , cell  := cellCode h
  , depth := h % 21 }

/-- The primal `depth` always respects the 3-adic depth bound (`≤ 20`). -/
theorem primalCoord_depth_le (h : Nat) : (primalCoord h).depth ≤ 20 := by
  simp only [primalCoord]
  omega

/-- `#stratify f` prints the primal coordinate of declaration `f`. -/
syntax (name := stratifyCmd) "#stratify " ident : command

@[command_elab stratifyCmd]
def elabStratify : CommandElab := fun stx => do
  match stx with
  | `(#stratify $id:ident) => do
    let env ← getEnv
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    match env.find? name with
    | some info =>
      match info.value? with
      | some e =>
        let h := e.hash.toNat
        let c := primalCoord h
        logInfo s!"[Aristo Reflection] Stratifying: {name}\n  ├── Size (divisor index): {c.size}\n  ├── Cell (harmonic): {c.cell}\n  └── Depth (3-adic ≤ 20): {c.depth}"
      | none => throwError "declaration {name} has no value to reflect"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #stratify command"

/-! ## Test suite -/

#stratify Nat.add
#stratify List.map
#stratify Prod.fst

end AristoTask

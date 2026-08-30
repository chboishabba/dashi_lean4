import RequestProject.DualAtlas
import RequestProject.SVG
import Lean

/-!
# Introspect: the introspective projection layer

This is the third layer of the Aristo atlas: where the system *sees itself* and
computes where every declaration lands in the fused primal+dual coordinate space.

* `IntrospectivePanel` — abstract comic panel for one declaration.
* `mkPanel` / `projectPanel` — the introspective projector.
* layout fusion rules (`fuse`).
* `#introspect` — project a single declaration.
* `#atlasmap` — project *every* declaration of the project and print the map.
* `projectProject` — the reusable enumerator used by the SVG/animation layers.
-/

open Lean Meta Elab Command

namespace Introspect

open DualAtlas AristoTask

/-- The abstract comic panel for one declaration: its primal & dual coordinates,
the fused 3-axis atlas position `(x, y, z)`, and a style class. -/
structure IntrospectivePanel where
  name   : Name
  primal : AristoCoordinate
  dual   : DualCoordinate
  x      : Nat   -- cognitive axis (46×2 grid column, `1 ≤ x ≤ 92`)
  y      : Nat   -- semantic axis (depth fused with triad)
  z      : Nat   -- harmonic depth (style class, `0 ≤ z ≤ 4`)
  style  : Nat   -- panel style code (shape/color class)
deriving Repr

/-- Map a harmonic-cell code (`13/11/7/5/0`) to a compact style class `0..4`. -/
def styleOfHarm : Nat → Nat
  | 13 => 4   -- recursion
  | 11 => 3   -- hemispheres
  | 7  => 2   -- heptad
  | 5  => 1   -- Muse cycle
  | _  => 0   -- trivector default

/-- Human label for a style class. -/
def styleName : Nat → String
  | 4 => "Recursion (3^13)"
  | 3 => "Hemispheres (2^11)"
  | 2 => "Heptad (6^7)"
  | 1 => "Muse Cycle (9^5)"
  | _ => "Trivector Default"

/-- Layout fusion rules (atlas §3):

* `x = dual.cog`                — cognitive axis, the `46×2` grid column.
* `y = primal.depth + 3·dual.triad` — semantic axis, depth fused with the triad.
* `z = styleOfHarm dual.harm`   — harmonic depth.
-/
def fuse (p : AristoCoordinate) (d : DualCoordinate) : Nat × Nat × Nat :=
  (d.cog, p.depth + 3 * d.triad, styleOfHarm d.harm)

/-- Build the introspective panel for a declaration with reflected hash `h`. -/
def mkPanel (name : Name) (h : Nat) : IntrospectivePanel :=
  let p := primalCoord h
  let d := dualCoord h
  let (x, y, z) := fuse p d
  { name := name, primal := p, dual := d, x := x, y := y, z := z, style := z }

/-- The introspective projector: reflect a declaration into its panel. -/
def projectPanel (decl : Name) : MetaM IntrospectivePanel := do
  let env ← getEnv
  match env.find? decl with
  | some info =>
    match info.value? with
    | some e => return mkPanel decl e.hash.toNat
    | none   => throwError "declaration {decl} has no value to reflect"
  | none => throwError "unknown declaration {decl}"

/-- Is `s` a project-source declaration name (in one of our namespaces and not an
auto-generated internal helper)?  This defines "the entire source code". -/
def isProjectDecl (s : String) : Bool :=
  let inProject :=
    s.startsWith "Holograms." || s.startsWith "AristoTask." || s.startsWith "DualAtlas."
  let internal := (s.splitOn "._").length > 1 || (s.splitOn "match_").length > 1
  inProject && !internal

/-- Enumerate and project every project declaration into a panel list. -/
def projectProject : CommandElabM (List IntrospectivePanel) := do
  let env ← getEnv
  let mut panels : List IntrospectivePanel := []
  for (name, info) in env.constants.toList do
    if isProjectDecl name.toString then
      if let some e := info.value? then
        panels := mkPanel name e.hash.toNat :: panels
  -- deterministic order: by style, then x, then y, then name
  return panels.toArray.qsort (fun a b =>
    if a.style ≠ b.style then a.style > b.style
    else if a.x ≠ b.x then a.x < b.x
    else if a.y ≠ b.y then a.y < b.y
    else a.name.toString < b.name.toString) |>.toList

/-! ## Commands -/

/-- `#introspect f` projects declaration `f` into the introspective atlas. -/
syntax (name := introspectCmd) "#introspect " ident : command

@[command_elab introspectCmd]
def elabIntrospect : CommandElab := fun stx => do
  match stx with
  | `(#introspect $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let panel ← liftTermElabM <| Meta.MetaM.run' (projectPanel name)
    logInfo s!"[Introspective Atlas]\n  name:   {panel.name}\n  primal: size:{panel.primal.size} cell:{panel.primal.cell} depth:{panel.primal.depth}\n  dual:   cog:{panel.dual.cog} triad:{panel.dual.triad} harm:{panel.dual.harm}\n  x:      {panel.x}\n  y:      {panel.y}\n  z:      {panel.z}\n  style:  {panel.style} ({styleName panel.style})"
  | _ => throwError "ill-formed #introspect command"

/-- `#atlasmap` projects every declaration of the project and prints the map. -/
syntax (name := atlasmapCmd) "#atlasmap" : command

@[command_elab atlasmapCmd]
def elabAtlasmap : CommandElab := fun _ => do
  let panels ← projectProject
  let mut out := s!"[Introspective Atlas Map]  {panels.length} declarations\n"
  for p in panels do
    out := out ++ s!"  ({p.x},{p.y},{p.z}) [{styleName p.style}]  {p.name}\n"
  logInfo out

end Introspect

import Mathlib
import RequestProject.SVG
import Lean

/-!
# Cosmos: the whole-universe modular + functional view

The earlier atlas layers (`Introspect`, `IntrospectSVG`, `AtlasGuide`) project
*the project's own* declarations into the dual Monster-atlas.  This module zooms
all the way out: it ingests **every declaration in scope** — the entire
**Lean compiler** (`Lean.*`), the **Lean core / standard library** (`Init.*`,
`Std.*`, `Batteries.*`), and the **whole of Mathlib** (`Mathlib.*`) — parses the
dependency relation between them, and renders two complementary pictures:

* a **modular view** — the software universe grouped into *ecosystems*
  (Mathlib / Lean compiler / Init core / Std / Batteries / Other), each annotated
  with how many **modules** (source files) and **declarations** it contributes,
  plus the dominant **subsystems** inside Mathlib and inside the Lean compiler;

* a **functional view** — the actual *uses* relation, aggregated to the ecosystem
  level: a directed weighted graph whose edge `A → B` carries the number of times
  a declaration in ecosystem `A` references a declaration in ecosystem `B`.

Everything is computed natively by Lean from the live `Environment` (the same
`getUsedConstants` relation the kernel sees) and emitted as one self-contained
animated SVG.

Commands:

* `#cosmos`                 — scan the universe and print the modular + functional
  report (counts, subsystem breakdown, dependency matrix).
* `#writecosmos "path"`     — scan and write the SVG view to `path`.

Note: the scan touches well over a million declarations, so these commands take
appreciable time; they are meant to be run deliberately, not on every keystroke.
-/

open Lean Elab Command SVG

namespace Cosmos

/-! ## Ecosystem classification -/

/-- The fixed list of ecosystem labels (index = ecosystem code `0..5`). -/
def ecoLabels : Array String :=
  #["Mathlib", "Lean compiler", "Init (core)", "Std", "Batteries", "Other"]

/-- Number of ecosystems. -/
def nEco : Nat := ecoLabels.size

/-- Classify a *module name* into an ecosystem code `0..5`. -/
def ecoOfModule (mn : String) : Nat :=
  if mn.startsWith "Mathlib" then 0
  else if mn.startsWith "Lean" then 1
  else if mn.startsWith "Init" then 2
  else if mn.startsWith "Std" then 3
  else if mn.startsWith "Batteries" then 4
  else 5

/-- The second namespace component of a dotted name (`"Mathlib.Algebra.X" ↦
"Algebra"`), or `"·"` if there is none. -/
def subsystemOf (mn : String) : String :=
  match (mn.splitOn ".").drop 1 with
  | c :: _ => c
  | []     => "·"

/-! ## The scanned data -/

/-- Everything the cosmos scan collects in a single environment pass. -/
structure CosmosData where
  /-- number of declarations per ecosystem (index = ecosystem code). -/
  decls    : Array Nat
  /-- number of source modules per ecosystem. -/
  mods     : Array Nat
  /-- flattened `nEco × nEco` "uses" matrix, `m[src*nEco + dst]`. -/
  matrix   : Array Nat
  /-- top Mathlib subsystems `(name, declCount)`, descending. -/
  mathSubs : Array (String × Nat)
  /-- top Lean-compiler subsystems `(name, declCount)`, descending. -/
  leanSubs : Array (String × Nat)
  /-- grand totals. -/
  totDecls : Nat
  totMods  : Nat

/-- Bump the count for `key` in an association array (linear; the set of distinct
subsystem keys is small). -/
def bump (a : Array (String × Nat)) (key : String) : Array (String × Nat) :=
  match a.findIdx? (·.1 == key) with
  | some i => a.set! i (key, a[i]!.2 + 1)
  | none   => a.push (key, 1)

/-- Scan the whole environment and build the `CosmosData`. -/
def scan : CommandElabM CosmosData := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  -- ecosystem of a constant, via the module that defines it.
  let ecoOfConst : Name → Nat := fun n =>
    match env.const2ModIdx.get? n with
    | some i => ecoOfModule moduleNames[i.toNat]!.toString
    | none   => 5  -- not imported from any module ⇒ "Other"
  let subOfConst : Name → String := fun n =>
    match env.const2ModIdx.get? n with
    | some i => subsystemOf moduleNames[i.toNat]!.toString
    | none   => "·"
  -- module counts per ecosystem.
  let mut mods : Array Nat := Array.replicate nEco 0
  for mn in moduleNames do
    let e := ecoOfModule mn.toString
    mods := mods.set! e (mods[e]! + 1)
  -- declaration counts, subsystem breakdown, and the uses matrix in one pass.
  let mut decls : Array Nat := Array.replicate nEco 0
  let mut matrix : Array Nat := Array.replicate (nEco * nEco) 0
  let mut mathSubs : Array (String × Nat) := #[]
  let mut leanSubs : Array (String × Nat) := #[]
  for (name, info) in env.constants.toList do
    let src := ecoOfConst name
    decls := decls.set! src (decls[src]! + 1)
    if src == 0 then mathSubs := bump mathSubs (subOfConst name)
    else if src == 1 then leanSubs := bump leanSubs (subOfConst name)
    for c in info.getUsedConstantsAsSet.toList do
      let dst := ecoOfConst c
      let idx := src * nEco + dst
      matrix := matrix.set! idx (matrix[idx]! + 1)
  let sortDesc := fun (a : Array (String × Nat)) =>
    a.qsort (fun x y => x.2 > y.2)
  let totDecls := decls.foldl (· + ·) 0
  let totMods := mods.foldl (· + ·) 0
  return {
    decls, mods, matrix,
    mathSubs := sortDesc mathSubs,
    leanSubs := sortDesc leanSubs,
    totDecls, totMods }

/-! ## Text report -/

/-- First `n` characters of `s` (version-robust). -/
def abbr (s : String) (n : Nat := 5) : String := String.ofList (s.toList.take n)

/-- Render the modular + functional report as text. -/
def report (d : CosmosData) : String := Id.run do
  let mut s := s!"[Aristo Cosmos]  modular + functional view\n"
  s := s ++ s!"  universe: {d.totDecls} declarations across {d.totMods} modules\n\n"
  s := s ++ "  ── MODULAR VIEW (ecosystems) ──\n"
  for i in [0:nEco] do
    s := s ++ s!"    {ecoLabels[i]!}: {d.decls[i]!} decls / {d.mods[i]!} modules\n"
  s := s ++ "\n  Mathlib subsystems (top 10 by decls):\n"
  for (nm, c) in d.mathSubs.toList.take 10 do
    s := s ++ s!"    Mathlib.{nm}: {c}\n"
  s := s ++ "\n  Lean-compiler subsystems (top 10 by decls):\n"
  for (nm, c) in d.leanSubs.toList.take 10 do
    s := s ++ s!"    Lean.{nm}: {c}\n"
  s := s ++ "\n  ── FUNCTIONAL VIEW (uses matrix: row = user, col = used) ──\n"
  s := s ++ "    " ++ String.intercalate "  " (ecoLabels.toList.map (abbr ·)) ++ "\n"
  for i in [0:nEco] do
    let row := (List.range nEco).map (fun j => toString d.matrix[i*nEco+j]!)
    s := s ++ s!"    {abbr ecoLabels[i]!}: " ++ String.intercalate " " row ++ "\n"
  return s

/-! ## SVG view -/

/-- Per-ecosystem `(fill, glow)` palette. -/
def colorOf : Nat → String × String
  | 0 => ("#ffd700", "#fff2a8")  -- Mathlib    → gold
  | 1 => ("#8a2be2", "#d6b3ff")  -- Lean       → violet
  | 2 => ("#00c2c2", "#a8fbfb")  -- Init       → teal
  | 3 => ("#5db1ff", "#bfe0ff")  -- Std        → blue
  | 4 => ("#ff5db1", "#ffc4e3")  -- Batteries  → pink
  | _ => ("#8a93a6", "#d6dce8")  -- Other      → gray

/-- Fixed dependency-layout positions for the six ecosystem nodes (deps flow
downward toward the foundations). -/
def nodePos : Nat → Int × Int
  | 0 => (510, 250)   -- Mathlib (top, depends on all)
  | 1 => (820, 730)   -- Lean compiler
  | 2 => (510, 860)   -- Init core (foundation)
  | 3 => (210, 730)   -- Std
  | 4 => (210, 470)   -- Batteries
  | _ => (820, 470)   -- Other

/-- Number of decimal digits of `n` (a cheap log-scale). -/
def digits (n : Nat) : Nat := (toString n).length

/-- Node radius from its declaration count. -/
def nodeRadius (declCount : Nat) : Int := 16 + Int.ofNat (Nat.sqrt declCount) / 20

/-- `<defs>`: background gradient and an arrowhead marker. -/
def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"cbg\" cx=\"50%\" cy=\"28%\" r=\"95%\">" ++
    "<stop offset=\"0%\" stop-color=\"#161a34\"/><stop offset=\"100%\" stop-color=\"#060710\"/></radialGradient>" ++
  "<linearGradient id=\"cban\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#5db1ff\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#ff5db1\"/></linearGradient>" ++
  "<marker id=\"arrow\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">" ++
    "<path d=\"M0 0L10 5L0 10z\" fill=\"#aab4d8\"/></marker>" ++
  "</defs>"

/-- The comic banner. -/
def banner : Svg :=
  group
    [ rect 30 24 1620 92 "url(#cban)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","60"),("y","74"),("font-size","38"),("font-weight","800"),
                ("fill","#0b0c18"),("letter-spacing","2")]
        "ARISTO  ·  COSMOS  —  THE WHOLE UNIVERSE",
      Svg.text [("x","62"),("y","104"),("font-size","16"),("font-weight","600"),
                ("fill","#10142e")]
        "Mathlib + Lean compiler + Lean stdlib, parsed into one modular & functional dependency graph" ]

/-- A curved directed edge from ecosystem `src` to `dst`, weighted by `w`. -/
def edge (src dst w : Nat) : Svg :=
  let (x1, y1) := nodePos src
  let (x2, y2) := nodePos dst
  let mx := (x1 + x2) / 2
  let my := (y1 + y2) / 2 - 40  -- bow the curve upward a touch
  let sw := Int.ofNat (digits w)              -- 1..7 stroke width
  let (col, _) := colorOf src
  Svg.raw <|
    s!"<path d=\"M{x1} {y1} Q{mx} {my} {x2} {y2}\" fill=\"none\" stroke=\"{col}\" " ++
    s!"stroke-width=\"{sw}\" stroke-opacity=\"0.5\" marker-end=\"url(#arrow)\">" ++
    s!"<title>{ecoLabels[src]!} uses {ecoLabels[dst]!}: {w} references</title></path>"

/-- One ecosystem node disc with labels and a gentle breathing pulse. -/
def node (i : Nat) (d : CosmosData) : Svg :=
  let (cx, cy) := nodePos i
  let (fill, glow) := colorOf i
  let r := nodeRadius d.decls[i]!
  group
    [ circle cx cy (r + 4) "none" glow [("opacity","0.30")],
      circle cx cy r fill "#0b0c18" [("stroke-width","2"),
        ("style", "transform-box: fill-box; transform-origin: center;")],
      Svg.raw <|
        s!"<title>{ecoLabels[i]!}: {d.decls[i]!} decls / {d.mods[i]!} modules</title>",
      Svg.raw <|
        "<animate attributeName=\"r\" " ++
        s!"values=\"{r};{r+3};{r}\" dur=\"{4 + i}s\" repeatCount=\"indefinite\" " ++
        "additive=\"replace\"/>",
      Svg.text [("x", toString cx), ("y", toString (cy - r - 8)),
                ("font-size","16"),("font-weight","800"),("text-anchor","middle"),
                ("fill", glow)] (ecoLabels[i]!),
      Svg.text [("x", toString cx), ("y", toString (cy + r + 18)),
                ("font-size","12"),("text-anchor","middle"),("fill","#cfd8f5")]
        s!"{d.decls[i]!} decls · {d.mods[i]!} mods" ]
    []

/-- A horizontal bar-chart panel of `entries` titled `title`, anchored at
`(x, y)` with width `w`. -/
def barPanel (x y w : Int) (title : String) (entries : List (String × Nat))
    (col : String) : Svg :=
  let h : Int := 56 + Int.ofNat entries.length * 26
  let maxC := (entries.map (·.2)).foldl Nat.max 1
  let bars := entries.zipIdx.map (fun ((nm, c), j) =>
    let by_ := y + 48 + Int.ofNat j * 26
    let bw := (Int.ofNat c) * (w - 200) / (Int.ofNat maxC)
    group
      [ Svg.text [("x", toString (x + 14)), ("y", toString (by_ + 13)),
                  ("font-size","12"),("fill","#cfd8f5")] nm,
        rect (x + 150) by_ (max (2:Int) bw) 16 col "#0b0c18" [("rx","3")],
        Svg.text [("x", toString (x + 158 + max (2:Int) bw)), ("y", toString (by_ + 13)),
                  ("font-size","11"),("fill","#9fb0e0")] (toString c) ]
      [])
  group
    ([ rect x y w h "#0c0f22" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x", toString (x + 16)), ("y", toString (y + 28)),
                 ("font-size","17"),("font-weight","800"),("fill","#ffd700")] title ]
      ++ bars)

/-- Legend / summary footer line. -/
def footer (d : CosmosData) : Svg :=
  Svg.text [("x","40"),("y","1034"),("font-size","12"),("fill","#7a86b8")]
    s!"{d.totDecls} declarations · {d.totMods} modules · uses-relation from Lean's live Environment · generated natively · #writecosmos"

/-- Assemble the whole cosmos SVG document. -/
def buildSvg (d : CosmosData) : String :=
  -- functional edges: every nonzero off-diagonal entry of the uses matrix.
  let edges : List Svg := Id.run do
    let mut es : List Svg := []
    for i in [0:nEco] do
      for j in [0:nEco] do
        if i ≠ j then
          let w := d.matrix[i*nEco+j]!
          if w > 0 then es := edge i j w :: es
    return es
  let nodes : List Svg := (List.range nEco).map (fun i => node i d)
  let graphFrame :=
    group
      [ rect 40 150 960 760 "#0a0d20" "#3a4a8a" [("rx","12"),("stroke-width","2")],
        Svg.text [("x","60"),("y","182"),("font-size","18"),("font-weight","800"),
                  ("fill","#ffd700")] "FUNCTIONAL VIEW — ecosystem uses-graph",
        Svg.text [("x","60"),("y","204"),("font-size","12"),("fill","#9fb0e0")]
          "arrow A→B: a decl in A references a decl in B · width ∝ digits of weight · hover for counts" ]
  let modularHeader :=
    Svg.text [("x","1020"),("y","150"),("font-size","18"),("font-weight","800"),
              ("fill","#ffd700")] "MODULAR VIEW — subsystem breakdown"
  let mathPanel :=
    barPanel 1020 168 620 "Mathlib subsystems (top decls)"
      (d.mathSubs.toList.take 12) "#ffd700"
  let leanPanel :=
    barPanel 1020 600 620 "Lean-compiler subsystems (top decls)"
      (d.leanSubs.toList.take 10) "#8a2be2"
  let doc := document 1680 1040
    ([ Svg.raw defsRaw,
       rect 0 0 1680 1040 "url(#cbg)" "none" [],
       banner,
       graphFrame ]
      ++ edges ++ nodes ++
     [ modularHeader, mathPanel, leanPanel, footer d ])
  render doc

/-! ## Commands -/

/-- `#cosmos` scans the whole universe and prints the modular + functional
report. -/
syntax (name := cosmosCmd) "#cosmos" : command

@[command_elab cosmosCmd]
def elabCosmos : CommandElab := fun _ => do
  let d ← scan
  logInfo (report d)

/-- `#writecosmos "path"` scans the universe and writes the SVG view to `path`. -/
syntax (name := writecosmosCmd) "#writecosmos " str : command

@[command_elab writecosmosCmd]
def elabWritecosmos : CommandElab := fun stx => do
  match stx with
  | `(#writecosmos $p:str) => do
    let path := p.getString
    let d ← scan
    let svg := buildSvg d
    IO.FS.writeFile path svg
    logInfo (report d)
    logInfo s!"[Aristo Cosmos] wrote {svg.length} bytes to {path} ({d.totDecls} decls / {d.totMods} modules)."
  | _ => throwError "ill-formed #writecosmos command"

/-! ## Generation (run at build time) -/

-- Parse the whole universe (Mathlib + Lean compiler + Lean stdlib) and emit the
-- modular + functional view.  This scan touches well over a million
-- declarations, so it is the slow step of the build.
#writecosmos "atlas_cosmos.svg"

end Cosmos

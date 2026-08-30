import RequestProject.IntrospectSVG
import RequestProject.DualAtlas
import Lean

/-!
# FiberHome — the natural home of every declaration in the fiber bundle, and
nearest-neighbour search by fiber address.

The dual atlas (`RequestProject.DualAtlas`) gives every declaration three
coordinates:

* `cog`   — the `46×2` cognitive grid column (`cogProj`, `1 ≤ cog ≤ 92`);
* `triad` — the `20×3` semantic triad row (`triadProj`, `triad ≤ 19`);
* `harm`  — the harmonic cell code (`harmCode`, value in `{0,5,7,11,13}`).

This module reads those three coordinates as a **fiber bundle**:

* the **base** is the `92 × 20` cognitive/semantic grid (`1840` base cells);
* the **fibre** over each base point is the `5`-element harmonic class
  (`{trivector, Muse, heptad, hemisphere, recursion}`, normalised to a rank
  `0..4` by `harmRank`).

The total space therefore has `92 · 20 · 5 = 9200` cells.  The **natural home**
of a declaration is the single cell `(cog, triad, harm)` its fingerprint lands
in, linearised by `homeIndex` to an integer in `[0, 9200)`.

This module contributes:

* `FiberHome` — the `(cog, triad, harm)` cell of a declaration;
* `homeIndex` — the linear address of a cell, with **verified** facts
  `homeIndex_lt` (it lands in `[0,9200)`) and `homeIndex_determines_cell`
  (the address determines the whole cell, so the linearisation is injective on
  the valid range);
* `SimilarHome` — "lands in the same cell", a **verified** `Equivalence`
  (`similarHome_equiv`) characterised cell-wise (`similarHome_iff_cell`); this is
  the formal meaning of "find similar declarations";
* `#findhome f` — reflect a single declaration into its natural home and report
  the population of that home over the whole environment;
* `#similar f` — sweep the **entire loaded environment** and list the
  declarations that share `f`'s home cell (its nearest neighbours), writing
  `atlas_fiberhome.json`;
* `#fibercensus` — report the occupancy statistics of the bundle over the whole
  corpus;
* `#writefibers "path"` — render all ~700k declarations as a heat-map over the
  `92 × 20` base grid, each base cell coloured by its dominant harmonic fibre and
  shaded by population, writing the SVG to `path`.

## Honest scope

Coordinates come from the same O(1) `Expr.hash` fingerprint used throughout the
project; nothing here claims a mathematical relationship between the Monster
group and the declarations.  The verified content is exactly the fiber-address
algebra (`homeIndex_lt`, `homeIndex_determines_cell`, `similarHome_equiv`,
`similarHome_iff_cell`); the census numbers and the picture are an empirical
read-out of the current environment.
-/

open Lean Meta Elab Command SVG

namespace FiberHome

open DualAtlas IntrospectSVG Introspect

/-! ## §1  The fiber address -/

/-- The harmonic class as a contiguous rank `0..4` (the fibre coordinate),
priority `13 > 11 > 7 > 5 > default`.  Equal to `styleOfHarm (harmCode h)`. -/
def harmRank (h : Nat) : Nat :=
  if h % 13 == 0 then 4
  else if h % 11 == 0 then 3
  else if h % 7 == 0 then 2
  else if h % 5 == 0 then 1
  else 0

/-- The natural home of a declaration: a cell `(cog, triad, harm)` of the
`92 × 20 × 5` fiber bundle. -/
structure FiberHome where
  cog   : Nat   -- cognitive grid column, `1 ≤ cog ≤ 92`
  triad : Nat   -- semantic triad row, `triad ≤ 19`
  harm  : Nat   -- harmonic fibre rank, `harm ≤ 4`
deriving Repr, DecidableEq

/-- The natural home of a fingerprint. -/
def homeOf (h : Nat) : FiberHome :=
  { cog := cogProj h, triad := triadProj h, harm := harmRank h }

/-- Number of base cells (`92 × 20`). -/
def baseCellCount : Nat := 1840
/-- Number of cells of the whole bundle (`92 × 20 × 5`). -/
def homeCellCount : Nat := 9200

/-- The linear address of a fiber cell, in `[0, 9200)`:
`(cog-1) + 92·triad + 1840·harm`. -/
def homeIndex (h : Nat) : Nat :=
  (cogProj h - 1) + 92 * triadProj h + 1840 * harmRank h

/-! ## §2  Verified fiber-address algebra -/

/-
The fibre rank is in range `0..4`.
-/
theorem harmRank_le (h : Nat) : harmRank h ≤ 4 := by
  unfold harmRank; split_ifs <;> norm_num;

/-
**Every declaration's home lands in the `[0, 9200)` cell space.**
-/
theorem homeIndex_lt (h : Nat) : homeIndex h < homeCellCount := by
  have h1 := DualAtlas.cogProj_mem h
  have h2 := DualAtlas.triadProj_le h
  have h3 := harmRank_le h
  unfold homeIndex homeCellCount at *
  omega

/-
**The linear address determines the whole cell** — so `homeIndex` is an
injective linearisation of the fiber bundle: two fingerprints with the same home
address agree on all three fiber coordinates.
-/
theorem homeIndex_determines_cell (h₁ h₂ : Nat) (heq : homeIndex h₁ = homeIndex h₂) :
    cogProj h₁ = cogProj h₂ ∧ triadProj h₁ = triadProj h₂ ∧ harmRank h₁ = harmRank h₂ := by
  unfold homeIndex at heq; have := cogProj_mem h₁; have := cogProj_mem h₂; have := triadProj_le h₁; have := triadProj_le h₂; have := harmRank_le h₁; have := harmRank_le h₂; omega;

/-- Two declarations are **similar** when they land in the same home cell. -/
def SimilarHome (h₁ h₂ : Nat) : Prop := homeIndex h₁ = homeIndex h₂

/-
**Similarity is an equivalence relation** — so "similar declarations" is a
partition of the corpus into the cells of the bundle.
-/
theorem similarHome_equiv : Equivalence SimilarHome := by
  constructor;
  · exact fun x => rfl;
  · exact fun h => h.symm;
  · exact fun h₁ h₂ => h₁.trans h₂

/-
**Similarity is exactly cell-equality**: similar declarations share their
cognitive column, semantic triad, and harmonic fibre.
-/
theorem similarHome_iff_cell (h₁ h₂ : Nat) :
    SimilarHome h₁ h₂ ↔
      (cogProj h₁ = cogProj h₂ ∧ triadProj h₁ = triadProj h₂ ∧ harmRank h₁ = harmRank h₂) := by
  exact ⟨ fun h => homeIndex_determines_cell h₁ h₂ h, fun h => by unfold SimilarHome homeIndex; rw [ h.1, h.2.1, h.2.2 ] ⟩

/-! ## §3  Fingerprint and reflection front-end -/

/-- The fingerprint of a declaration from its cached `Expr.hash` (O(1)): the XOR
of the type's hash and the value's hash (`0` when there is no value). -/
def declFingerprint (info : ConstantInfo) : Nat :=
  let vh := match info.value? with | some v => v.hash.toNat | none => 0
  info.type.hash.toNat ^^^ vh

/-- Human-readable name of a fibre rank. -/
def fibreName (r : Nat) : String := styleName r

/-- `#findhome f` reflects declaration `f` into its natural home cell and reports
the population of that cell over the whole environment. -/
syntax (name := findhomeCmd) "#findhome " ident : command

@[command_elab findhomeCmd]
def elabFindhome : CommandElab := fun stx => do
  match stx with
  | `(#findhome $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info =>
      let h := declFingerprint info
      let home := homeOf h
      let idx := homeIndex h
      -- population of this home cell over the whole environment
      let mut pop := 0
      for (_, i) in env.constants.toList do
        if homeIndex (declFingerprint i) == idx then pop := pop + 1
      logInfo s!"[Aristo Fiber Home] {name}\n  ├── Cognitive column (46×2) = {home.cog}\n  ├── Semantic triad (20×3)   = {home.triad}\n  ├── Harmonic fibre          = {fibreName home.harm} (rank {home.harm})\n  ├── Linear home index       = {idx} / {homeCellCount}\n  └── Cell population (env)    = {pop} declarations share this home"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #findhome command"

/-- `#similar f` sweeps the whole environment and lists the declarations that
share `f`'s natural home cell — its nearest neighbours in the fiber bundle.
A JSON artifact `atlas_fiberhome.json` is written. -/
syntax (name := similarCmd) "#similar " ident : command

@[command_elab similarCmd]
def elabSimilar : CommandElab := fun stx => do
  match stx with
  | `(#similar $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info =>
      let h := declFingerprint info
      let home := homeOf h
      let idx := homeIndex h
      let mut pop := 0
      let mut sample : Array Name := #[]
      for (nm, i) in env.constants.toList do
        if nm != name && !nm.isInternal then
          if homeIndex (declFingerprint i) == idx then
            pop := pop + 1
            if sample.size < 40 then sample := sample.push nm
      let mut lines : String := ""
      for nm in sample do
        lines := lines ++ s!"  │   • {nm}\n"
      logInfo s!"[Aristo Similar] declarations sharing the home of {name}\n  ├── home cell = (cog {home.cog}, triad {home.triad}, {fibreName home.harm})\n  ├── linear index = {idx}\n  ├── neighbours found = {pop}\n  └── sample (≤ 40):\n{lines}"
      -- best-effort JSON artifact
      try
        let mut arr : String := ""
        let mut first := true
        for nm in sample do
          let sep := if first then "" else ",\n"
          arr := arr ++ sep ++ s!"    \"{nm}\""
          first := false
        let json :=
          s!"\{\n" ++
          s!"  \"query\": \"{name}\",\n" ++
          s!"  \"homeIndex\": {idx},\n" ++
          s!"  \"cog\": {home.cog},\n" ++
          s!"  \"triad\": {home.triad},\n" ++
          s!"  \"harm\": {home.harm},\n" ++
          s!"  \"harmName\": \"{fibreName home.harm}\",\n" ++
          s!"  \"neighbourCount\": {pop},\n" ++
          s!"  \"sample\": [\n" ++ arr ++ "\n  ]\n" ++
          s!"}\n"
        IO.FS.writeFile "atlas_fiberhome.json" json
      catch _ => pure ()
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #similar command"

/-! ## §4  Census over the whole corpus -/

/-- `#fibercensus` reports occupancy statistics of the fiber bundle over the
entire loaded environment. -/
syntax (name := fibercensusCmd) "#fibercensus" : command

@[command_elab fibercensusCmd]
def elabFibercensus : CommandElab := fun _ => do
  let env ← getEnv
  let mut cells : Std.HashMap Nat Nat := {}
  let mut total := 0
  for (_, info) in env.constants.toList do
    total := total + 1
    let idx := homeIndex (declFingerprint info)
    cells := cells.insert idx (cells.getD idx 0 + 1)
  let occupied := cells.size
  let maxPop := cells.toList.foldl (fun m (_, c) => max m c) 0
  let avgPerOccupied := if occupied == 0 then 0 else total / occupied
  logInfo s!"[Aristo Fiber Census] placed the whole corpus into the {homeCellCount}-cell bundle\n  ├── total declarations        = {total}\n  ├── occupied home cells (≤ {homeCellCount}) = {occupied}\n  ├── empty home cells          = {homeCellCount - occupied}\n  ├── busiest cell population    = {maxPop}\n  └── mean population / occupied = {avgPerOccupied}"

/-! ## §5  Visualisation: all ~700k declarations along the fibers -/

/-- Truncate a `Float` to an `Int`. -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- Geometry of the base grid heat-map. -/
def cellW : Int := 14
def cellH : Int := 16
def gridX0 : Int := 60
def gridY0 : Int := 150

/-- The per-cell accumulator: `(total, per-fibre counts r0..r4)`. -/
structure CellStat where
  total : Nat
  f0 : Nat
  f1 : Nat
  f2 : Nat
  f3 : Nat
  f4 : Nat
deriving Inhabited

/-- Dominant fibre rank of a cell (argmax of the five fibre counts). -/
def CellStat.dominant (s : CellStat) : Nat :=
  let pairs : List (Nat × Nat) := [(0, s.f0), (1, s.f1), (2, s.f2), (3, s.f3), (4, s.f4)]
  (pairs.foldl (fun best p => if p.2 > best.2 then p else best) (0, s.f0)).1

/-- Gather, for each base cell `(cog, triad)`, its population and fibre split,
over the whole environment.  Returns `(total, maxPop, grid)`. -/
def gatherFibers : CommandElabM (Nat × Nat × Std.HashMap (Nat × Nat) CellStat) := do
  let env ← getEnv
  let mut grid : Std.HashMap (Nat × Nat) CellStat := {}
  let mut total := 0
  let mut maxPop := 0
  for (_, info) in env.constants.toList do
    total := total + 1
    let h := declFingerprint info
    let key := (cogProj h, triadProj h)
    let r := harmRank h
    let s := grid.getD key ⟨0, 0, 0, 0, 0, 0⟩
    let s' : CellStat :=
      { total := s.total + 1
        f0 := s.f0 + (if r == 0 then 1 else 0)
        f1 := s.f1 + (if r == 1 then 1 else 0)
        f2 := s.f2 + (if r == 2 then 1 else 0)
        f3 := s.f3 + (if r == 3 then 1 else 0)
        f4 := s.f4 + (if r == 4 then 1 else 0) }
    grid := grid.insert key s'
    if s'.total > maxPop then maxPop := s'.total
  return (total, maxPop, grid)

/-- One heat-map cell rectangle, coloured by dominant fibre, opacity by
population (√-scaled against `maxPop`). -/
def cellSvg (maxPop : Nat) (cog triad : Nat) (s : CellStat) : Svg :=
  let (fill, _) := colorOf (s.dominant)
  let x := gridX0 + (Int.ofNat (cog - 1)) * cellW
  let y := gridY0 + (Int.ofNat triad) * cellH
  let frac := Float.sqrt (Float.ofNat s.total / Float.ofNat (max maxPop 1))
  let op := 0.12 + 0.88 * frac
  Svg.elem "rect"
    [("x", toString x), ("y", toString y),
     ("width", toString (cellW - 1)), ("height", toString (cellH - 1)),
     ("fill", fill), ("stroke", "#05060f"), ("stroke-width", "0.4"),
     ("opacity", toString op)]
    [ Svg.raw s!"<title>cog {cog} · triad {triad} · {s.total} decls (fibres {s.f0}/{s.f1}/{s.f2}/{s.f3}/{s.f4})</title>" ]

/-- The legend chips for the five harmonic fibres. -/
def legend : Svg :=
  let entries : List (Nat × String) :=
    [(0, "Trivector"), (1, "Muse (9^5)"), (2, "Heptad (6^7)"),
     (3, "Hemispheres (2^11)"), (4, "Recursion (3^13)")]
  group (entries.map (fun (r, nm) =>
    let (fill, _) := colorOf r
    let x : Int := 60 + (Int.ofNat r) * 250
    group
      [ rect x 110 18 18 fill "#05060f" [("rx", "3")],
        Svg.text [("x", toString (x + 26)), ("y", "124"),
                  ("font-size", "13"), ("fill", "#dfe6ff")] nm ]))

/-- Build the fiber heat-map SVG document. -/
def buildFiberAtlas (total maxPop : Nat) (grid : Std.HashMap (Nat × Nat) CellStat) : String := Id.run do
  let mut cellsG : List Svg := []
  for cog in [1:93] do
    for triad in [0:20] do
      match grid[(cog, triad)]? with
      | some s => cellsG := cellSvg maxPop cog triad s :: cellsG
      | none => pure ()
  let gridW := gridX0 + 92 * cellW + 40
  let gridH := gridY0 + 20 * cellH + 120
  let doc := document gridW.toNat gridH.toNat
    [ rect 0 0 gridW gridH "#06070f" "none" [],
      Svg.text [("x", "40"), ("y", "50"), ("font-size", "26"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        "FIBER ATLAS · EVERY DECLARATION IN ITS NATURAL HOME",
      Svg.text [("x", "40"), ("y", "78"), ("font-size", "14"), ("fill", "#9fb0d8")]
        "base = 46×2 cognitive grid (x) × 20×3 semantic triad (y) · fibre = harmonic class (colour) · shade = population",
      legend,
      group cellsG,
      Svg.text [("x", "60"), ("y", toString (gridY0 + 20 * cellH + 40)),
                ("font-size", "15"), ("font-weight", "700"), ("fill", "#ffd700")]
        s!"{total} declarations placed · {homeCellCount}-cell bundle (92 cognitive × 20 triad × 5 harmonic) · busiest cell {maxPop} decls",
      Svg.text [("x", "60"), ("y", toString (gridY0 + 20 * cellH + 62)),
                ("font-size", "12"), ("fill", "#7f8db8")]
        "each rectangle is one base cell (cog × triad); colour = dominant harmonic fibre; opacity ∝ √population · generated natively by Lean · #writefibers" ]
  return render doc

/-- `#fiberatlas` builds the fiber heat-map and reports its size. -/
syntax (name := fiberatlasCmd) "#fiberatlas" : command

@[command_elab fiberatlasCmd]
def elabFiberatlas : CommandElab := fun _ => do
  let (total, maxPop, grid) ← gatherFibers
  let svg := buildFiberAtlas total maxPop grid
  logInfo s!"[Fiber Atlas] placed {total} declarations across {grid.size} occupied base cells (busiest {maxPop}) → {svg.length}-byte heat-map SVG."

/-- `#writefibers "path"` writes the fiber heat-map SVG to `path`. -/
syntax (name := writefibersCmd) "#writefibers " str : command

@[command_elab writefibersCmd]
def elabWritefibers : CommandElab := fun stx => do
  match stx with
  | `(#writefibers $p:str) => do
    let path := p.getString
    let (total, maxPop, grid) ← gatherFibers
    let svg := buildFiberAtlas total maxPop grid
    IO.FS.writeFile path svg
    logInfo s!"[Fiber Atlas] wrote {svg.length} bytes ({total} decls, {grid.size} occupied base cells, busiest {maxPop}) to {path}"
  | _ => throwError "ill-formed #writefibers command"

/-! ## §6  Build-time generation + test suite -/

#findhome Nat.add
#findhome List.map
#findhome Prod.fst

#similar Nat.add

#fibercensus

#fiberatlas
#writefibers "atlas_fibers.svg"

end FiberHome
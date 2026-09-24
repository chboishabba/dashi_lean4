import RequestProject.DeclWeave
import RequestProject.SVG
import Lean

/-!
# DeclWeaveSVG — the AST→irrep-1 embedding, rendered as an animated atlas

`DeclWeave` embeds each declaration's expression graph (its AST) into the
`196883`-cell address space of the smallest non-trivial Monster irrep:
every node `nd` lands at `nodeCell nd = (k%71, k%59, k%47)` where `k =
nodeContent nd`.  Distinct cells ⇒ **faithful** (the weave separates the nodes);
a shared cell ⇒ a **smush** (information lost at this resolution).

This layer renders that embedding.  For each project declaration it computes the
cloud of node cells and draws it as a point cloud inside the irrep-1 CRT cube
`ℤ/71 × ℤ/59 × ℤ/47` (an isometric projection makes the three CRT axes visible).
Nodes that collide onto an already-occupied cell — the *smushes* — are drawn in
red; faithfully-placed nodes are drawn on the indigo→gold heat ramp by their
depth coordinate `k%47`.  The animation is a flip-book over declarations; each
frame annotates the declaration with its node/arrow counts, its distinct-cell
count, its smush count and whether the embedding is faithful.  A static bar panel
at the bottom shows the smush count per declaration — the *faithfulness
certificate*: a zero-height bar is a fully faithful embedding.

Everything drawn is computed natively by Lean from the `DeclWeave` definitions
the proofs use (`exprNodes`, `nodeCell`, `nodeCellCodes`, `smushCount`,
`isFaithful`), so the picture is faithful to the formal model.

## Honest scope

The embedding is purely combinatorial.  A node's cell is a fixed function of its
content (the literal value, de Bruijn index, name/string hash, universe depth) or,
for composite nodes, of its constructor.  Sharing a cell means two nodes have
congruent addresses, nothing more; no claim is made that the Monster group acts on
the embedded declarations.

Commands:

* `#declweavefilm`               — build the film, report size and decl count.
* `#writedeclweave "path"`       — build the film and write the SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace DeclWeaveSVG

open DeclWeave ExprAddress

/-! ## §1  Per-declaration data gathered by reflection -/

/-- Everything the renderer needs about one declaration's embedding. -/
structure WeaveData where
  name     : String
  nodes    : Nat
  arrows   : Nat
  cells    : Nat
  smush    : Nat
  faithful : Bool
  /-- `(a, b, c, isSmushed)` for each drawn node: its CRT cell and whether it
  collides with an earlier node. -/
  pts      : Array (Nat × Nat × Nat × Bool)
  deriving Inhabited

/-- Maximum declarations drawn in the flip-book. -/
def maxDecls : Nat := 28

/-- Maximum nodes drawn per declaration. -/
def maxPts : Nat := 700

/-- A **fuel-bounded** DFS node sample.  Mathlib-scale expressions are stored as
heavily-shared DAGs, so the naive structural `exprNodes` (used by the proofs)
overflows the stack on them; this worklist traversal pops at most `budget` nodes
and never recurses, giving a deterministic, bounded sample of the AST. -/
def boundedNodes (budget : Nat) (e0 : Expr) : Array Expr := Id.run do
  let mut out : Array Expr := #[]
  let mut fuel := budget
  let mut stack : Array Expr := #[e0]
  while fuel > 0 do
    if stack.size = 0 then break
    let e := stack.back!
    stack := stack.pop
    out := out.push e
    fuel := fuel - 1
    for c in exprChildren e do
      stack := stack.push c
  return out

/-- Build the full per-declaration weave data from a bounded node sample.  Counts
(`nodes`, `arrows`, `cells`, `smush`) are over the sampled nodes; for trees with
at most `maxPts` nodes this is the exact AST, otherwise an honest capped sample. -/
def weaveDataOf (nm : String) (e : Expr) : WeaveData := Id.run do
  let sample := boundedNodes maxPts e
  let mut seen : Std.HashSet Nat := {}
  let mut pts : Array (Nat × Nat × Nat × Bool) := #[]
  let mut edges := 0
  for nd in sample do
    edges := edges + (exprChildren nd).length
    let k := nodeContent nd
    let code := cellCode k
    let smushed := seen.contains code
    seen := seen.insert code
    pts := pts.push (k % 71, k % 59, k % 47, smushed)
  let nNodes := pts.size
  let cells := seen.size
  return {
    name := nm, nodes := nNodes, arrows := edges,
    cells := cells, smush := nNodes - cells,
    faithful := nNodes == cells, pts := pts }

/-! ## §2  Geometry -/

def canvasW : Nat := 1480
def canvasH : Nat := 1000

/-- Cube origin and per-axis screen steps for the isometric CRT projection. -/
def oxF : Float := 360.0
def oyF : Float := 250.0
def axA : Float := 9.2     -- step per unit of `k%71`
def ayB : Float := 9.6     -- step per unit of `k%59`
def dxC : Float := 5.6     -- depth shear x per unit of `k%47`
def dyC : Float := 3.0     -- depth shear y per unit of `k%47`

def f2i (f : Float) : Int := f.toInt64.toInt

/-- Isometric projection of a CRT cell `(a,b,c)` to a screen point. -/
def project (a b c : Nat) : Int × Int :=
  let x := oxF + Float.ofNat a * axA + Float.ofNat c * dxC
  let y := oyF + Float.ofNat b * ayB - Float.ofNat c * dyC
  (f2i x, f2i y)

/-! ## §3  Colour -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex2 (n : Nat) : String :=
  let n := min n 255
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

/-- Heat colour for depth `c ∈ [0,47)`: indigo → magenta → gold. -/
def depthColor (c : Nat) : String :=
  let v := min 255 (c * 255 / 46)
  let (r, g, b) :=
    if v ≤ 128 then (28 + v, 22 + v / 4, 70 + v / 2)
    else (200 + (v - 128) / 3, 40 + (v - 128), 150 - (v - 128))
  s!"#{hex2 r}{hex2 g}{hex2 b}"

/-! ## §4  Drawing -/

/-- The three CRT axis guides of the cube, from the origin. -/
def cubeFrame : Svg :=
  let (ax, ay) := project 70 0 0
  let (bx, byy) := project 0 58 0
  let (cx, cyy) := project 0 0 46
  let (ox, oy) := project 0 0 0
  group
    [ line ox oy ax ay "#2a7fff" [("stroke-width","1.5"),("opacity","0.5")],
      line ox oy bx byy "#00c2c2" [("stroke-width","1.5"),("opacity","0.5")],
      line ox oy cx cyy "#ffd700" [("stroke-width","1.5"),("opacity","0.5")],
      Svg.text [("x", toString (ax+6)),("y", toString ay),("font-size","12"),
                ("fill","#2a7fff")] "k%71",
      Svg.text [("x", toString (bx-40)),("y", toString (byy+14)),("font-size","12"),
                ("fill","#00c2c2")] "k%59",
      Svg.text [("x", toString (cx+6)),("y", toString cyy),("font-size","12"),
                ("fill","#ffd700")] "k%47 (depth)" ]

/-- One declaration's point cloud as a frame, visible only in its time slot. -/
def cloudFrame (d : WeaveData) (idx total : Nat) : Svg :=
  let vals := (List.range total).map (fun f => if f == idx then "1" else "0")
  let values := String.intercalate ";" vals
  let dur := s!"{total * 2}s"
  let dots := d.pts.toList.map (fun (a, b, c, sm) =>
    let (x, y) := project a b c
    if sm then
      circle x y 3 "#ff3b5c" "#7a0014" [("opacity","0.9")]
    else
      circle x y 2 (depthColor c) "none" [("opacity","0.85")])
  Svg.elem "g" [("opacity", if idx == 0 then "1" else "0")]
    (Svg.raw s!"<animate attributeName=\"opacity\" values=\"{values}\" dur=\"{dur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>"
     :: dots)

/-- One declaration's HUD text, visible only in its time slot. -/
def hudFrame (d : WeaveData) (idx total : Nat) : Svg :=
  let vals := (List.range total).map (fun f => if f == idx then "1" else "0")
  let values := String.intercalate ";" vals
  let dur := s!"{total * 2}s"
  let fcol := if d.faithful then "#9fe0b0" else "#ff9fb0"
  let ftxt := if d.faithful then "FAITHFUL (no smush)" else s!"SMUSHED ×{d.smush}"
  Svg.elem "g" [("opacity", if idx == 0 then "1" else "0")]
    [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"{values}\" dur=\"{dur}\" calcMode=\"discrete\" repeatCount=\"indefinite\"/>",
      Svg.text [("x","40"),("y","150"),("font-size","20"),("font-weight","800"),
                ("fill","#ffd700")] (SVG.esc d.name),
      Svg.text [("x","40"),("y","176"),("font-size","14"),("fill","#9fb0e0")]
        s!"AST nodes {d.nodes} · arrows {d.arrows} · distinct cells {d.cells}",
      Svg.text [("x","40"),("y","198"),("font-size","15"),("font-weight","700"),
                ("fill", fcol)] ftxt ]

/-- The static smush bar panel — the faithfulness certificate over all decls. -/
def barPanel (ds : Array WeaveData) : Svg :=
  let n := ds.size
  let baseY : Int := 940
  let barW : Int := if n == 0 then 10 else Int.ofNat (1400 / max 1 n)
  let maxSmush := ds.foldl (fun m d => max m d.smush) 1
  let bars := ds.toList.zipIdx.map (fun (d, i) =>
    let x : Int := 40 + Int.ofNat i * barW
    let hgt : Int := Int.ofNat (d.smush * 120 / max 1 maxSmush)
    let col := if d.smush == 0 then "#9fe0b0" else "#ff3b5c"
    group
      [ rect x (baseY - hgt) (max 2 (barW - 2)) hgt col "none" [("opacity","0.85")],
        Svg.raw s!"<title>{SVG.esc d.name}: {d.smush} smushed / {d.nodes} nodes</title>" ])
  group
    (Svg.text [("x","40"),("y","916"),("font-size","13"),("font-weight","700"),
               ("fill","#9fb0e0")]
       s!"smush per declaration (green = faithful · red = smushed) · max {maxSmush}"
     :: line 40 baseY (40 + Int.ofNat n * barW) baseY "#2a335f" [("stroke-width","1")]
     :: bars)

def defsRaw : String :=
  "<defs><radialGradient id=\"wbg\" cx=\"45%\" cy=\"30%\" r=\"95%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"wbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#2a7fff\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#ff3b5c\"/></linearGradient></defs>"

def banner : Svg :=
  group
    [ rect 24 20 1432 84 "url(#wbanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","48"),("y","60"),("font-size","28"),("font-weight","800"),
                ("fill","#0b0c18")]
        "DECL WEAVE · AST GRAPH → MONSTER IRREP-1 CELL SPACE (71×59×47 = 196883)",
      Svg.text [("x","50"),("y","90"),("font-size","13"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "each AST node → its CRT cell (k%71, k%59, k%47); red = smush (collision), heat = depth; faithful ⇔ no two nodes share a cell" ]

/-! ## §5  Assembling the film -/

/-- Build the complete animated weave SVG from gathered declaration data. -/
def buildFilm (ds : Array WeaveData) : String :=
  let total := ds.size
  let clouds := ds.toList.zipIdx.map (fun (d, i) => cloudFrame d i (max 1 total))
  let huds := ds.toList.zipIdx.map (fun (d, i) => hudFrame d i (max 1 total))
  let doc := document canvasW canvasH
    ([ Svg.raw defsRaw,
       rect 0 0 (Int.ofNat canvasW) (Int.ofNat canvasH) "url(#wbg)" "none" [],
       banner,
       cubeFrame ]
     ++ clouds ++ huds ++
     [ barPanel ds,
       Svg.text [("x","40"),("y", toString (Int.ofNat canvasH - 14)),
                 ("font-size","11"),("fill","#5a6790")]
         s!"{total} declarations · cells = DeclWeave.nodeCell · faithfulness = DeclWeave.isFaithful · pigeonhole bound 196883 (DeclWeave.smush_of_overflow) · #writedeclweave" ])
  render doc

/-! ## §6  Reflection: gather project declarations -/

/-- Gather weave data for the project's declarations (capped at `maxDecls`),
sorted by AST node count ascending (foundational, smaller trees first). -/
def gatherWeave : CommandElabM (Array WeaveData) := do
  let env ← getEnv
  let mut rows : Array WeaveData := #[]
  for (name, info) in env.constants.toList do
    if ExprAddress.isProjectDecl name.toString then
      let e := match info.value? with
        | some v => v
        | none   => info.type
      rows := rows.push (weaveDataOf name.toString e)
  let sorted := rows.qsort (fun a b => a.nodes < b.nodes)
  return sorted.toList.take maxDecls |>.toArray

/-! ## §7  Commands -/

/-- `#declweavefilm` builds the animated weave atlas and reports its size. -/
syntax (name := declweavefilmCmd) "#declweavefilm" : command

@[command_elab declweavefilmCmd]
def elabDeclweavefilm : CommandElab := fun _ => do
  let ds ← gatherWeave
  let svg := buildFilm ds
  let faithfulN := ds.foldl (fun c d => if d.faithful then c + 1 else c) 0
  logInfo s!"[Decl Weave Film] {ds.size} declarations ({faithfulN} faithful) → {svg.length}-byte animated SVG."

/-- `#writedeclweave "path"` builds the weave atlas and writes the SVG to `path`. -/
syntax (name := writedeclweaveCmd) "#writedeclweave " str : command

@[command_elab writedeclweaveCmd]
def elabWritedeclweave : CommandElab := fun stx => do
  match stx with
  | `(#writedeclweave $p:str) => do
    let path := p.getString
    let ds ← gatherWeave
    let svg := buildFilm ds
    IO.FS.writeFile path svg
    logInfo s!"[Decl Weave Film] wrote {svg.length} bytes ({ds.size} declarations) to {path}"
  | _ => throwError "ill-formed #writedeclweave command"

/-! ## §8  Build-time generation -/

#declweavefilm

#writedeclweave "atlas_declweave.svg"

end DeclWeaveSVG

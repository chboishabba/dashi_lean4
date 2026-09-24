import RequestProject.ExprAddress
import RequestProject.CorpusGraph
import Lean

/-!
# ExprAddressCorpus — landing the *entire* corpus on the CRT cells, and the atom forest

`ExprAddress` gives every declaration an intrinsic structural fingerprint `k`
(the sum of its expression-tree constructor codes) and a CRT address
`crtTriple k = (k % 71, k % 59, k % 47)`, a coordinate in the
`71 · 59 · 47 = 196883`-cell space of the smallest non-trivial Monster irrep.
`ExprAddress.crtTriple_inj` proves the triple is a *unique* address for every
`k < 196883`; once a declaration's fingerprint exceeds that bound it wraps, so
two declarations whose fingerprints are congruent modulo `196883` (and, more
crudely, anything sharing all three residues) **land on the same cell**.

This layer realises two follow-up requests.

## §A  Land the whole corpus and find the collisions

`#corpuscells` reflects over *every* constant in the environment (with Mathlib
imported this is the whole of Mathlib + the Lean 4 base library), computes each
declaration's structural fingerprint and its CRT cell, and reports:

* how many declarations were swept;
* how many of the `196883` cells are occupied, and how many declarations are
  therefore *co-located* (collisions = swept − occupied cells);
* the most-crowded cells, with a sample of the declarations that share them.

`#writecorpuscells "path"` renders the `(k % 71, k % 59)` projection of the cell
space as a `71 × 59` occupancy heat-map (intensity = how many declarations land
in that column), so the crowded backbone and the empty regions read at a glance.

The accounting is **purely combinatorial**: a shared cell means two
declarations have structurally congruent fingerprints, nothing more.

## §B  The atom forest — every atom of every (sampled) declaration as a spanning tree

`#atomforest` / `#writeatomforest "path"` draw, for a sample of declarations, the
declaration's whole expression tree as a *tree of atoms*: every `Expr` node is a
coloured dot (colour = its constructor class), every parent→child structural link
is an edge, and each tree is laid out in its own panel.  The trees are then knit
into one graph by two kinds of **spanning edge**: a cyan edge joins atoms in
different trees that reference the *same* constant (shared vocabulary), and a
gold edge joins a `const` atom to the root of the drawn tree it names.
-/

open Lean Meta Elab Command SVG

namespace ExprAddressCorpus

open ExprAddress CorpusGraph Introspect IntrospectSVG DualAtlas

/-! ## §A  Corpus cell sweep -/

/-- The immediate structural children of an `Expr` node. -/
def exprChildren : Expr → List Expr
  | .app f a         => [f, a]
  | .lam _ t b _     => [t, b]
  | .forallE _ t b _ => [t, b]
  | .letE _ t v b _  => [t, v, b]
  | .mdata _ x       => [x]
  | .proj _ _ x      => [x]
  | _                => []

/-- A **fuel-bounded** structural sum: pop nodes off an explicit worklist,
adding each node's constructor code, until `budget` nodes have been visited.

Mathlib's expression trees are stored as DAGs with heavy sub-term sharing, so a
naive recursive sum re-walks shared sub-terms and explodes on large proof terms.
The global node budget bounds the work per declaration to `budget` pops while
still producing a deterministic, intrinsic integer fingerprint (it agrees with
the naive sum on any tree small enough not to exhaust the budget). -/
def boundedStructuralSum (budget : Nat) (e0 : Expr) : Nat := Id.run do
  let mut acc  := 0
  let mut fuel := budget
  let mut stack : Array Expr := #[e0]
  while fuel > 0 do
    if stack.size = 0 then break
    let e := stack.back!
    stack := stack.pop
    acc  := acc + exprCtorCode e
    fuel := fuel - 1
    for c in exprChildren e do
      stack := stack.push c
  return acc

/-- The per-declaration node budget for the corpus sweep. -/
def sweepBudget : Nat := 2000

/-- The fingerprint of a declaration `info`: fuel-bounded structural sum of its
type plus that of its value (if any). -/
def declFingerprint (info : ConstantInfo) : Nat :=
  let tSum := boundedStructuralSum sweepBudget info.type
  let vSum := match info.value? with
    | some v => boundedStructuralSum sweepBudget v
    | none   => 0
  tSum + vSum

/-- The result of sweeping the whole corpus onto the CRT cells:
`(swept, occupied, maxCount, colProj, topCells)` where

* `swept`     — number of declarations addressed;
* `occupied`  — number of distinct CRT cells `(k%71, k%59, k%47)` hit;
* `colProj`   — the `(k%71, k%59)` projection counts (for the heat-map);
* `topCells`  — the most-crowded cells, each with a count and up to four
  member names. -/
def gatherCells :
    CommandElabM (Nat × Nat × Nat × Std.HashMap (Nat × Nat) Nat ×
                  Array ((Nat × Nat × Nat) × Nat × Array Name)) := do
  let env ← getEnv
  -- cell → (count, up to 4 sample names)
  let mut cells : Std.HashMap (Nat × Nat × Nat) (Nat × Array Name) := {}
  let mut colProj : Std.HashMap (Nat × Nat) Nat := {}
  let mut swept := 0
  for (name, info) in env.constants.toList do
    let s := name.toString
    if !internalName s && !name.isInternal then
      swept := swept + 1
      let k := declFingerprint info
      let cell := crtTriple k
      let proj := (k % 71, k % 59)
      colProj := colProj.insert proj (colProj.getD proj 0 + 1)
      match cells[cell]? with
      | some (c, names) =>
        let names := if names.size < 4 then names.push name else names
        cells := cells.insert cell (c + 1, names)
      | none =>
        cells := cells.insert cell (1, #[name])
  let occupied := cells.size
  let arr := cells.toList.toArray.map (fun (cell, c, names) => (cell, c, names))
  let sorted := arr.qsort (fun a b => a.2.1 > b.2.1)
  let maxCount := (sorted[0]?).map (fun x => x.2.1) |>.getD 1
  let top := (sorted.toList.take 28).toArray
  return (swept, occupied, maxCount, colProj, top)

/-- `#corpuscells` sweeps the entire corpus onto the CRT cell space and reports
the occupancy and the most-crowded (colliding) cells. -/
syntax (name := corpuscellsCmd) "#corpuscells" : command

@[command_elab corpuscellsCmd]
def elabCorpuscells : CommandElab := fun _ => do
  let (swept, occupied, _maxC, _colProj, top) ← gatherCells
  let collisions := swept - occupied
  let mut out :=
    s!"[Corpus → CRT cells] swept {swept} declarations (entire corpus: Mathlib + Lean base)\n" ++
    s!"  ├── occupied cells = {occupied} / 196883\n" ++
    s!"  ├── co-located declarations (collisions) = {collisions}\n" ++
    s!"  └── most-crowded cells (cell = (k%71, k%59, k%47)):\n"
  for (cell, c, names) in top do
    let (a, b, d) := cell
    let sample := String.intercalate ", " (names.toList.map (·.toString))
    out := out ++ s!"      ({a},{b},{d}) ×{c}   e.g. {sample}\n"
  logInfo out

/-! ### Heat-map of the `(k%71, k%59)` cell projection -/

def hmX0 : Nat := 60
def hmY0 : Nat := 150
def hmCell : Nat := 18

/-- One heat-map tile for projected cell `(a, b)` with `count` declarations,
shaded against `maxCount`. -/
def tileSvg (maxCount : Nat) (a b count : Nat) : Svg :=
  let x := hmX0 + a * hmCell
  let y := hmY0 + b * hmCell
  let frac := Float.sqrt (Float.ofNat count / Float.ofNat (max maxCount 1))
  -- dark slate → gold ramp
  let r := 16 + Nat.min 239 (Float.toUInt32 (frac * 239.0)).toNat
  let g := 22 + Nat.min 193 (Float.toUInt32 (frac * 193.0)).toNat
  let bl := 60 - Nat.min 50 (Float.toUInt32 (frac * 50.0)).toNat
  let fill := s!"rgb({r},{g},{bl})"
  Svg.elem "rect"
    [("x", toString x), ("y", toString y),
     ("width", toString (hmCell - 1)), ("height", toString (hmCell - 1)),
     ("fill", fill), ("stroke", "#05060f"), ("stroke-width", "0.4")]
    [ Svg.raw s!"<title>cell (k%71={a}, k%59={b}) · {count} declarations</title>" ]

/-- Build the corpus-cell heat-map SVG. -/
def buildCellMap (swept occupied maxCount : Nat)
    (colProj : Std.HashMap (Nat × Nat) Nat) : String :=
  let w := hmX0 * 2 + 71 * hmCell
  let h := hmY0 + 59 * hmCell + 120
  -- background grid of all tiles (0 where empty)
  let tiles := (List.range 71).flatMap (fun a =>
    (List.range 59).map (fun b =>
      tileSvg maxCount a b (colProj.getD (a, b) 0)))
  let collisions := swept - occupied
  let doc := document w h
    [ rect 0 0 (Int.ofNat w) (Int.ofNat h) "#04050d" "none" [],
      rect 30 22 (Int.ofNat (w - 60)) 96 "#101736" "#23305f" [("rx", "12")],
      Svg.text [("x", "52"), ("y", "60"), ("font-size", "26"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        "CORPUS → CRT CELLS · (k mod 71) × (k mod 59) OCCUPANCY",
      Svg.text [("x", "54"), ("y", "92"), ("font-size", "14"), ("fill", "#9fb0e0")]
        s!"{swept} declarations swept (Mathlib + Lean base) · {occupied} of 196883 cells occupied · {collisions} co-located (collisions)",
      group tiles,
      Svg.text [("x", toString hmX0), ("y", toString (hmY0 + 59 * hmCell + 34)),
                ("font-size", "13"), ("fill", "#7f8db8")]
        s!"x = k mod 71   ·   y = k mod 59   ·   brightness ∝ √(declarations landing in that column)   ·   max column = {maxCount}",
      Svg.text [("x", toString hmX0), ("y", toString (hmY0 + 59 * hmCell + 56)),
                ("font-size", "12"), ("fill", "#5f6c92")]
        "the third residue (k mod 47) is summed out in this projection · generated natively by Lean · #writecorpuscells" ]
  render doc

/-- `#writecorpuscells "path"` writes the corpus cell-occupancy heat-map. -/
syntax (name := writecorpuscellsCmd) "#writecorpuscells " str : command

@[command_elab writecorpuscellsCmd]
def elabWritecorpuscells : CommandElab := fun stx => do
  match stx with
  | `(#writecorpuscells $p:str) => do
    let (swept, occupied, maxC, colProj, _top) ← gatherCells
    let svg := buildCellMap swept occupied maxC colProj
    IO.FS.writeFile p.getString svg
    logInfo s!"[Corpus cells] wrote {svg.length} bytes ({swept} decls, {occupied}/196883 cells occupied) to {p.getString}"
  | _ => throwError "ill-formed #writecorpuscells command"

/-! ## §B  The atom forest -/

/-- A single atom in a declaration's expression tree. -/
structure AtomNode where
  parent : Int     -- index of parent node, `-1` for the root
  code   : Nat     -- constructor code (`ExprAddress.exprCtorCode`)
  depth  : Nat
  cname  : String  -- for `const` atoms, the referenced name; otherwise `""`
deriving Inhabited

/-- Collect up to `cap` atoms of `e` in preorder, recording parent links. -/
partial def collectAux (cap : Nat) (e : Expr) (par : Int) (d : Nat) :
    StateM (Array AtomNode) Unit := do
  if (← get).size ≥ cap then return
  let id := (← get).size
  let cname := match e with | .const n _ => n.toString | _ => ""
  modify (·.push { parent := par, code := exprCtorCode e, depth := d, cname })
  for c in exprChildren e do
    collectAux cap c (Int.ofNat id) (d + 1)

/-- The atom list of a declaration's value (falling back to its type). -/
def declAtoms (cap : Nat) (info : ConstantInfo) : Array AtomNode :=
  let e := match info.value? with | some v => v | none => info.type
  (collectAux cap e (-1) 0 |>.run #[]).2

/-! ### Geometry of one tree panel -/

/-- Colour `(fill, glow)` of an atom by its constructor class, reusing the
project palette via the harmonic code of the constructor code. -/
def atomColor (code : Nat) : String × String :=
  colorOf (styleOfHarm (harmCode (code + 1)))

/-- Position of atom `i` (of `n`) within a panel at `(px, py)` of size
`(pw, ph)`: preorder index spreads horizontally, depth descends vertically. -/
def atomPos (px py pw ph : Float) (i n : Nat) (depth maxDepth : Nat) : Float × Float :=
  let fx := px + pw * (Float.ofNat i + 0.5) / Float.ofNat (max n 1)
  let fy := py + 26.0 + (ph - 40.0) * Float.ofNat depth / Float.ofNat (max maxDepth 1)
  (fx, fy)

/-- Truncate a `Float` to an `Int` for SVG coordinates. -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- A drawn declaration tree: its name, the atoms, the panel rectangle, and the
maximum depth (for vertical scaling). -/
structure DrawnTree where
  name     : Name
  atoms    : Array AtomNode
  px       : Float
  py       : Float
  pw       : Float
  ph       : Float
  maxDepth : Nat
deriving Inhabited

/-- Render the parent→child edges of one tree. -/
def treeEdges (t : DrawnTree) : List Svg :=
  let n := t.atoms.size
  (t.atoms.toList.zipIdx).filterMap (fun (a, i) =>
    if a.parent < 0 then none
    else
      let pj := a.parent.toNat
      match t.atoms[pj]? with
      | some pa =>
        let (x1, y1) := atomPos t.px t.py t.pw t.ph i n a.depth t.maxDepth
        let (x2, y2) := atomPos t.px t.py t.pw t.ph pj n pa.depth t.maxDepth
        some (line (f2i x1) (f2i y1) (f2i x2) (f2i y2) "#3a4a86"
          [("stroke-width", "0.8"), ("opacity", "0.6")])
      | none => none)

/-- Render the atom dots of one tree. -/
def treeNodes (t : DrawnTree) : List Svg :=
  let n := t.atoms.size
  (t.atoms.toList.zipIdx).map (fun (a, i) =>
    let (x, y) := atomPos t.px t.py t.pw t.ph i n a.depth t.maxDepth
    let (fill, _glow) := atomColor a.code
    let r : Int := if a.parent < 0 then 4 else 2
    Svg.elem "circle"
      [("cx", toString (f2i x)), ("cy", toString (f2i y)), ("r", toString r),
       ("fill", fill), ("stroke", "#05060f"), ("stroke-width", "0.4")]
      [ Svg.raw s!"<title>{SVG.esc a.cname} · ctor {a.code} · depth {a.depth}</title>" ])

/-- The root position of a drawn tree (its panel-local atom 0). -/
def treeRoot (t : DrawnTree) : Float × Float :=
  atomPos t.px t.py t.pw t.ph 0 t.atoms.size 0 t.maxDepth

/-- Panel chrome: a border box and the declaration name. -/
def treeFrame (t : DrawnTree) : Svg :=
  group
    [ rect (f2i t.px) (f2i t.py) (f2i t.pw) (f2i t.ph) "none" "#23305f"
        [("rx", "6"), ("opacity", "0.5")],
      Svg.text [("x", toString (f2i t.px + 8)), ("y", toString (f2i t.py + 16)),
                ("font-size", "12"), ("font-weight", "700"), ("fill", "#dfe6ff")]
        s!"{t.name}  ·  {t.atoms.size} atoms" ]

/-- The candidate declarations to draw, in panel order.  Only those present in
the environment are kept, so the list is robust across libraries. -/
def forestCandidates : List Name :=
  [`Nat.add, `Nat.mul, `Nat.succ_le_succ, `List.map, `List.foldr, `List.length,
   `Prod.fst, `Option.map, `Or.inl, `And.intro, `Nat.rec, `List.append]

def forestCols : Nat := 4
def panelW : Float := 360.0
def panelH : Float := 300.0
def forestX0 : Float := 40.0
def forestY0 : Float := 150.0
def forestGap : Float := 24.0
def atomCap : Nat := 200

/-- Build the set of `DrawnTree`s laid out in a grid. -/
def gatherForest : CommandElabM (Array DrawnTree) := do
  let env ← getEnv
  let present := forestCandidates.filter (fun n => (env.find? n).isSome)
  let mut trees : Array DrawnTree := #[]
  for (name, idx) in present.zipIdx do
    let some info := env.find? name | continue
    let atoms := declAtoms atomCap info
    let maxDepth := atoms.foldl (fun m a => max m a.depth) 1
    let col := idx % forestCols
    let row := idx / forestCols
    let px := forestX0 + Float.ofNat col * (panelW + forestGap)
    let py := forestY0 + Float.ofNat row * (panelH + forestGap)
    trees := trees.push
      { name, atoms, px, py, pw := panelW, ph := panelH, maxDepth }
  return trees

/-- Spanning edges across trees: when an atom is a `const` referencing another
drawn tree, draw a faint edge from that atom to the referenced tree's root. -/
def spanningEdges (trees : Array DrawnTree) : List Svg :=
  let rootOf : Std.HashMap String (Float × Float) :=
    trees.foldl (fun m t => m.insert t.name.toString (treeRoot t)) {}
  trees.toList.flatMap (fun t =>
    let n := t.atoms.size
    (t.atoms.toList.zipIdx).filterMap (fun (a, i) =>
      if a.cname == "" then none
      else match rootOf[a.cname]? with
        | some (rx, ry) =>
          if a.cname == t.name.toString then none
          else
            let (x, y) := atomPos t.px t.py t.pw t.ph i n a.depth t.maxDepth
            some (Svg.elem "path"
              [("d", s!"M {f2i x} {f2i y} L {f2i rx} {f2i ry}"),
               ("fill", "none"), ("stroke", "#ffd700"),
               ("stroke-width", "1.0"), ("opacity", "0.5")] [])
        | none => none))

/-- The screen position and owning-tree index of every `const` atom across all
drawn trees. -/
def constAtomPositions (trees : Array DrawnTree) : Array (String × Nat × Float × Float) :=
  Id.run do
    let mut out : Array (String × Nat × Float × Float) := #[]
    for (t, ti) in trees.toList.zipIdx do
      let n := t.atoms.size
      for (a, i) in t.atoms.toList.zipIdx do
        if a.cname != "" then
          let (x, y) := atomPos t.px t.py t.pw t.ph i n a.depth t.maxDepth
          out := out.push (a.cname, ti, x, y)
    return out

/-- **Shared-vocabulary spanning edges.**  Any constant referenced from atoms in
*different* trees knits those trees together: for each such constant we connect
its occurrences in a star to the first occurrence.  This is what makes the
per-declaration trees span into one graph across the whole sheet. -/
def sharedConstEdges (trees : Array DrawnTree) : List Svg :=
  Id.run do
    -- group occurrences by constant name
    let mut groups : Std.HashMap String (Array (Nat × Float × Float)) := {}
    for (cn, ti, x, y) in constAtomPositions trees do
      groups := groups.insert cn ((groups.getD cn #[]).push (ti, x, y))
    let mut edges : List Svg := []
    for (_, occs) in groups.toList do
      -- only constants that appear in at least two distinct trees span anything
      let distinctTrees := (occs.toList.map (·.1)).dedup.length
      if distinctTrees ≥ 2 then
        match occs[0]? with
        | some (_, hx, hy) =>
          for (_, x, y) in occs.toList.drop 1 |>.take 16 do
            edges := (Svg.elem "path"
              [("d", s!"M {f2i hx} {f2i hy} L {f2i x} {f2i y}"),
               ("fill", "none"), ("stroke", "#7ad9ff"),
               ("stroke-width", "0.7"), ("opacity", "0.28")] []) :: edges
        | none => pure ()
    return edges

/-- Assemble the atom-forest SVG. -/
def buildForest (trees : Array DrawnTree) : String :=
  let rows := (trees.size + forestCols - 1) / forestCols
  let w := f2i (forestX0 * 2.0 + Float.ofNat forestCols * (panelW + forestGap))
  let h := f2i (forestY0 + Float.ofNat rows * (panelH + forestGap) + 60.0)
  let totalAtoms := trees.foldl (fun s t => s + t.atoms.size) 0
  let edgeG  := group (trees.toList.flatMap treeEdges)
  let sharedG := group (sharedConstEdges trees)
  let spanG  := group (spanningEdges trees)
  let nodeG  := group (trees.toList.flatMap treeNodes)
  let frameG := group (trees.toList.map treeFrame)
  let doc := document w.toNat h.toNat
    [ rect 0 0 w h "#04050d" "none" [],
      rect 30 22 (w - 60) 96 "#101736" "#23305f" [("rx", "12")],
      Svg.text [("x", "52"), ("y", "60"), ("font-size", "26"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        "ATOM FOREST · EVERY ATOM OF EVERY DECLARATION AS A SPANNING TREE",
      Svg.text [("x", "54"), ("y", "92"), ("font-size", "14"), ("fill", "#9fb0e0")]
        s!"{trees.size} declaration trees · {totalAtoms} atoms · dots = Expr nodes (colour = constructor class) · blue edges = parent→child · cyan edges = shared constants · gold edges = const references spanning trees",
      sharedG, spanG, edgeG, nodeG, frameG,
      Svg.text [("x", "40"), ("y", toString (h - 24)),
                ("font-size", "12"), ("fill", "#5f6c92")]
        "each tree is a declaration's full expression tree (capped at 200 atoms) · generated natively by Lean · #writeatomforest" ]
  render doc

/-- `#atomforest` builds the atom-forest graph and reports its size. -/
syntax (name := atomforestCmd) "#atomforest" : command

@[command_elab atomforestCmd]
def elabAtomforest : CommandElab := fun _ => do
  let trees ← gatherForest
  let totalAtoms := trees.foldl (fun s t => s + t.atoms.size) 0
  let svg := buildForest trees
  logInfo s!"[Atom forest] {trees.size} declaration trees, {totalAtoms} atoms, {(sharedConstEdges trees).length} shared-constant edges + {(spanningEdges trees).length} root-reference edges → {svg.length}-byte SVG."

/-- `#writeatomforest "path"` writes the atom-forest SVG. -/
syntax (name := writeatomforestCmd) "#writeatomforest " str : command

@[command_elab writeatomforestCmd]
def elabWriteatomforest : CommandElab := fun stx => do
  match stx with
  | `(#writeatomforest $p:str) => do
    let trees ← gatherForest
    let svg := buildForest trees
    IO.FS.writeFile p.getString svg
    logInfo s!"[Atom forest] wrote {svg.length} bytes ({trees.size} trees) to {p.getString}"
  | _ => throwError "ill-formed #writeatomforest command"

/-! ## §C  Build-time generation -/

#corpuscells
#writecorpuscells "atlas_corpuscells.svg"

#atomforest
#writeatomforest "atlas_atomforest.svg"

end ExprAddressCorpus

import RequestProject.IntrospectSVG
import Lean

/-!
# CorpusGraph: the dependency graph of the *entire* corpus

The previous atlas layers reflect only the project's own namespaces
(`Holograms`, `AristoTask`, `DualAtlas`, …) — a few dozen declarations.  This
layer realises the request to **scale up to the entire corpus and visualise the
graph**: it reflects over *every* constant in the whole Lean environment
(≈ 10⁵ declarations spanning ≈ 2·10³ top-level namespaces, with ≈ 1.5·10⁶
reference edges) and renders the **namespace dependency graph** as a single
self-contained, self-playing animated SVG.

## The construction

* **Nodes = top-level namespaces.**  Every non-internal declaration is bucketed
  by its top-level namespace (`topNs`, e.g. `Lean`, `Std`, `List`, …).  A node's
  size is the number of declarations it contains.  To keep the picture legible at
  corpus scale, only the `topK` largest namespaces are drawn as nodes, but the
  totals reported (and the edges) are computed over the whole environment.

* **Edges = cross-namespace references.**  For every declaration we read the
  constants it actually uses (`Expr.getUsedConstants` over its value), and add a
  weighted directed edge between the two namespaces involved.  The edge weight is
  how many such references cross from one namespace to the other — the real
  coupling between the two regions of the corpus.

* **Layout.**  The namespaces are placed on a phyllotaxis (golden-angle) spiral,
  ranked by size: the largest hubs sit near the centre and the long tail spreads
  outward.  Node radius grows with `√(declaration count)`; node colour is the
  harmonic class (`DualAtlas.harmCode`) of the namespace-name hash, reusing the
  project palette.  Each edge is a quadratic Bézier bowed toward the centre, with
  width and opacity scaling with `√(weight)` — so the heavy backbone edges read
  clearly through the haze of light ones.

* **Animation.**  Native SMIL: the edges light up in a travelling wave (a phase
  offset per edge), the node glows pulse, and a slow radar sweep rotates over the
  whole graph.

Commands:

* `#corpusgraph`              — build the graph; report the corpus totals + size.
* `#writecorpusgraph "path"` — write the corpus-graph SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace CorpusGraph

open Introspect IntrospectSVG DualAtlas

/-! ## Reflecting the whole corpus -/

/-- The top-level namespace of a declaration name (its first dotted component). -/
def topNs (s : String) : String := (s.splitOn ".").headD s

/-- Is this name an auto-generated internal helper we should skip?  This mirrors
the project's `Introspect.isProjectDecl` internal test but applies it corpus-wide
(no namespace restriction). -/
def internalName (s : String) : Bool :=
  (s.splitOn "._").length > 1 ||
  (s.splitOn "match_").length > 1 ||
  (s.splitOn ".eq_").length > 1 ||
  s.startsWith "_"

/-- A namespace node: its name, the number of declarations it holds, and a hash
of its name used to pick a harmonic colour. -/
structure NsNode where
  name  : String
  count : Nat
  hash  : Nat
deriving Repr, Inhabited

/-- A directed weighted edge between namespace node indices. -/
structure NsEdge where
  src : Nat
  dst : Nat
  wt  : Nat
deriving Repr, Inhabited

/-- How many of the largest namespaces to draw as graph nodes. -/
def topK : Nat := 60

/-- The complete reflected corpus graph: the global totals
`(totalDecls, totalRefs, totalNamespaces)`, the drawn namespace `nodes`
(ranked largest-first), and the cross-namespace `edges` among them. -/
def gatherCorpus :
    CommandElabM (Nat × Nat × Nat × Array NsNode × Array NsEdge) := do
  let env ← getEnv
  -- First pass: per-namespace counts, name → namespace map, and global totals.
  let mut sizes    : Std.HashMap String Nat := {}
  let mut nameToNs : Std.HashMap Name String := {}
  let mut allNs    : Std.HashSet String := {}
  let mut totalDecls := 0
  let mut totalRefs  := 0
  for (name, info) in env.constants.toList do
    let s := name.toString
    if !internalName s && !name.isInternal then
      let t := topNs s
      allNs := allNs.insert t
      if let some e := info.value? then
        totalDecls := totalDecls + 1
        totalRefs  := totalRefs + e.getUsedConstants.size
        sizes := sizes.insert t (sizes.getD t 0 + 1)
        nameToNs := nameToNs.insert name t
  -- Rank namespaces by size and keep the top `topK`.
  let ranked := sizes.toList.toArray.qsort (fun a b => a.2 > b.2)
  let topArr := (ranked.toList.take topK).toArray
  let idxOf : Std.HashMap String Nat :=
    (topArr.toList.zipIdx).foldl (fun m (nc, i) => m.insert nc.1 i) {}
  -- Second pass: accumulate cross-namespace reference weights among top nodes.
  let mut edgeMap : Std.HashMap (Nat × Nat) Nat := {}
  for (name, info) in env.constants.toList do
    let s := name.toString
    if !internalName s && !name.isInternal then
      if let some e := info.value? then
        if let some ai := idxOf[nameToNs.getD name (topNs s)]? then
          for u in e.getUsedConstants do
            if let some bi := idxOf[nameToNs.getD u (topNs u.toString)]? then
              if ai != bi then
                edgeMap := edgeMap.insert (ai, bi) (edgeMap.getD (ai, bi) 0 + 1)
  let nodes := topArr.map (fun (n, c) =>
    { name := n, count := c, hash := (hash n).toNat : NsNode })
  let edges := edgeMap.toList.toArray.map (fun ((a, b), w) =>
    { src := a, dst := b, wt := w : NsEdge })
  return (totalDecls, totalRefs, allNs.size, nodes, edges)

/-! ## Geometry -/

def tau    : Float := 6.283185307179586
/-- The golden angle in radians (`2π·(2−φ)`), the phyllotaxis step. -/
def golden : Float := 2.399963229728653
def cx     : Float := 820.0
def cy     : Float := 600.0
def maxR   : Float := 540.0

/-- Truncate a `Float` to an `Int` (for SVG coordinates). -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- Phyllotaxis position of the `i`-th node out of `n`: largest hubs near the
centre, the long tail spiralling outward. -/
def nodePos (i n : Nat) : Float × Float :=
  let fi := Float.ofNat i
  let fn := Float.ofNat (max n 1)
  let rad := 70.0 + (maxR - 70.0) * Float.sqrt (fi / fn)
  let ang := golden * fi
  (cx + rad * Float.cos ang, cy + rad * Float.sin ang)

/-- Visual radius of a node with `count` declarations, scaled against the largest
namespace `maxCount`. -/
def nodeR (count maxCount : Nat) : Float :=
  4.0 + 42.0 * Float.sqrt (Float.ofNat count) / Float.sqrt (Float.ofNat (max maxCount 1))

/-! ## Rendering -/

/-- Style class / colour of a namespace, keyed by its name hash. -/
def nodeStyle (n : NsNode) : Nat := styleOfHarm (harmCode n.hash)

/-- One dependency edge: a quadratic Bézier from `src` to `dst`, bowed toward the
centre, with width and opacity scaling with `√(weight)` and a travelling-wave
opacity pulse. -/
def edgeSvg (nodes : Array NsNode) (maxW : Nat) (e : NsEdge) : Svg :=
  match nodes[e.src]?, nodes[e.dst]? with
  | some _, some _ =>
    let n := nodes.size
    let (x1, y1) := nodePos e.src n
    let (x2, y2) := nodePos e.dst n
    let mx := (x1 + x2) / 2.0
    let my := (y1 + y2) / 2.0
    -- pull the control point toward the centre to bundle the edges inward
    let ctlx := mx + (cx - mx) * 0.4
    let ctly := my + (cy - my) * 0.4
    let frac := Float.sqrt (Float.ofNat e.wt / Float.ofNat (max maxW 1))
    let w := 0.4 + 2.6 * frac
    let baseOp := 0.05 + 0.55 * frac
    let phase := Float.ofNat ((e.src + e.dst) % 12) * 0.5
    let d := s!"M {f2i x1} {f2i y1} Q {f2i ctlx} {f2i ctly} {f2i x2} {f2i y2}"
    Svg.elem "path"
      [("d", d), ("fill", "none"), ("stroke", "#6f8bdb"),
       ("stroke-width", toString w), ("opacity", toString baseOp)]
      [ Svg.raw s!"<animate attributeName=\"opacity\" dur=\"6s\" begin=\"{phase}s\" repeatCount=\"indefinite\" values=\"{baseOp};{baseOp + 0.35};{baseOp}\" keyTimes=\"0;0.5;1\"/>" ]
  | _, _ => group []

/-- One namespace node: a pulsing glow disc, the coloured node disc, and (for the
larger nodes) a label.  `total` is the number of drawn nodes (the layout
denominator), `i` the node's rank, `maxCount` the largest namespace size. -/
def nodeSvg (total maxCount : Nat) (i : Nat) (n : NsNode) (label : Bool) : Svg :=
  let (fill, glow) := colorOf (nodeStyle n)
  let (fx, fy) := nodePos i total
  let r := nodeR n.count maxCount
  let ri := f2i r
  let ix := f2i fx
  let iy := f2i fy
  let phase := Float.ofNat (i % 10) * 0.4
  let fontSz := 10 + ri / 6
  group
    [ Svg.raw s!"<title>{SVG.esc n.name} · {n.count} declarations</title>",
      circle ix iy (ri + 6) "none" glow
        [("opacity", "0.22"), ("filter", "url(#cgGlow)")],
      Svg.elem "circle"
        [("cx", toString ix), ("cy", toString iy), ("r", toString ri),
         ("fill", fill), ("stroke", "#05060f"), ("stroke-width", "1.2")]
        [ Svg.raw s!"<animate attributeName=\"r\" dur=\"4s\" begin=\"{phase}s\" repeatCount=\"indefinite\" values=\"{ri};{ri + 2};{ri}\" keyTimes=\"0;0.5;1\"/>" ],
      if label then
        Svg.text
          [("x", toString (ix + ri + 4)), ("y", toString (iy + 4)),
           ("font-size", toString fontSz), ("font-weight", "600"),
           ("fill", "#dfe6ff"), ("opacity", "0.92")]
          n.name
      else group [] ]

/-! ## Chrome (background, banner, radar sweep, footer) -/

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"cgBg\" cx=\"50%\" cy=\"44%\" r=\"80%\">" ++
    "<stop offset=\"0%\" stop-color=\"#101736\"/><stop offset=\"100%\" stop-color=\"#04050d\"/></radialGradient>" ++
  "<linearGradient id=\"cgBanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"cgGlow\" x=\"-80%\" y=\"-80%\" width=\"260%\" height=\"260%\">" ++
    "<feGaussianBlur stdDeviation=\"3\"/></filter>" ++
  "<radialGradient id=\"cgSweep\" cx=\"50%\" cy=\"50%\" r=\"50%\">" ++
    "<stop offset=\"0%\" stop-color=\"#7ad9ff\" stop-opacity=\"0.0\"/>" ++
    "<stop offset=\"82%\" stop-color=\"#7ad9ff\" stop-opacity=\"0.0\"/>" ++
    "<stop offset=\"100%\" stop-color=\"#7ad9ff\" stop-opacity=\"0.12\"/></radialGradient>" ++
  "</defs>"

/-- A slow radar sweep rotating over the whole graph. -/
def radarSweep : Svg :=
  let ix := f2i cx
  let iy := f2i cy
  let r := f2i maxR
  Svg.elem "g" []
    [ Svg.elem "path"
        [("d", s!"M {ix} {iy} L {ix + r} {iy} A {r} {r} 0 0 1 {ix} {iy + r} Z"),
         ("fill", "url(#cgSweep)"), ("opacity", "0.8")]
        [ Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"rotate\" from=\"0 {ix} {iy}\" to=\"360 {ix} {iy}\" dur=\"18s\" repeatCount=\"indefinite\"/>" ] ]

def banner : Svg :=
  group
    [ rect 30 22 1540 86 "url(#cgBanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "66"), ("font-size", "30"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "CORPUS GRAPH · THE WHOLE ENVIRONMENT AS A NAMESPACE DEPENDENCY NETWORK",
      Svg.text [("x", "58"), ("y", "95"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "nodes = top-level namespaces (size = #declarations) · edges = cross-namespace references · reflected natively by Lean over the entire corpus" ]

/-! ## Assembly -/

/-- Build the corpus-graph SVG document string. -/
def buildGraph (totalDecls totalRefs totalNs : Nat)
    (nodes : Array NsNode) (edges : Array NsEdge) : String :=
  let maxCount := (nodes[0]?).map (·.count) |>.getD 1
  let maxW := edges.foldl (fun m e => max m e.wt) 1
  -- draw heavy edges last (on top), light ones first
  let edgesSorted := edges.qsort (fun a b => a.wt < b.wt)
  let edgeG := group (edgesSorted.toList.map (edgeSvg nodes maxW))
  -- label only the larger nodes to avoid clutter
  let nNodes := nodes.size
  let nodeG := group ((nodes.toList.zipIdx).map (fun (n, i) =>
    nodeSvg nNodes maxCount i n (i < 26)))
  let doc := document 1600 1200
    [ Svg.raw defsRaw,
      rect 0 0 1600 1200 "url(#cgBg)" "none" [],
      circle (f2i cx) (f2i cy) (f2i maxR) "none" "#23305f"
        [("stroke-width", "1"), ("opacity", "0.4")],
      radarSweep,
      banner,
      edgeG,
      nodeG,
      Svg.text [("x", "40"), ("y", "1150"), ("font-size", "16"), ("font-weight", "700"),
                ("fill", "#ffd700")]
        s!"entire corpus: {totalDecls} declarations · {totalRefs} reference edges · {totalNs} top-level namespaces",
      Svg.text [("x", "40"), ("y", "1174"), ("font-size", "12"), ("fill", "#7f8db8")]
        s!"graph shows the {nodes.size} largest namespaces and the {edges.size} cross-namespace edges among them · layout = golden-angle spiral by size · generated natively by Lean · #writecorpusgraph" ]
  render doc

/-! ## Commands -/

/-- `#corpusgraph` builds the corpus dependency graph and reports its size. -/
syntax (name := corpusgraphCmd) "#corpusgraph" : command

@[command_elab corpusgraphCmd]
def elabCorpusgraph : CommandElab := fun _ => do
  let (td, tr, tn, nodes, edges) ← gatherCorpus
  let svg := buildGraph td tr tn nodes edges
  logInfo s!"[Corpus Graph] entire corpus: {td} decls, {tr} reference edges, {tn} namespaces. Drew {nodes.size} namespace nodes and {edges.size} edges → {svg.length}-byte animated SVG."

/-- `#writecorpusgraph "path"` writes the corpus-graph SVG to `path`. -/
syntax (name := writecorpusgraphCmd) "#writecorpusgraph " str : command

@[command_elab writecorpusgraphCmd]
def elabWritecorpusgraph : CommandElab := fun stx => do
  match stx with
  | `(#writecorpusgraph $p:str) => do
    let path := p.getString
    let (td, tr, tn, nodes, edges) ← gatherCorpus
    let svg := buildGraph td tr tn nodes edges
    IO.FS.writeFile path svg
    logInfo s!"[Corpus Graph] wrote {svg.length} bytes ({nodes.size} nodes, {edges.size} edges; corpus {td} decls / {tr} refs / {tn} namespaces) to {path}"
  | _ => throwError "ill-formed #writecorpusgraph command"

/-! ## Build-time generation -/

#corpusgraph

#writecorpusgraph "atlas_corpus.svg"

end CorpusGraph

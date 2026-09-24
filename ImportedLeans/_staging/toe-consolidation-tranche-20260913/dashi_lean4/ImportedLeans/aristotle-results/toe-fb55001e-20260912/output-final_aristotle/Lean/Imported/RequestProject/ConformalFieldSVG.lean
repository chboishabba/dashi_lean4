import RequestProject.ConformalField
import RequestProject.SemanticCID
import RequestProject.SVG
import Lean

/-!
# ConformalFieldSVG: the multi-hash conformal field, *as an animation*

`RequestProject.ConformalField` proves two things and draws a **static**
picture of the second (`atlas_conformal.svg`).  This layer turns both into a
single self-contained, self-playing **animated SVG** whose every coordinate is
computed natively by Lean from the very definitions the proofs use
(`ConformalField.arrow`/`arrowAt`, `multiHash`, `score`, `digestSpace`), so the
film is faithful to the formalised mathematics.

The film has three animated movements:

1. **Conformal arrow field** — the affine permutation `x ↦ (a·x + b) mod p` of
   `ConformalField.arrow` drawn on a ring of `gridP` hash nodes.  The arrows
   *draw themselves in* one by one (a `stroke-dashoffset` sweep), visualising
   `arrow_injective`/`arrow_surjective`: every node has exactly one out-arrow and
   one in-arrow.
2. **Orbit token** — a glowing token rides the permutation, hopping node → node
   along the arrows `x ↦ arrowAt x`, so the eye can verify the field is a single
   structure-preserving cycle (the dynamical content of `arrow_bijective`).  The
   unique fixed point `x = (1-a)⁻¹·b` is highlighted in gold.
3. **Multi-hash bars** — for the featured declarations, the four salted hashes
   of `multiHash` grow in as horizontal bars (each `< digestSpace = 2^24`),
   making visible that the score is a *vector* of hashes, not a single digest
   (`score_eq_iff_multiHash_eq`).

Commands:

* `#conformalfilm`               — build the film for the featured examples, report size.
* `#writeconformalanim "path"`   — build the film and write the animated SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace ConformalFieldSVG

open ConformalField

/-! ## Arrow-field geometry (mirrors `ConformalField.elabConformalsweep`) -/

/-- Number of hash nodes drawn on the ring (a small prime, as in the sweep). -/
def gridP : Nat := 97
/-- Affine multiplier of the conformal arrow `x ↦ a·x + b`. -/
def aCoef : Nat := 5
/-- Affine shift of the conformal arrow `x ↦ a·x + b`. -/
def bCoef : Nat := 11

/-- The conformal arrow on the drawing grid: `x ↦ (a·x + b) mod gridP`. -/
def arrowAt (x : Nat) : Nat := (aCoef * x + bCoef) % gridP

/-- Ring centre x. -/
def cxF : Float := 400.0
/-- Ring centre y. -/
def cyF : Float := 440.0
/-- Ring radius. -/
def rF : Float := 300.0

/-- Position of hash node `i` on the ring. -/
def nodePos (i : Nat) : Float × Float :=
  let θ := 2.0 * 3.14159265 * (Float.ofNat i) / (Float.ofNat gridP)
  (cxF + rF * Float.cos θ, cyF + rF * Float.sin θ)

/-- Format a `Float` coordinate for SVG. -/
def fc (f : Float) : String := toString f

/-- The orbit of a start node under repeated application of `arrowAt`. -/
def orbitAux : Nat → Nat → List Nat
  | _, 0     => []
  | x, k + 1 => x :: orbitAux (arrowAt x) k

/-- `n` consecutive hops of the conformal arrow starting from `start`. -/
def orbit (start n : Nat) : List Nat := orbitAux start n

/-- Per-arrow colour, cycling a small cool→warm palette. -/
def palette : Nat → String
  | 0 => "#2bd0c0" | 1 => "#4fd86a" | 2 => "#ffd23d"
  | 3 => "#ff7a59" | 4 => "#ff5db1" | _ => "#8a6bff"

/-- Per-salt colour for the multi-hash bars. -/
def saltColor : Nat → String
  | 0 => "#2bd0c0" | 1 => "#ffd23d" | 2 => "#ff7a59" | _ => "#ff5db1"

/-! ## Movement 1 — the arrows draw themselves in -/

/-- Every conformal arrow `x ↦ arrowAt x`, each drawn in on a staggered
`stroke-dashoffset` sweep. -/
def arrowsSvg : String :=
  (List.range gridP).foldl (fun acc x =>
    let y := arrowAt x
    let (x0, y0) := nodePos x
    let (x1, y1) := nodePos y
    let col := palette (x % 6)
    let beg := s!"{x * 28}ms"
    acc ++
      s!"<line x1=\"{fc x0}\" y1=\"{fc y0}\" x2=\"{fc x1}\" y2=\"{fc y1}\" " ++
      s!"stroke=\"{col}\" stroke-width=\"1.4\" opacity=\"0.8\" marker-end=\"url(#ahd)\" " ++
      s!"stroke-dasharray=\"900\" stroke-dashoffset=\"900\">" ++
      s!"<animate attributeName=\"stroke-dashoffset\" from=\"900\" to=\"0\" begin=\"{beg}\" " ++
      s!"dur=\"0.7s\" fill=\"freeze\"/></line>") ""

/-- The hash nodes (small dots fading in), with the affine fixed point in gold. -/
def nodesSvg : String :=
  -- fixed point: solution of x ≡ a·x + b, i.e. (1-a)·x ≡ b (mod p); here x = 70.
  (List.range gridP).foldl (fun acc i =>
    let (x0, y0) := nodePos i
    let isFix := arrowAt i == i
    let beg := s!"{i * 28}ms"
    if isFix then
      acc ++
        s!"<circle cx=\"{fc x0}\" cy=\"{fc y0}\" r=\"7\" fill=\"#ffd700\" stroke=\"#fff\" stroke-width=\"1.5\">" ++
        s!"<animate attributeName=\"r\" values=\"5;9;5\" dur=\"1.6s\" repeatCount=\"indefinite\"/></circle>"
    else
      acc ++
        s!"<circle cx=\"{fc x0}\" cy=\"{fc y0}\" r=\"3\" fill=\"#cfd8f5\" opacity=\"0\">" ++
        s!"<animate attributeName=\"opacity\" from=\"0\" to=\"0.9\" begin=\"{beg}\" dur=\"0.4s\" fill=\"freeze\"/></circle>") ""

/-! ## Movement 2 — a token rides the permutation -/

/-- A glowing token hopping node → node along the conformal arrows. -/
def tokenSvg : String :=
  let orb := orbit 1 96 ++ [1]
  let xs := String.intercalate ";" (orb.map (fun i => fc (nodePos i).1))
  let ys := String.intercalate ";" (orb.map (fun i => fc (nodePos i).2))
  let dur := fc (Float.ofNat orb.length * 0.16)
  s!"<circle r=\"8\" fill=\"#ffffff\" filter=\"url(#glow)\" opacity=\"0\">" ++
  s!"<animate attributeName=\"opacity\" from=\"0\" to=\"0.95\" begin=\"3s\" dur=\"0.5s\" fill=\"freeze\"/>" ++
  s!"<animate attributeName=\"cx\" values=\"{xs}\" begin=\"3s\" dur=\"{dur}s\" " ++
  s!"repeatCount=\"indefinite\" calcMode=\"linear\"/>" ++
  s!"<animate attributeName=\"cy\" values=\"{ys}\" begin=\"3s\" dur=\"{dur}s\" " ++
  s!"repeatCount=\"indefinite\" calcMode=\"linear\"/></circle>"

/-! ## Movement 3 — multi-hash bars for the featured declarations -/

/-- The declarations featured in the multi-hash panel. -/
def featured : List Name := [`Nat.add, `List.map, `Prod.fst]

/-- Left edge of the multi-hash panel. -/
def panelX : Int := 760
/-- Maximum bar length (a full `digestSpace`). -/
def barMax : Float := 300.0

/-- The animated multi-hash panel for the reflected `items`. -/
def multiHashPanel (items : List (Name × Nat)) : List Svg :=
  items.zipIdx.flatMap (fun ((nm, k), i) =>
    let by0 : Int := 120 + Int.ofNat i * 165
    let hs := multiHash k
    let header :=
      [ Svg.text [("x", toString (panelX)), ("y", toString by0),
                  ("font-size","13"), ("font-weight","800"), ("fill","#ffd700")]
          nm.toString,
        Svg.text [("x", toString (panelX)), ("y", toString (by0 + 16)),
                  ("font-size","10"), ("fill","#9fb0e0")]
          s!"score = {SemCID.toHex (score k)}" ]
    let bars := hs.zipIdx.map (fun (v, j) =>
      let frac := Float.ofNat v / Float.ofNat digestSpace
      let wTarget := frac * barMax
      let ry : Int := by0 + 26 + Int.ofNat j * 26
      let beg := s!"{2000 + (i * 4 + j) * 160}ms"
      let col := saltColor j
      Svg.raw <|
        s!"<g>" ++
        s!"<rect x=\"{panelX}\" y=\"{ry}\" width=\"{fc barMax}\" height=\"18\" rx=\"4\" " ++
        s!"fill=\"#10142c\" stroke=\"#2a335f\"/>" ++
        s!"<rect x=\"{panelX}\" y=\"{ry}\" width=\"0\" height=\"18\" rx=\"4\" fill=\"{col}\" opacity=\"0.92\">" ++
        s!"<animate attributeName=\"width\" from=\"0\" to=\"{fc wTarget}\" begin=\"{beg}\" " ++
        s!"dur=\"0.7s\" fill=\"freeze\" calcMode=\"spline\" keySplines=\"0.3 0 0.2 1\" keyTimes=\"0;1\"/></rect>" ++
        s!"<text x=\"{panelX + 8}\" y=\"{ry + 14}\" font-size=\"10\" font-weight=\"700\" fill=\"#070812\">" ++
        s!"h{j} = {SemCID.toHex v}</text></g>")
    header ++ bars)

/-! ## Assembling the film -/

/-- Build the complete animated conformal-field SVG for the reflected `items`. -/
def buildFilm (items : List (Name × Nat)) : String :=
  let w : Nat := 1180
  let h : Nat := 800
  let doc := document w h
    ([ Svg.raw
         ("<defs>" ++
          "<radialGradient id=\"bgd\" cx=\"40%\" cy=\"20%\" r=\"120%\">" ++
          "<stop offset=\"0%\" stop-color=\"#1a1f3c\"/><stop offset=\"100%\" stop-color=\"#070812\"/></radialGradient>" ++
          "<marker id=\"ahd\" markerWidth=\"6\" markerHeight=\"6\" refX=\"5\" refY=\"3\" orient=\"auto\">" ++
          "<path d=\"M0,0 L6,3 L0,6 Z\" fill=\"#9fb0e0\"/></marker>" ++
          "<filter id=\"glow\" x=\"-200%\" y=\"-200%\" width=\"500%\" height=\"500%\">" ++
          "<feGaussianBlur stdDeviation=\"4\" result=\"b\"/><feMerge>" ++
          "<feMergeNode in=\"b\"/><feMergeNode in=\"SourceGraphic\"/></feMerge></filter></defs>"),
       rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#bgd)" "none" [],
       -- title bar
       rect 20 18 (Int.ofNat w - 40) 56 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x","40"),("y","44"),("font-size","22"),("font-weight","800"),
                 ("fill","#ffd700")] "CONFORMAL FIELD — multi-hash scores & the arrow permutation, animated",
       Svg.text [("x","40"),("y","65"),("font-size","12"),("fill","#9fb0e0")]
         s!"affine arrows x ↦ ({aCoef}·x + {bCoef}) mod {gridP} form a permutation (arrow_bijective); coordinates computed natively by Lean",
       -- Movement 1 + 2 (the ring lives in one raw layer)
       Svg.text [("x","40"),("y","100"),("font-size","13"),("font-weight","700"),
                 ("fill","#2bd0c0")] "1 · the conformal arrow field draws itself in — one out-arrow / one in-arrow per node",
       Svg.raw arrowsSvg,
       Svg.raw nodesSvg,
       Svg.text [("x","40"),("y","760"),("font-size","12"),("fill","#9fb0e0")]
         "2 · a token rides the permutation orbit · the gold node is the affine fixed point",
       Svg.raw tokenSvg,
       -- Movement 3 header
       Svg.text [("x", toString panelX),("y","100"),("font-size","13"),("font-weight","700"),
                 ("fill","#2bd0c0")] "3 · multi-hash bars (each < 2^24)" ]
     ++ multiHashPanel items
     ++ [ Svg.text [("x","20"),("y", toString (Int.ofNat h - 14)),("font-size","11"),
                    ("fill","#5a6790")]
            "generated natively by Lean · faithful arrow/multiHash/score projections · #writeconformalanim" ])
  render doc

/-- Reflect the featured declarations into `(name, fingerprint)` pairs. -/
def gatherFeatured : CommandElabM (List (Name × Nat)) := do
  let env ← getEnv
  let mut out : List (Name × Nat) := []
  for nm in featured do
    match env.find? nm with
    | some info => out := (nm, fullFingerprint nm info) :: out
    | none => pure ()
  return out.reverse

/-! ## Commands -/

/-- `#conformalfilm` builds the animated conformal-field film and reports its size. -/
syntax (name := conformalfilmCmd) "#conformalfilm" : command

@[command_elab conformalfilmCmd]
def elabConformalfilm : CommandElab := fun _ => do
  let items ← gatherFeatured
  let svg := buildFilm items
  logInfo s!"[Conformal Field Film] animated {gridP} arrows + {items.length} multi-hash bars into a {svg.length}-byte SVG."

/-- `#writeconformalanim "path"` builds the film and writes the animated SVG to `path`. -/
syntax (name := writeconformalanimCmd) "#writeconformalanim " str : command

@[command_elab writeconformalanimCmd]
def elabWriteconformalanim : CommandElab := fun stx => do
  match stx with
  | `(#writeconformalanim $p:str) => do
    let path := p.getString
    let items ← gatherFeatured
    let svg := buildFilm items
    IO.FS.writeFile path svg
    logInfo s!"[Conformal Field Film] wrote {svg.length} bytes ({items.length} declarations) to {path}"
  | _ => throwError "ill-formed #writeconformalanim command"

/-! ## Test suite -/

#conformalfilm
#writeconformalanim "atlas_conformal_anim.svg"

end ConformalFieldSVG

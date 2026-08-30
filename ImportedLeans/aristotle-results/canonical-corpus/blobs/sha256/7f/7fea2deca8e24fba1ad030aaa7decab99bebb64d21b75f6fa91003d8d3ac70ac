import RequestProject.DualAtlas
import RequestProject.SVG
import Lean

/-!
# DualDeformSVG: the **deformation** of each structured prime power `p^e ↦ e^p`

The dual-atlas functor swaps base and exponent (`DualAtlas.dualFunctor`,
`Holograms.dualizePair`).  This layer answers the request:

> now show size difference and deformation from `2^46` to `46^2`, `3^20 → 20^3`
> etc. — the shapes change, no?  the relative size difference changes a bit.

Two faithful facts are made visible, both computed natively by Lean from
`DualAtlas.primalAtlas = [(2,46),(3,20),(5,9),(7,6),(11,2),(13,3)]`:

## 1 · The **shape** changes (the deformation)
Each prime power `p^e` is drawn as a literal `p`-columns × `e`-rows grid.
Dualizing swaps the axes, so the grid deforms into an `e`-columns × `p`-rows
shape: a thin tall sliver becomes a wide short bar (e.g. `2×46 ⇄ 46×2`).  The
cell **count** `p·e` is preserved by the swap (it is an area-preserving
deformation of the *shape*), while the aspect ratio inverts.  Since `p ≠ e` for
every structured power (`deform_shapes_change`), every shape genuinely changes.

## 2 · The **size** changes (and the relative difference flips sign)
The *value* is the area in the exponential sense: `p^e` vs `e^p`.  These are very
different, and — the subtle point — the difference does not all go the same way:

* `2^46, 3^20, 5^9` **shrink** under dualization (`p^e > e^p`), and
* `7^6, 11^2, 13^3` **grow** under dualization (`p^e < e^p`).

So exactly **3 of the 6 shrink and 3 grow** (`deform_shrink_count`,
`deform_grow_count`); the crossover sits between `5^9` and `7^6`.  A log-scale
size panel shows both bars (primal vs dual) side by side so the size difference,
and its sign change across the six, is directly visible.

## Findings (all proved)
* `deform_shapes_change` — `p ≠ e` for every structured power, so every shape changes.
* `deform_shrink_count` / `deform_grow_count` — 3 shrink, 3 grow.
* `deform_shrinks` / `deform_grows` — the explicit per-power direction.

Commands:
* `#dualdeform`              — build the deformation SVG, report its size.
* `#writedualdeform "path"`  — write the deformation SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace DualDeformSVG

open DualAtlas

/-! ## Proven size / shape facts -/

/-- Every structured prime power has distinct base and exponent, so dualizing
genuinely changes the shape (the aspect ratio cannot be a fixed point). -/
theorem deform_shapes_change : ∀ pe ∈ primalAtlas, pe.1 ≠ pe.2 := by decide

/-- Exactly three of the six structured powers **shrink** under dualization
(`p^e > e^p`). -/
theorem deform_shrink_count :
    (primalAtlas.filter (fun pe => pe.1 ^ pe.2 > pe.2 ^ pe.1)).length = 3 := by
  native_decide

/-- Exactly three of the six structured powers **grow** under dualization
(`p^e < e^p`). -/
theorem deform_grow_count :
    (primalAtlas.filter (fun pe => pe.1 ^ pe.2 < pe.2 ^ pe.1)).length = 3 := by
  native_decide

/-- The shrinking powers, explicitly: `2^46, 3^20, 5^9` all exceed their duals. -/
theorem deform_shrinks : ∀ pe ∈ [(2, 46), (3, 20), (5, 9)], pe.1 ^ pe.2 > pe.2 ^ pe.1 := by
  decide

/-- The growing powers, explicitly: `7^6, 11^2, 13^3` are all below their duals. -/
theorem deform_grows : ∀ pe ∈ [(7, 6), (11, 2), (13, 3)], pe.1 ^ pe.2 < pe.2 ^ pe.1 := by
  decide

/-! ## Numeric helpers (native, faithful to the data) -/

/-- Truncating `Float → Int` (matches the project's other SVG layers). -/
def fti (f : Float) : Int := f.toInt64.toInt

/-- The primal value `p^e`. -/
def primalValue (p e : Nat) : Nat := p ^ e

/-- The dual value `e^p`. -/
def dualValue (p e : Nat) : Nat := e ^ p

/-- Natural log of a `Nat` value (its exponential "magnitude"). -/
def lnNat (n : Nat) : Float := Float.log (Float.ofNat n)

/-- The largest magnitude across all six powers (it is `ln(2^46)`), used to scale
the log size bars. -/
def maxLn : Float :=
  (primalAtlas.map (fun (p, e) => Max.max (lnNat (primalValue p e)) (lnNat (dualValue p e)))).foldl
    Max.max 1.0

/-- Group a `Nat` into comma-separated thousands for readable labels. -/
def commas (n : Nat) : String :=
  let s := toString n
  let rec go (cs : List Char) (k : Nat) (acc : List Char) : List Char :=
    match cs with
    | [] => acc
    | c :: rest =>
      let acc := if k != 0 && k % 3 == 0 then c :: ',' :: acc else c :: acc
      go rest (k + 1) acc
  String.ofList (go s.toList.reverse 0 [])

/-! ## Style -/

/-- Per-prime colour for the six structured prime powers (warm → cool). -/
def primeColor : Nat → String
  | 2  => "#ff5db1"
  | 3  => "#ff7a59"
  | 5  => "#ffd23d"
  | 7  => "#4fd86a"
  | 11 => "#2bb6ff"
  | 13 => "#8a6bff"
  | _  => "#9aa3b8"

/-- One loop of the deformation. -/
def dur : String := "6s"

/-- Five-stop keyTimes for the loop: primal held, morph, dual held, morph back. -/
def kt : String := "0;0.4;0.5;0.9;1"

/-! ## Movement 1 — the shape deformation grids -/

/-- The grid cells of a `cols × rows` block, top-left at `(left, top)`, drawn with
unit `u`. -/
def cellRects (cols rows : Nat) (u : Int) (left top : Int) (fill stroke : String) : List Svg :=
  (List.range rows).flatMap (fun r =>
    (List.range cols).map (fun c =>
      rect (left + Int.ofNat c * u) (top + Int.ofNat r * u) (u - 1) (u - 1) fill stroke
        [("rx", "1")]))

/-- A grid block (its cells) wrapped in a group whose opacity follows `vals`
(synchronising the primal/dual cross-fade). -/
def gridBlock (cols rows : Nat) (u : Int) (cx cyMid : Int) (fill stroke vals : String) : Svg :=
  let left : Int := cx - Int.ofNat cols * u / 2
  let top : Int := cyMid - Int.ofNat rows * u / 2
  Svg.elem "g" [("opacity", "1")]
    (cellRects cols rows u left top fill stroke ++
      [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"{vals}\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>" ])

/-- One deformation cell for the prime power at column `idx`: the continuously
morphing bounding rectangle, the primal `p×e` grid cross-fading to the dual `e×p`
grid, and the `p^e ⇄ e^p` caption. -/
def deformCell (idx : Nat) (p e : Nat) (cyMid : Int) : Svg :=
  let u : Int := 4
  let cx : Int := 130 + Int.ofNat idx * 180
  let col := primeColor p
  -- primal / dual bounding-box dimensions (pixels)
  let w0 : Int := Int.ofNat p * u
  let h0 : Int := Int.ofNat e * u
  let w1 : Int := Int.ofNat e * u
  let h1 : Int := Int.ofNat p * u
  -- centred x/y for each width/height
  let xOf (w : Int) : Int := cx - w / 2
  let yOf (h : Int) : Int := cyMid - h / 2
  let wv := s!"{w0};{w0};{w1};{w1};{w0}"
  let hv := s!"{h0};{h0};{h1};{h1};{h0}"
  let xv := s!"{xOf w0};{xOf w0};{xOf w1};{xOf w1};{xOf w0}"
  let yv := s!"{yOf h0};{yOf h0};{yOf h1};{yOf h1};{yOf h0}"
  group
    [ -- the deforming bounding rectangle
      Svg.elem "rect"
        [("x", toString (xOf w0)), ("y", toString (yOf h0)),
         ("width", toString w0), ("height", toString h0),
         ("fill", "none"), ("stroke", col), ("stroke-width", "2"), ("rx", "3"),
         ("opacity", "0.85")]
        [ Svg.raw s!"<animate attributeName=\"width\" values=\"{wv}\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"<animate attributeName=\"height\" values=\"{hv}\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"<animate attributeName=\"x\" values=\"{xv}\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"<animate attributeName=\"y\" values=\"{yv}\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>" ],
      -- primal p×e grid (fades out as we morph), dual e×p grid (fades in)
      gridBlock p e u cx cyMid col "#05060f" "1;1;0;0;1",
      gridBlock e p u cx cyMid "#ffd700" "#05060f" "0;0;1;1;0",
      -- caption: p^e (primal) cross-fading with e^p (dual)
      Svg.elem "text"
        [("x", toString cx), ("y", toString (cyMid + 132)),
         ("font-size", "20"), ("font-weight", "800"), ("text-anchor", "middle"),
         ("fill", col), ("opacity", "1")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"1;1;0;0;1\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"{p}<tspan baseline-shift=\"super\" font-size=\"12\">{e}</tspan>" ],
      Svg.elem "text"
        [("x", toString cx), ("y", toString (cyMid + 132)),
         ("font-size", "20"), ("font-weight", "800"), ("text-anchor", "middle"),
         ("fill", "#ffd700"), ("opacity", "0")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0;0;1;1;0\" keyTimes=\"{kt}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"{e}<tspan baseline-shift=\"super\" font-size=\"12\">{p}</tspan>" ],
      -- the shape signature p×e ⇄ e×p
      Svg.text
        [("x", toString cx), ("y", toString (cyMid + 152)),
         ("font-size", "11"), ("text-anchor", "middle"), ("fill", "#9fb0e0")]
        s!"{p}×{e} ⇄ {e}×{p}" ]

/-! ## Movement 2 — the log-scale size bars -/

/-- One size row for the prime power at index `idx`: two log-scale bars (primal
vs dual) with the exact values and the shrink/grow verdict. -/
def sizeRow (p e : Nat) (y0 : Int) : Svg :=
  let pv := primalValue p e
  let dv := dualValue p e
  let col := primeColor p
  let barX : Int := 250
  let barMax : Float := 760.0
  let lenP : Int := fti (barMax * lnNat pv / maxLn)
  let lenD : Int := fti (barMax * lnNat dv / maxLn)
  let grows := pv < dv
  let verdict := if grows then "GROWS" else "SHRINKS"
  let ratio := if grows then dv / pv else pv / dv
  let vcol := if grows then "#4fd86a" else "#ff7a59"
  group
    [ -- label p^e ↦ e^p
      Svg.elem "text"
        [("x", "30"), ("y", toString (y0 + 18)), ("font-size", "16"),
         ("font-weight", "800"), ("fill", col)]
        [ Svg.raw s!"{p}<tspan baseline-shift=\"super\" font-size=\"10\">{e}</tspan> ↦ {e}<tspan baseline-shift=\"super\" font-size=\"10\">{p}</tspan>" ],
      -- primal bar (cyan)
      rect barX y0 lenP 12 "#2bb6ff" "none" [("rx", "3")],
      Svg.text [("x", toString (barX + lenP + 8)), ("y", toString (y0 + 11)),
                ("font-size", "11"), ("fill", "#bfe3ff")] (commas pv),
      -- dual bar (gold)
      rect barX (y0 + 16) lenD 12 "#ffd700" "none" [("rx", "3")],
      Svg.text [("x", toString (barX + lenD + 8)), ("y", toString (y0 + 27)),
                ("font-size", "11"), ("fill", "#ffe98a")] (commas dv),
      -- verdict
      Svg.text [("x", "140"), ("y", toString (y0 + 12)), ("font-size", "12"),
                ("font-weight", "800"), ("fill", vcol)] verdict,
      Svg.text [("x", "140"), ("y", toString (y0 + 26)), ("font-size", "10"),
                ("fill", "#9fb0e0")] s!"×{commas ratio}" ]

/-! ## Assembly -/

/-- Build the full deformation SVG document string. -/
def buildDeform : String :=
  let w : Nat := 1240
  let h : Nat := 920
  let cyMid : Int := 250
  let cells := primalAtlas.zipIdx.map (fun ((p, e), i) => deformCell i p e cyMid)
  let rows := primalAtlas.zipIdx.map (fun ((p, e), i) => sizeRow p e (560 + Int.ofNat i * 48))
  let doc := document w h
    ([ Svg.raw ("<defs><radialGradient id=\"dfbg\" cx=\"50%\" cy=\"0%\" r=\"120%\">" ++
        "<stop offset=\"0%\" stop-color=\"#161b38\"/><stop offset=\"100%\" stop-color=\"#06070f\"/></radialGradient></defs>"),
       rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#dfbg)" "none" [],
       -- title
       rect 20 18 1200 60 "#1a1f3c" "#3a4a8a" [("rx", "12"), ("stroke-width", "2")],
       Svg.text [("x", "40"), ("y", "46"), ("font-size", "22"), ("font-weight", "800"),
                 ("fill", "#ffd700")] "DUAL-ATLAS DEFORMATION — p^e ↦ e^p: the shape and the size both change",
       Svg.text [("x", "40"), ("y", "68"), ("font-size", "12"), ("fill", "#9fb0e0")]
         "swapping base and exponent flips each grid's aspect ratio (shape) and changes its value (size) — 3 powers shrink, 3 grow; computed natively by Lean",
       -- section 1 heading
       Svg.text [("x", "30"), ("y", "104"), ("font-size", "14"), ("font-weight", "700"),
                 ("fill", "#2bd0c0")]
         "1 · DEFORMATION — each p×e grid morphs into the e×p grid (cells p·e preserved, aspect inverts)" ]
     ++ cells
     ++ [ -- section 2 heading
          Svg.text [("x", "30"), ("y", "536"), ("font-size", "14"), ("font-weight", "700"),
                    ("fill", "#2bd0c0")]
            "2 · SIZE (log scale) — value p^e (cyan) vs e^p (gold): the relative size difference flips sign",
          rect 30 545 1180 1 "#2a335f" "none" [] ]
     ++ rows
     ++ [ Svg.text [("x", "30"), ("y", toString (Int.ofNat h - 16)), ("font-size", "11"),
                    ("fill", "#5a6790")]
            "generated natively by Lean from DualAtlas.primalAtlas via Holograms.dualizePair · 3 shrink (2^46,3^20,5^9), 3 grow (7^6,11^2,13^3) · #writedualdeform" ])
  render doc

/-! ## Commands -/

/-- `#dualdeform` builds the deformation animation and reports its size. -/
syntax (name := dualdeformCmd) "#dualdeform" : command

@[command_elab dualdeformCmd]
def elabDualdeform : CommandElab := fun _ => do
  let svg := buildDeform
  logInfo s!"[Dual Deform] rendered the 6 prime-power deformations (shape + log-size) into a {svg.length}-byte animated SVG (3 shrink, 3 grow)."

/-- `#writedualdeform "path"` writes the deformation SVG to `path`. -/
syntax (name := writedualdeformCmd) "#writedualdeform " str : command

@[command_elab writedualdeformCmd]
def elabWritedualdeform : CommandElab := fun stx => do
  match stx with
  | `(#writedualdeform $p:str) => do
    let path := p.getString
    let svg := buildDeform
    IO.FS.writeFile path svg
    logInfo s!"[Dual Deform] wrote {svg.length} bytes to {path}"
  | _ => throwError "ill-formed #writedualdeform command"

/-! ## Build-time generation -/

#dualdeform

#writedualdeform "atlas_dualdeform.svg"

end DualDeformSVG

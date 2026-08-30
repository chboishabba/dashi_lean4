import RequestProject.Irrep194

/-!
# QDeform: deforming the projection along the 104 q-expansions as the number of
available primes changes with each irrep combination

This layer answers the request:

> now we deform the projection along the 104 q-expansions and show what happens
> as the number of primes available changes with each irrep combination, a new
> svg.

## The construction

Each of the 104 q-expansion pages carries the coefficient `c(pi+1) = [q^{pi+1}] j`
of the McKay–Thompson series `T1 = j` (the same coefficients whose **irrep
combinations** are the monstrous-moonshine decompositions recorded in
`JExpansion`/`Moonshine`).  For page `pi` we read off the **primes available** at
that page as exactly the Monster primes dividing that coefficient:

```
availLayer pi = monsterPrimes.filter (p ∣ |c(pi+1)|).
```

This is the page's prime support — the dimensions the irrep combination at that
page actually lights up.  As `pi` runs `0 … 103` the available-prime count
`availCount pi` rises and falls (`qdeform_*` findings below).

Every project declaration is then **folded onto exactly those available primes**
via `IrrepFold.foldPos` (residue-fraction vector sum over the available
dimensions; the empty layer collapses everything to a single point on the
sphere).  Turning the 104 pages morphs each atom continuously through its
per-page locations, so we watch the **projection deform** as the number of
available primes changes.  The dependency **arrows are preserved**
(`IrrepFold.foldEdges`): each arrow's endpoints are animated in lockstep with the
two atoms it joins, so they stretch and bend through every deformation but never
detach.  A live inset graph plots `availCount` across the 104 pages with a cursor
on the current page.

## The findings (all proved by `native_decide`)

* `qdeform_max_count` — across all 104 pages the available-prime count never
  exceeds **6**.
* `qdeform_collapse` — at page 71 (`q^71`) the coefficient is coprime to every
  Monster prime, so **no primes are available** and the whole projection
  collapses to one point on the sphere (`availLayer 70 = []`).
* `qdeform_peak` — page 95 (`q^95`) hits the maximum of **6** available primes.
* `qdeform_distinct_counts` — the 104 pages realise exactly **7** distinct
  available-prime counts (the values `0 … 6`).
* `availLayer_subset` — nothing ever leaves Monster-prime space.

Commands:

* `#qdeform`              — build the deformation animation; report its size.
* `#writeqdeform "path"`  — write the deformation SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace QDeform

open Introspect IntrospectSVG DualAtlas Moonshine PrimeProjection IrrepFold

/-! ## The available primes per q-expansion page -/

/-- The number of q-expansion pages deformed through (`q¹ … q¹⁰⁴`). -/
def numQPages : Nat := 104

/-- The **primes available** at expansion page `pi`: the Monster primes dividing
the coefficient `c(pi+1) = [q^{pi+1}] j`.  This is the prime support of the
irrep combination at that page. -/
def availLayer (pi : Nat) : List Nat :=
  monsterPrimes.filter (fun p => (jCoeff (pi + 2)).natAbs % p == 0)

/-- The number of available primes at page `pi`. -/
def availCount (pi : Nat) : Nat := (availLayer pi).length

/-- Nothing ever leaves Monster-prime space: every available prime is a Monster
prime. -/
theorem availLayer_subset (pi : Nat) : ∀ p ∈ availLayer pi, p ∈ monsterPrimes :=
  fun _ h => (List.mem_filter.mp h).1

/-- **Finding.**  Across all 104 pages the available-prime count never exceeds 6. -/
theorem qdeform_max_count : ∀ pi, pi < numQPages → availCount pi ≤ 6 := by
  native_decide

/-- **Finding.**  At page 71 (`q^71`) the coefficient is coprime to every Monster
prime, so no primes are available and the projection collapses to one point. -/
theorem qdeform_collapse : availLayer 70 = [] := by native_decide

/-- **Finding.**  Page 95 (`q^95`) attains the maximum of 6 available primes. -/
theorem qdeform_peak : availCount 94 = 6 := by native_decide

/-- **Finding.**  The 104 pages realise exactly 7 distinct available-prime counts
(the values `0 … 6`). -/
theorem qdeform_distinct_counts :
    ((List.range numQPages).map availCount).eraseDups.length = 7 := by
  native_decide

/-! ## Geometry: fold each atom onto the available primes of each page -/

/-- The position of atom `h` on page `pi`: the fold of `h` onto the primes
available at that page (reusing `IrrepFold.foldPos`). -/
def qPos (h pi : Nat) : Int × Int :=
  let (x, y) := IrrepFold.foldPos h (availLayer pi)
  (IrrepFold.f2i x, IrrepFold.f2i y)

/-! ## Animation value strings -/

/-- Duration of one full 104-page deformation cycle. -/
def qDur : String := "64s"

/-- A `;`-joined value string, one entry per page, from a per-page function. -/
def joinPages (f : Nat → String) : String :=
  String.intercalate ";" ((List.range numQPages).map f)

/-- The `translate` value string for an atom: its positions over all 104 pages. -/
def qTranslate (h : Nat) : String :=
  joinPages (fun pi => let (x, y) := qPos h pi; s!"{x} {y}")

/-- One endpoint coordinate (x or y) of an atom over all 104 pages. -/
def qCoord (h : Nat) (useX : Bool) : String :=
  joinPages (fun pi => let (x, y) := qPos h pi; toString (if useX then x else y))

/-! ## Rendering: arrows, atoms -/

/-- One dependency arrow whose four endpoint coordinates are animated in lockstep
with the two atoms it joins, so it is preserved through every deformation. -/
def qArrow (atoms : List FoldAtom) (e : Nat × Nat) : Svg :=
  match atoms[e.1]?, atoms[e.2]? with
  | some a, some b =>
    let (ax, ay) := qPos a.hash 0
    let (bx, byy) := qPos b.hash 0
    Svg.elem "line"
      [("x1", toString ax), ("y1", toString ay),
       ("x2", toString bx), ("y2", toString byy),
       ("stroke", "#5566aa"), ("stroke-width", "1"), ("opacity", "0.26")]
      [ Svg.raw s!"<animate attributeName=\"x1\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoord a.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y1\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoord a.hash false}\"/>",
        Svg.raw s!"<animate attributeName=\"x2\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoord b.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y2\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoord b.hash false}\"/>" ]
  | _, _ => group []

/-- One atom: a marker translated continuously through its 104 per-page locations,
deforming as the available primes change. -/
def qMarker (a : FoldAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := qPos a.hash 0
  Svg.elem "g"
    [("transform", s!"translate({sx} {sy})")]
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · hash {a.hash} · {styleName a.style} · {a.deps.length} arrows</title>",
      circle 0 0 7 "none" glow [("opacity", "0.40"), ("filter", "url(#qglow)")],
      circle 0 0 5 fill "#05060f" [("stroke-width", "1")],
      Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"translate\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qTranslate a.hash}\"/>" ]

/-! ## Chrome: sphere frame, banner, availability graph, HUD -/

/-- A faint reference sphere: boundary circle (whose top point is the collapse
location) plus inner guides. -/
def sphereFrame : Svg :=
  group
    [ circle (IrrepFold.f2i IrrepFold.foldCx) (IrrepFold.f2i IrrepFold.foldCy)
        (IrrepFold.f2i IrrepFold.foldR) "none" "#23305f" [("stroke-width", "1"), ("opacity", "0.6")],
      circle (IrrepFold.f2i IrrepFold.foldCx) (IrrepFold.f2i IrrepFold.foldCy)
        (IrrepFold.f2i (IrrepFold.foldR * 0.66)) "none" "#1a2348" [("stroke-width", "1"), ("opacity", "0.45")],
      circle (IrrepFold.f2i IrrepFold.foldCx) (IrrepFold.f2i IrrepFold.foldCy)
        (IrrepFold.f2i (IrrepFold.foldR / 3.0)) "none" "#1a2348" [("stroke-width", "1"), ("opacity", "0.4")],
      circle (IrrepFold.f2i IrrepFold.foldCx) (IrrepFold.f2i (IrrepFold.foldCy - IrrepFold.foldR))
        4 "#ffd700" "#05060f" [("opacity", "0.8")],
      Svg.text [("x", toString (IrrepFold.f2i IrrepFold.foldCx + 10)),
                ("y", toString (IrrepFold.f2i (IrrepFold.foldCy - IrrepFold.foldR) - 8)),
                ("font-size", "12"), ("fill", "#ffd700")]
        "collapse point — pages with no available primes land here" ]

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"qbg\" cx=\"46%\" cy=\"40%\" r=\"85%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"qbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"qglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1340 86 "url(#qbanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "62"), ("font-size", "28"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "Q-DEFORM · PROJECTION DEFORMED ALONG THE 104 q-EXPANSIONS · ARROWS PRESERVED",
      Svg.text [("x", "58"), ("y", "92"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "the primes available at page n are the Monster primes dividing [q^n] j — its irrep-combination support; the count rises and falls (0 … 6) and the whole projection deforms with it" ]

/-! ### The live availability graph (inset, top-right) -/

/-- Graph box geometry. -/
def gx0 : Float := 980.0
def gy0 : Float := 130.0
def gw  : Float := 380.0
def gh  : Float := 150.0

/-- X pixel for page `pi` in the inset graph. -/
def graphX (pi : Nat) : Float :=
  gx0 + gw * Float.ofNat pi / Float.ofNat (numQPages - 1)

/-- Y pixel for an available-prime count `c` (`0 … 6`) in the inset graph. -/
def graphY (c : Nat) : Float :=
  gy0 + gh - gh * Float.ofNat c / 6.0

/-- The polyline of `availCount` across the 104 pages. -/
def availPolyline : Svg :=
  let pts := String.intercalate " "
    ((List.range numQPages).map (fun pi =>
      s!"{IrrepFold.f2i (graphX pi)},{IrrepFold.f2i (graphY (availCount pi))}"))
  Svg.elem "polyline"
    [("points", pts), ("fill", "none"), ("stroke", "#7ad9ff"),
     ("stroke-width", "2"), ("opacity", "0.9")] []

/-- The cursor dot gliding along the availability polyline on the current page. -/
def availCursor : Svg :=
  let xs := joinPages (fun pi => toString (IrrepFold.f2i (graphX pi)))
  let ys := joinPages (fun pi => toString (IrrepFold.f2i (graphY (availCount pi))))
  Svg.elem "circle"
    [("cx", toString (IrrepFold.f2i (graphX 0))),
     ("cy", toString (IrrepFold.f2i (graphY (availCount 0)))),
     ("r", "5"), ("fill", "#ffd700"), ("stroke", "#05060f")]
    [ Svg.raw s!"<animate attributeName=\"cx\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{xs}\"/>",
      Svg.raw s!"<animate attributeName=\"cy\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{ys}\"/>" ]

/-- The availability-graph panel: frame, axis labels, polyline, cursor. -/
def availGraph : Svg :=
  group
    [ rect (IrrepFold.f2i gx0 - 20) (IrrepFold.f2i gy0 - 28)
        (IrrepFold.f2i gw + 40) (IrrepFold.f2i gh + 56) "#0b1430" "#2a7fff"
        [("rx", "10"), ("stroke-width", "1"), ("opacity", "0.92")],
      Svg.text [("x", toString (IrrepFold.f2i gx0 - 6)), ("y", toString (IrrepFold.f2i gy0 - 8)),
                ("font-size", "13"), ("font-weight", "700"), ("fill", "#7ad9ff")]
        "available primes per q-expansion page (0 … 6)",
      Svg.elem "line"
        [("x1", toString (IrrepFold.f2i gx0)), ("y1", toString (IrrepFold.f2i (gy0 + gh))),
         ("x2", toString (IrrepFold.f2i (gx0 + gw))), ("y2", toString (IrrepFold.f2i (gy0 + gh))),
         ("stroke", "#3a4a8a"), ("stroke-width", "1")] [],
      availPolyline,
      availCursor,
      Svg.text [("x", toString (IrrepFold.f2i gx0 - 6)), ("y", toString (IrrepFold.f2i (gy0 + gh) + 18)),
                ("font-size", "11"), ("fill", "#9fb0e0")]
        "q^1                                                   q^104" ]

/-! ### Per-page HUD -/

/-- One HUD frame for expansion page `pi`, visible only during its 1/104 slot. -/
def qHud (pi : Nat) : Svg :=
  let vis := joinPages (fun q => if q == pi then "1" else "0")
  let ps := availLayer pi
  let tuple :=
    if ps.isEmpty then "(none — full collapse to the sphere point)"
    else String.intercalate "·" (ps.map toString)
  let key := Moonshine.jCoeff (pi + 2)
  let keyS :=
    let s := toString key
    if s.length ≤ 20 then s else (s.take 14).toString ++ "… (" ++ toString s.length ++ " digits)"
  group
    [ Svg.text [("x", "40"), ("y", "1000"), ("font-size", "22"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        s!"q-EXPANSION {pi + 1} / {numQPages}",
      Svg.text [("x", "300"), ("y", "1000"), ("font-size", "16"), ("fill", "#9fb0e0")]
        s!"[q^{pi + 1}] j = {keyS}",
      Svg.text [("x", "40"), ("y", "1024"), ("font-size", "15"), ("font-weight", "700"),
                ("fill", "#7ad9ff")]
        s!"available primes ({ps.length}):  {tuple}",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]

/-! ## Assembly -/

/-- Build the full q-deformation SVG document string. -/
def buildQDeform (atoms : List FoldAtom) : String :=
  let edges := foldEdges atoms
  let arrows := group (edges.map (qArrow atoms))
  let markers := group (atoms.map qMarker)
  let huds := group ((List.range numQPages).map qHud)
  let doc := document 1400 1040
    [ Svg.raw defsRaw,
      rect 0 0 1400 1040 "url(#qbg)" "none" [],
      banner,
      sphereFrame,
      arrows,
      markers,
      availGraph,
      huds,
      Svg.text [("x", "40"), ("y", "1010"), ("font-size", "11"), ("fill", "#5a6790")]
        s!"generated natively by Lean · {atoms.length} decls · {edges.length} arrows · available primes(n) = Monster primes ∣ [q^n] j · folded via Σᵢ (h mod pᵢ)/pᵢ · #writeqdeform" ]
  render doc

/-! ## Commands -/

/-- `#qdeform` builds the deformation animation and reports its size. -/
syntax (name := qdeformCmd) "#qdeform" : command

@[command_elab qdeformCmd]
def elabQdeform : CommandElab := fun _ => do
  let atoms ← projectFoldAtoms
  let edges := foldEdges atoms
  let svg := buildQDeform atoms
  logInfo s!"[Q-Deform] deformed {atoms.length} decls (with {edges.length} preserved arrows) along {numQPages} q-expansions; available-prime count ranges 0 … {((List.range numQPages).map availCount).foldl Nat.max 0} → {svg.length}-byte animated SVG."

/-- `#writeqdeform "path"` writes the deformation SVG to `path`. -/
syntax (name := writeqdeformCmd) "#writeqdeform " str : command

@[command_elab writeqdeformCmd]
def elabWriteqdeform : CommandElab := fun stx => do
  match stx with
  | `(#writeqdeform $p:str) => do
    let path := p.getString
    let atoms ← projectFoldAtoms
    let edges := foldEdges atoms
    let svg := buildQDeform atoms
    IO.FS.writeFile path svg
    logInfo s!"[Q-Deform] wrote {svg.length} bytes ({atoms.length} decls, {edges.length} arrows, {numQPages} q-expansions) to {path}"
  | _ => throwError "ill-formed #writeqdeform command"

/-! ## Build-time generation -/

#qdeform

#writeqdeform "atlas_qdeform.svg"

end QDeform

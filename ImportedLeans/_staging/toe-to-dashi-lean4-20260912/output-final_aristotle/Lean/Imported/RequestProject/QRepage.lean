import RequestProject.QDeform

/-!
# QRepage: re-paging the q-expansion deformation to get different views

This layer answers the follow-up request:

> can we change the paging to get different views? can you switch it up?

## What "paging" means here

In `QDeform` the animation is a flip-book of **pages**.  Page `pi` reads one
q-expansion coefficient of `j` and draws one dot per *available Monster prime*
(a Monster prime dividing that coefficient); the picture **collapses to a single
point** on a page whose coefficient is coprime to all 15 Monster primes.

The only thing that ties a *page number* to a *coefficient* is the **paging
function** `coeffIdx : Nat → Nat`, where page `pi` reads `jCoeff (coeffIdx pi)`.
`QDeform` hard-wires `coeffIdx pi = pi + 2` (so page `pi` reads
`c(pi+1) = [q^{pi+1}] j`, and the collapse lands on page 70).

Here we make the paging a **parameter**, so we can re-page the same data into
different views and watch the collapse move — or disappear.

## The catch (a proved fact, not a slogan)

Across the entire usable coefficient window (`jCoeff 2 … jCoeff 119`) there is
**exactly one** full-collapse coefficient: `jCoeff 72 = c(71)`
(`QShapes`/`QDeform` record the same uniqueness).  So re-paging cannot create or
destroy collapses arbitrarily — it can only relocate the single one, and a paging
that never lands on index 72 shows **no collapse at all**.

## The views (all collapse pages proved by `native_decide`)

| view | paging `coeffIdx pi` | pages | collapse page | note |
|------|----------------------|-------|---------------|------|
| base    | `pi + 2`    | 0…103 | **70** | the original `QDeform` view |
| late    | `pi + 16`   | 0…103 | **56** | start the window 14 coefficients later |
| reverse | `119 - pi`  | 0…117 | **47** | play the coefficients backwards |
| even    | `2·pi + 2`  | 0…58  | **35** | only the even-power coefficients |
| odd     | `2·pi + 3`  | 0…58  | *none* | only odd powers — index 72 is even, so it is **never read**, and the collapse vanishes |

Every view keeps the dependency arrows attached to their atoms, exactly as in
`QDeform`.

Commands:

* `#repage_all`                      — report all views and their collapse pages.
* `#writerepage_late "path"`         — write the *late* view.
* `#writerepage_reverse "path"`      — write the *reverse* view.
* `#writerepage_even "path"`         — write the *even* view.
* `#writerepage_odd "path"`          — write the *odd* (no-collapse) view.
-/

open Lean Meta Elab Command SVG

namespace QRepage

open Introspect IntrospectSVG DualAtlas Moonshine PrimeProjection IrrepFold

/-! ## The paging-parameterised availability -/

/-- The **primes available** at page `pi` under paging `coeffIdx`: the Monster
primes dividing `jCoeff (coeffIdx pi)`. -/
def availLayerVia (coeffIdx : Nat → Nat) (pi : Nat) : List Nat :=
  monsterPrimes.filter (fun p => (jCoeff (coeffIdx pi)).natAbs % p == 0)

/-- The number of available primes at page `pi` under paging `coeffIdx`. -/
def availCountVia (coeffIdx : Nat → Nat) (pi : Nat) : Nat :=
  (availLayerVia coeffIdx pi).length

/-! ## The four re-pagings -/

/-- *Late* view: start the window 14 coefficients later. -/
def coeffLate (pi : Nat) : Nat := pi + 16
/-- *Reverse* view: play the coefficient window backwards. -/
def coeffReverse (pi : Nat) : Nat := 119 - pi
/-- *Even* view: read only the even-power coefficients. -/
def coeffEven (pi : Nat) : Nat := 2 * pi + 2
/-- *Odd* view: read only the odd-power coefficients. -/
def coeffOdd (pi : Nat) : Nat := 2 * pi + 3

/-- Number of pages in each view. -/
def pagesLate : Nat := 104
def pagesReverse : Nat := 118
def pagesEven : Nat := 59
def pagesOdd : Nat := 59

/-! ## Findings: where each view collapses (all `native_decide`) -/

/-- The *base* paging (`pi+2`) collapses at page 70 — recovering the original
`QDeform` collapse, re-derived through the parameterised availability. -/
theorem repage_base_collapse : availCountVia (· + 2) 70 = 0 := by native_decide

/-- The *late* view collapses at page 56. -/
theorem repage_late_collapse : availCountVia coeffLate 56 = 0 := by native_decide

/-- …and page 56 is the *only* collapse of the late view. -/
theorem repage_late_unique :
    (List.range pagesLate).filter (fun pi => availCountVia coeffLate pi == 0) = [56] := by
  native_decide

/-- The *reverse* view collapses at page 47. -/
theorem repage_reverse_collapse : availCountVia coeffReverse 47 = 0 := by native_decide

/-- …and page 47 is the *only* collapse of the reverse view. -/
theorem repage_reverse_unique :
    (List.range pagesReverse).filter (fun pi => availCountVia coeffReverse pi == 0) = [47] := by
  native_decide

/-- The *even* view collapses at page 35. -/
theorem repage_even_collapse : availCountVia coeffEven 35 = 0 := by native_decide

/-- …and page 35 is the *only* collapse of the even view. -/
theorem repage_even_unique :
    (List.range pagesEven).filter (fun pi => availCountVia coeffEven pi == 0) = [35] := by
  native_decide

/-- The *odd* view has **no collapse at all**: the unique collapse coefficient
`jCoeff 72 = c(71)` is even, so an odd-only paging never reads it. -/
theorem repage_odd_nocollapse :
    ∀ pi, pi < pagesOdd → availCountVia coeffOdd pi ≠ 0 := by native_decide

/-- Equivalently, the odd view's collapse list is empty. -/
theorem repage_odd_unique :
    (List.range pagesOdd).filter (fun pi => availCountVia coeffOdd pi == 0) = [] := by
  native_decide

/-- Every view still never exceeds 6 available primes on any page. -/
theorem repage_max_count :
    (∀ pi, pi < pagesLate → availCountVia coeffLate pi ≤ 6) ∧
    (∀ pi, pi < pagesReverse → availCountVia coeffReverse pi ≤ 6) ∧
    (∀ pi, pi < pagesEven → availCountVia coeffEven pi ≤ 6) ∧
    (∀ pi, pi < pagesOdd → availCountVia coeffOdd pi ≤ 6) := by
  native_decide

/-! ## Geometry: fold each atom onto the available primes of each page -/

/-- The position of atom `h` on page `pi` under paging `coeffIdx`. -/
def qPosVia (coeffIdx : Nat → Nat) (h pi : Nat) : Int × Int :=
  let (x, y) := IrrepFold.foldPos h (availLayerVia coeffIdx pi)
  (IrrepFold.f2i x, IrrepFold.f2i y)

/-- Duration of one full deformation cycle. -/
def qDur : String := "64s"

/-- A `;`-joined value string with one entry per page. -/
def joinPagesN (numPages : Nat) (f : Nat → String) : String :=
  String.intercalate ";" ((List.range numPages).map f)

/-- The `translate` value string for an atom over all pages. -/
def qTranslateVia (numPages : Nat) (coeffIdx : Nat → Nat) (h : Nat) : String :=
  joinPagesN numPages (fun pi => let (x, y) := qPosVia coeffIdx h pi; s!"{x} {y}")

/-- One endpoint coordinate (x or y) of an atom over all pages. -/
def qCoordVia (numPages : Nat) (coeffIdx : Nat → Nat) (h : Nat) (useX : Bool) : String :=
  joinPagesN numPages (fun pi => let (x, y) := qPosVia coeffIdx h pi; toString (if useX then x else y))

/-! ## Rendering: arrows, atoms, HUD -/

/-- One dependency arrow, animated in lockstep with the two atoms it joins. -/
def qArrowVia (numPages : Nat) (coeffIdx : Nat → Nat) (atoms : List FoldAtom)
    (e : Nat × Nat) : Svg :=
  match atoms[e.1]?, atoms[e.2]? with
  | some a, some b =>
    let (ax, ay) := qPosVia coeffIdx a.hash 0
    let (bx, byy) := qPosVia coeffIdx b.hash 0
    Svg.elem "line"
      [("x1", toString ax), ("y1", toString ay),
       ("x2", toString bx), ("y2", toString byy),
       ("stroke", "#5566aa"), ("stroke-width", "1"), ("opacity", "0.26")]
      [ Svg.raw s!"<animate attributeName=\"x1\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoordVia numPages coeffIdx a.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y1\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoordVia numPages coeffIdx a.hash false}\"/>",
        Svg.raw s!"<animate attributeName=\"x2\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoordVia numPages coeffIdx b.hash true}\"/>",
        Svg.raw s!"<animate attributeName=\"y2\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qCoordVia numPages coeffIdx b.hash false}\"/>" ]
  | _, _ => group []

/-- One atom marker translated continuously through its per-page locations. -/
def qMarkerVia (numPages : Nat) (coeffIdx : Nat → Nat) (a : FoldAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := qPosVia coeffIdx a.hash 0
  Svg.elem "g"
    [("transform", s!"translate({sx} {sy})")]
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · hash {a.hash} · {styleName a.style} · {a.deps.length} arrows</title>",
      circle 0 0 7 "none" glow [("opacity", "0.40"), ("filter", "url(#qglow)")],
      circle 0 0 5 fill "#05060f" [("stroke-width", "1")],
      Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"translate\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{qTranslateVia numPages coeffIdx a.hash}\"/>" ]

/-- A faint reference sphere whose top point is the collapse location. -/
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

/-- The banner, parameterised by this view's title and subtitle. -/
def banner (title subtitle : String) : Svg :=
  group
    [ rect 30 22 1340 86 "url(#qbanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "62"), ("font-size", "26"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        title,
      Svg.text [("x", "58"), ("y", "92"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        subtitle ]

/-! ### The live availability graph (inset, top-right) -/

def gx0 : Float := 980.0
def gy0 : Float := 130.0
def gw  : Float := 380.0
def gh  : Float := 150.0

def graphX (numPages pi : Nat) : Float :=
  gx0 + gw * Float.ofNat pi / Float.ofNat (numPages - 1)

def graphY (c : Nat) : Float :=
  gy0 + gh - gh * Float.ofNat c / 6.0

/-- The polyline of `availCountVia` across the pages of this view. -/
def availPolyline (numPages : Nat) (coeffIdx : Nat → Nat) : Svg :=
  let pts := String.intercalate " "
    ((List.range numPages).map (fun pi =>
      s!"{IrrepFold.f2i (graphX numPages pi)},{IrrepFold.f2i (graphY (availCountVia coeffIdx pi))}"))
  Svg.elem "polyline"
    [("points", pts), ("fill", "none"), ("stroke", "#7ad9ff"),
     ("stroke-width", "2"), ("opacity", "0.9")] []

/-- The cursor dot gliding along the availability polyline. -/
def availCursor (numPages : Nat) (coeffIdx : Nat → Nat) : Svg :=
  let xs := joinPagesN numPages (fun pi => toString (IrrepFold.f2i (graphX numPages pi)))
  let ys := joinPagesN numPages (fun pi => toString (IrrepFold.f2i (graphY (availCountVia coeffIdx pi))))
  Svg.elem "circle"
    [("cx", toString (IrrepFold.f2i (graphX numPages 0))),
     ("cy", toString (IrrepFold.f2i (graphY (availCountVia coeffIdx 0)))),
     ("r", "5"), ("fill", "#ffd700"), ("stroke", "#05060f")]
    [ Svg.raw s!"<animate attributeName=\"cx\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{xs}\"/>",
      Svg.raw s!"<animate attributeName=\"cy\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{ys}\"/>" ]

def availGraph (numPages : Nat) (coeffIdx : Nat → Nat) (xlabel : String) : Svg :=
  group
    [ rect (IrrepFold.f2i gx0 - 20) (IrrepFold.f2i gy0 - 28)
        (IrrepFold.f2i gw + 40) (IrrepFold.f2i gh + 56) "#0b1430" "#2a7fff"
        [("rx", "10"), ("stroke-width", "1"), ("opacity", "0.92")],
      Svg.text [("x", toString (IrrepFold.f2i gx0 - 6)), ("y", toString (IrrepFold.f2i gy0 - 8)),
                ("font-size", "13"), ("font-weight", "700"), ("fill", "#7ad9ff")]
        "available primes per page (0 … 6)",
      Svg.elem "line"
        [("x1", toString (IrrepFold.f2i gx0)), ("y1", toString (IrrepFold.f2i (gy0 + gh))),
         ("x2", toString (IrrepFold.f2i (gx0 + gw))), ("y2", toString (IrrepFold.f2i (gy0 + gh))),
         ("stroke", "#3a4a8a"), ("stroke-width", "1")] [],
      availPolyline numPages coeffIdx,
      availCursor numPages coeffIdx,
      Svg.text [("x", toString (IrrepFold.f2i gx0 - 6)), ("y", toString (IrrepFold.f2i (gy0 + gh) + 18)),
                ("font-size", "11"), ("fill", "#9fb0e0")]
        xlabel ]

/-! ### Per-page HUD -/

def qHud (numPages : Nat) (coeffIdx : Nat → Nat) (pi : Nat) : Svg :=
  let vis := joinPagesN numPages (fun q => if q == pi then "1" else "0")
  let idx := coeffIdx pi
  let ps := availLayerVia coeffIdx pi
  let tuple :=
    if ps.isEmpty then "(none — full collapse to the sphere point)"
    else String.intercalate "·" (ps.map toString)
  let key := Moonshine.jCoeff idx
  let keyS :=
    let s := toString key
    if s.length ≤ 20 then s else (s.take 14).toString ++ "… (" ++ toString s.length ++ " digits)"
  group
    [ Svg.text [("x", "40"), ("y", "1000"), ("font-size", "22"), ("font-weight", "800"),
                ("fill", "#ffd700")]
        s!"PAGE {pi + 1} / {numPages}",
      Svg.text [("x", "300"), ("y", "1000"), ("font-size", "16"), ("fill", "#9fb0e0")]
        s!"[q^{idx - 1}] j = {keyS}",
      Svg.text [("x", "40"), ("y", "1024"), ("font-size", "15"), ("font-weight", "700"),
                ("fill", "#7ad9ff")]
        s!"available primes ({ps.length}):  {tuple}",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"{qDur}\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]

/-! ## Assembly -/

/-- Build a re-paged deformation SVG for a given view. -/
def buildRepage (atoms : List FoldAtom) (numPages : Nat) (coeffIdx : Nat → Nat)
    (title subtitle xlabel : String) : String :=
  let edges := foldEdges atoms
  let arrows := group (edges.map (qArrowVia numPages coeffIdx atoms))
  let markers := group (atoms.map (qMarkerVia numPages coeffIdx))
  let huds := group ((List.range numPages).map (qHud numPages coeffIdx))
  let doc := document 1400 1040
    [ Svg.raw defsRaw,
      rect 0 0 1400 1040 "url(#qbg)" "none" [],
      banner title subtitle,
      sphereFrame,
      arrows,
      markers,
      availGraph numPages coeffIdx xlabel,
      huds,
      Svg.text [("x", "40"), ("y", "1010"), ("font-size", "11"), ("fill", "#5a6790")]
        s!"generated natively by Lean · {atoms.length} decls · {edges.length} arrows · re-paged via coeffIdx · folded via Σᵢ (h mod pᵢ)/pᵢ" ]
  render doc

/-! ## Commands -/

/-- `#repage_all` reports every view and its collapse page. -/
syntax (name := repageAllCmd) "#repage_all" : command

@[command_elab repageAllCmd]
def elabRepageAll : CommandElab := fun _ => do
  let f (np : Nat) (ci : Nat → Nat) : List Nat :=
    (List.range np).filter (fun pi => availCountVia ci pi == 0)
  logInfo s!"[Q-Repage] views and collapse pages:\n  base    (pi+2,   {QDeform.numQPages} pages): collapse {f 104 (· + 2)}\n  late    (pi+16,  {pagesLate} pages): collapse {f pagesLate coeffLate}\n  reverse (119-pi, {pagesReverse} pages): collapse {f pagesReverse coeffReverse}\n  even    (2pi+2,  {pagesEven} pages): collapse {f pagesEven coeffEven}\n  odd     (2pi+3,  {pagesOdd} pages): collapse {f pagesOdd coeffOdd}  ← none"

private def writeView (path : String) (np : Nat) (ci : Nat → Nat)
    (title subtitle xlabel : String) : CommandElabM Unit := do
  let atoms ← projectFoldAtoms
  let svg := buildRepage atoms np ci title subtitle xlabel
  IO.FS.writeFile path svg
  logInfo s!"[Q-Repage] wrote {svg.length} bytes ({atoms.length} decls, {np} pages) to {path}"

syntax (name := writeLateCmd) "#writerepage_late " str : command
@[command_elab writeLateCmd]
def elabWriteLate : CommandElab := fun stx => do
  match stx with
  | `(#writerepage_late $p:str) =>
    writeView p.getString pagesLate coeffLate
      "Q-REPAGE · LATE VIEW · COLLAPSE MOVED TO PAGE 56"
      "same data, paging coeffIdx(n)=n+16: the window starts 14 coefficients later, so the unique collapse slides from page 70 to page 56"
      "[q^16] j                                          [q^119] j"
  | _ => throwError "ill-formed #writerepage_late command"

syntax (name := writeReverseCmd) "#writerepage_reverse " str : command
@[command_elab writeReverseCmd]
def elabWriteReverse : CommandElab := fun stx => do
  match stx with
  | `(#writerepage_reverse $p:str) =>
    writeView p.getString pagesReverse coeffReverse
      "Q-REPAGE · REVERSE VIEW · COLLAPSE MOVED TO PAGE 47"
      "same data, paging coeffIdx(n)=119−n: the coefficients play backwards, so the collapse appears at page 47"
      "[q^118] j                                          [q^1] j"
  | _ => throwError "ill-formed #writerepage_reverse command"

syntax (name := writeEvenCmd) "#writerepage_even " str : command
@[command_elab writeEvenCmd]
def elabWriteEven : CommandElab := fun stx => do
  match stx with
  | `(#writerepage_even $p:str) =>
    writeView p.getString pagesEven coeffEven
      "Q-REPAGE · EVEN VIEW · COLLAPSE MOVED TO PAGE 35"
      "same data, paging coeffIdx(n)=2n+2: only even-power coefficients; index 72 is even so the collapse survives, at page 35"
      "[q^1] j                                            [q^117] j"
  | _ => throwError "ill-formed #writerepage_even command"

syntax (name := writeOddCmd) "#writerepage_odd " str : command
@[command_elab writeOddCmd]
def elabWriteOdd : CommandElab := fun stx => do
  match stx with
  | `(#writerepage_odd $p:str) =>
    writeView p.getString pagesOdd coeffOdd
      "Q-REPAGE · ODD VIEW · THE COLLAPSE DISAPPEARS"
      "same data, paging coeffIdx(n)=2n+3: only odd-power coefficients; the unique collapse coefficient [q^71] j is even and is never read, so no page ever collapses"
      "[q^2] j                                            [q^118] j"
  | _ => throwError "ill-formed #writerepage_odd command"

/-! ## Build-time generation -/

#repage_all

#writerepage_late "atlas_repage_late.svg"
#writerepage_reverse "atlas_repage_reverse.svg"
#writerepage_even "atlas_repage_even.svg"
#writerepage_odd "atlas_repage_odd.svg"

end QRepage

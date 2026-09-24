import RequestProject.SVG
import RequestProject.Moonshine
import RequestProject.DualAtlas
import Lean

/-!
# IrrepGears: the 194 Monster irreps as a deforming train of rotating gears,
with `7^6` as the pivot

This layer answers the request:

> so `7^6` is like a pivot point.  lets now add in the 194 irreps and deform
> them, and show the outline of each and who contains who.  i imagine many
> rotating gears.

## The picture

The Monster has exactly **194 irreducible representations** (`Moonshine.numIrreps
= 194`).  Here each irrep `i ∈ {0,…,193}` is drawn as a literal **gear** whose
tooth count is `teeth i = i + 1` (so the 194 gears carry `1,2,…,194` teeth).  All
194 gears rotate continuously, and — to honour "deform them" — each one also
breathes (an additive scale pulse), so its outline is constantly deforming while
it turns.

**Who contains who.**  One gear *contains* another exactly when its tooth count
is a multiple of the other's: gear `a` (teeth `t_a`) contains gear `b` (teeth
`t_b`) iff `t_b ∣ t_a` and `t_b < t_a`.  This is the genuine divisibility partial
order on `{1,…,194}`.  Two gears **mesh** (are drawn joined by a tooth-line) when
one is an *immediate* divisor of the other — i.e. the ratio of tooth counts is a
single prime.  Because `a/b` prime forces `Ω(a) = Ω(b) + 1`, every meshing line
runs between two **adjacent rings**, so the whole figure is a real gear train:

* gears are placed on concentric rings by their **depth** `Ω(teeth)` (the number
  of prime factors with multiplicity); ring `0` is the lone hub gear (teeth `1`,
  which divides — is contained in — every other gear), and ring `d` holds every
  gear of depth `d`;
* adjacent rings rotate in **opposite directions**, exactly as meshing gears must.

**The pivot.**  `7^6 = 117649` is the crossover of the dual-atlas deformation
(`DualDeformSVG`: `2^46,3^20,5^9` shrink, then `7^6,11^2,13^3` grow).  Projected
into the 194 irreps it lands on irrep index `117649 % 194 = 85`, i.e. the gear
with `86` teeth — drawn here as the highlighted **pivot gear**.  Its dual `6^7 =
279936` lands on index `188` (the `189`-tooth gear), the **dual pivot**.

## Findings (all proved, computed natively by Lean)

* `gears_count` — there are exactly `194` gears (one per Monster irrep).
* `pivot_index` / `dual_pivot_index` — `7^6` ↦ index `85` (teeth `86`); `6^7` ↦
  index `188` (teeth `189`).
* `containment_pairs` — there are exactly `859` "contains" pairs (strict
  divisibility) among the 194 gears.
* `cover_edges_count` — exactly `357` of those are *meshing* (immediate-divisor)
  pairs — the gear-train teeth-lines drawn here.
* `top_gears_count` — exactly `97` gears are contained in nothing (the outermost
  ring of "free" gears, teeth `98 … 194`).
* `ring_sizes` — the eight rings hold `[1,44,62,47,23,11,4,2]` gears by depth.
* `max_depth` — the deepest gear sits at depth `7` (teeth `128 = 2^7`); the
  powers-of-two tower `1∣2∣4∣8∣16∣32∣64∣128` is a containment chain of length 8.
* `hub_contained_in_all` — the hub gear (teeth `1`) is contained in every gear.

Commands:

* `#irrepgears`              — build the gear-train SVG; report its size.
* `#writeirrepgears "path"`  — write the gear-train SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace IrrepGears

/-! ## Number theory of the gears (the "who contains who" data) -/

/-- Count the prime factors of `m` with multiplicity, trial-dividing from `d`,
fuel-bounded so the recursion is structural (and kernel-reducible). -/
def factorCount : Nat → Nat → Nat → Nat
  | _, _, 0 => 0
  | m, d, fuel + 1 =>
    if d * d > m then (if m > 1 then 1 else 0)
    else if m % d == 0 then 1 + factorCount (m / d) d fuel
    else factorCount m (d + 1) fuel

/-- `Ω(n)` — the number of prime factors of `n` counted with multiplicity. -/
def bigOmega (n : Nat) : Nat := if n ≤ 1 then 0 else factorCount n 2 (n + 1)

/-- Primality test (used to detect *immediate* divisors: `a/b` prime). -/
def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range n).all (fun d => d < 2 || n % d ≠ 0)

/-- The number of gears: one per Monster irrep. -/
def numGears : Nat := Moonshine.numIrreps

/-- The tooth counts of the 194 gears: `1, 2, …, 194`. -/
def gearTeeth : List Nat := (List.range numGears).map (· + 1)

/-- The depth (ring) of a gear: `Ω` of its tooth count. -/
def depthOf (t : Nat) : Nat := bigOmega t

/-- The gears sitting on ring `d` (those of depth `d`), in increasing tooth order. -/
def ringMembers (d : Nat) : List Nat := gearTeeth.filter (fun t => depthOf t == d)

/-- The number of gears on ring `d`. -/
def ringSize (d : Nat) : Nat := (ringMembers d).length

/-- The rank of gear `t` within its own ring (its index among same-depth gears). -/
def rankOf (t : Nat) : Nat := (ringMembers (depthOf t)).findIdx (· == t)

/-- All strict "contains" pairs `(b, a)` with `b ∣ a`, `b < a` (the full
divisibility order — who contains who). -/
def containEdges : List (Nat × Nat) :=
  gearTeeth.flatMap (fun a =>
    gearTeeth.filterMap (fun b => if b < a && a % b == 0 then some (b, a) else none))

/-- The *meshing* (immediate-divisor) pairs `(b, a)`: `b ∣ a`, `b < a`, and the
ratio `a / b` is prime — the gear-train teeth-lines. -/
def meshEdges : List (Nat × Nat) :=
  gearTeeth.flatMap (fun a =>
    gearTeeth.filterMap (fun b =>
      if b < a && a % b == 0 && isPrime (a / b) then some (b, a) else none))

/-- The "free" gears, contained in nothing: tooth counts with no multiple `≤ 194`. -/
def topGears : List Nat :=
  gearTeeth.filter (fun t => gearTeeth.all (fun u => !(u > t && u % t == 0)))

/-- The pivot tooth count: `7^6 = 117649` projects to irrep index `85`, gear teeth `86`. -/
def pivotTeeth : Nat := (117649 % numGears) + 1

/-- The dual pivot tooth count: `6^7 = 279936` projects to irrep index `188`, gear teeth `189`. -/
def dualPivotTeeth : Nat := (279936 % numGears) + 1

/-! ## Proved findings -/

/-- There are exactly `194` gears, one per Monster irrep. -/
theorem gears_count : numGears = 194 := rfl

/-- `7^6 = 117649` lands on irrep index `85`, i.e. the gear with `86` teeth. -/
theorem pivot_index : 117649 % numGears = 85 := by decide

theorem pivot_teeth_eq : pivotTeeth = 86 := by decide

/-- `6^7 = 279936` lands on irrep index `188`, i.e. the gear with `189` teeth. -/
theorem dual_pivot_index : 279936 % numGears = 188 := by decide

theorem dual_pivot_teeth_eq : dualPivotTeeth = 189 := by decide

/-- There are exactly `859` strict containment ("contains") pairs among the gears. -/
theorem containment_pairs : containEdges.length = 859 := by native_decide

/-- Exactly `357` of those are meshing (immediate-divisor) pairs — the gear-train lines. -/
theorem cover_edges_count : meshEdges.length = 357 := by native_decide

/-- Exactly `97` gears are contained in nothing (the outermost free gears). -/
theorem top_gears_count : topGears.length = 97 := by native_decide

/-- The eight rings hold `[1,44,62,47,23,11,4,2]` gears by depth. -/
theorem ring_sizes : (List.range 8).map ringSize = [1, 44, 62, 47, 23, 11, 4, 2] := by
  native_decide

/-- The deepest gear sits at depth `7`. -/
theorem max_depth : (gearTeeth.map depthOf).foldl Nat.max 0 = 7 := by native_decide

/-- The powers-of-two tower `1 ∣ 2 ∣ 4 ∣ 8 ∣ 16 ∣ 32 ∣ 64 ∣ 128` is a containment
chain of length `8` (matching `max_depth + 1`). -/
theorem two_chain :
    [(1, 2), (2, 4), (4, 8), (8, 16), (16, 32), (32, 64), (64, 128)].all
      (fun p => p.2 % p.1 == 0) = true := by decide

/-- The hub gear (teeth `1`) is contained in every gear: it divides them all. -/
theorem hub_contained_in_all : gearTeeth.all (fun t => t % 1 == 0) = true := by native_decide

/-! ## Geometry -/

def tau : Float := 6.283185307
def cx : Float := 940.0
def cy : Float := 1030.0

/-- Truncate a `Float` to an `Int` for SVG coordinates. -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- The ring radius for depth `d`: the hub at the centre, then expanding rings. -/
def ringR (d : Nat) : Float :=
  if d == 0 then 0.0 else 150.0 + Float.ofNat (d - 1) * 120.0

/-- The angle of gear `t` on its ring (with a per-ring offset so meshing lines
between rings don't all line up radially). -/
def gearAngle (t : Nat) : Float :=
  let d := depthOf t
  let n := ringSize d
  tau * Float.ofNat (rankOf t) / Float.ofNat (max n 1) + 0.37 * Float.ofNat d - 1.5707963

/-- The plane position (Float) of gear `t`. -/
def gearPosF (t : Nat) : Float × Float :=
  let d := depthOf t
  let r := ringR d
  let a := gearAngle t
  (cx + r * Float.cos a, cy + r * Float.sin a)

/-- The plane position (Int) of gear `t`. -/
def gearPos (t : Nat) : Int × Int :=
  let (x, y) := gearPosF t
  (f2i x, f2i y)

/-- The outer radius of gear `t`'s glyph (larger tooth counts → bigger gears). -/
def gearRo (t : Nat) : Float := 8.0 + Float.log (Float.ofNat (t + 1)) * 2.3

/-- The number of teeth actually drawn on the glyph (capped for legibility; the
true tooth count is reported in the gear's tooltip). -/
def visTeeth (t : Nat) : Nat := max 5 (min t 13)

/-! ## Style -/

/-- Per-ring (per-depth) colour, hot core → cool rim. -/
def ringColor : Nat → String
  | 0 => "#ffd700"
  | 1 => "#ff5db1"
  | 2 => "#ff7a59"
  | 3 => "#ffd23d"
  | 4 => "#4fd86a"
  | 5 => "#2bb6ff"
  | 6 => "#8a6bff"
  | _ => "#c8d0ff"

/-- Truncate a `Float` to an `Int` rotation duration string (seconds): bigger
gears turn slower, as in a real gear train. -/
def durOf (t : Nat) : String := s!"{6 + t / 12}s"

/-- The breathing ("deform") duration of a gear. -/
def breatheDur (t : Nat) : String := s!"{4 + t / 20}s"

/-! ## Rendering -/

/-- The gear-tooth polygon point string for a glyph centred at the local origin. -/
def cogPoints (ro ri : Float) (nteeth : Nat) : String :=
  let n := 2 * nteeth
  String.intercalate " " ((List.range n).map (fun k =>
    let r := if k % 2 == 0 then ro else ri
    let a := tau * Float.ofNat k / Float.ofNat n
    s!"{f2i (r * Float.cos a)},{f2i (r * Float.sin a)}"))

/-- One meshing (immediate-divisor) teeth-line between two gears. -/
def meshLine (e : Nat × Nat) : Svg :=
  let (bx, by_) := gearPos e.1
  let (ax, ay) := gearPos e.2
  Svg.elem "line"
    [("x1", toString bx), ("y1", toString by_),
     ("x2", toString ax), ("y2", toString ay),
     ("stroke", "#46568f"), ("stroke-width", "1"), ("opacity", "0.30")] []

/-- One gear: a rotating, breathing cog placed at its ring position.  The pivot
gear (`7^6`) and dual pivot (`6^7`) get a highlight halo and a label. -/
def gearSvg (t : Nat) : Svg :=
  let d := depthOf t
  let (gx, gy) := gearPos t
  let ro := gearRo t
  let ri := ro * 0.6
  let col := ringColor d
  let isPivot := t == pivotTeeth
  let isDual := t == dualPivotTeeth
  let dir : Int := if d % 2 == 0 then 360 else -360
  let fill := if isPivot then "#fff3b0" else if isDual then "#cfe6ff" else "#0e1430"
  let stroke := if isPivot then "#ffd700" else if isDual then "#7ad9ff" else col
  let sw := if isPivot || isDual then "2.4" else "1.3"
  let halo :=
    if isPivot || isDual then
      circle 0 0 (f2i (ro + 9.0)) "none" stroke
        [("stroke-width", "2"), ("opacity", "0.55"), ("stroke-dasharray", "3 4")]
    else group []
  let title :=
    let role :=
      if isPivot then " · PIVOT 7^6 (irrep 85)"
      else if isDual then " · DUAL PIVOT 6^7 (irrep 188)" else ""
    Svg.raw s!"<title>irrep {t - 1} · {t} teeth · depth Ω={d} · ring {d}{role}</title>"
  Svg.elem "g" [("transform", s!"translate({gx} {gy})")]
    [ title,
      halo,
      -- the rotating + breathing cog
      Svg.elem "g" []
        [ Svg.elem "polygon"
            [("points", cogPoints ro ri (visTeeth t)), ("fill", fill),
             ("stroke", stroke), ("stroke-width", sw), ("opacity", "0.92"),
             ("stroke-linejoin", "round")] [],
          circle 0 0 (f2i (ri * 0.45)) "#05060f" stroke [("stroke-width", "1")],
          Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"rotate\" from=\"0 0 0\" to=\"{dir} 0 0\" dur=\"{durOf t}\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"scale\" additive=\"sum\" values=\"1;1.1;1;0.92;1\" dur=\"{breatheDur t}\" repeatCount=\"indefinite\"/>" ],
      -- a tiny tooth-count label, not rotating
      Svg.text
        [("x", "0"), ("y", toString (f2i (ro + 11.0))), ("font-size", "7"),
         ("text-anchor", "middle"), ("fill", "#7f8bbf")] (toString t),
      -- pivot / dual labels
      (if isPivot then
        Svg.text [("x", "0"), ("y", toString (f2i (-(ro + 14.0)))), ("font-size", "12"),
                  ("font-weight", "800"), ("text-anchor", "middle"), ("fill", "#ffd700")]
          "PIVOT 7^6"
       else if isDual then
        Svg.text [("x", "0"), ("y", toString (f2i (-(ro + 14.0)))), ("font-size", "12"),
                  ("font-weight", "800"), ("text-anchor", "middle"), ("fill", "#7ad9ff")]
          "DUAL 6^7"
       else group []) ]

/-- Faint reference rings, one per depth. -/
def ringGuides : Svg :=
  group ((List.range 8).map (fun d =>
    circle (f2i cx) (f2i cy) (f2i (ringR d)) "none" "#1d2750"
      [("stroke-width", "1"), ("opacity", "0.5")]))

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"ggbg\" cx=\"50%\" cy=\"52%\" r=\"75%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"ggbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1820 86 "url(#ggbanner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "56"), ("y", "62"), ("font-size", "28"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "1")]
        "194 IRREP GEARS · ROTATING & DEFORMING · WHO CONTAINS WHO · PIVOT 7^6",
      Svg.text [("x", "58"), ("y", "92"), ("font-size", "14"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "one gear per Monster irrep (teeth = i+1); a contains b iff teeth_b ∣ teeth_a; adjacent rings mesh & counter-rotate; 7^6 → irrep 85 is the pivot gear" ]

def findingsBadge : Svg :=
  group
    [ rect 30 1948 1820 46 "#0b1430" "#2a7fff" [("rx", "8"), ("stroke-width", "1"), ("opacity", "0.93")],
      Svg.text [("x", "44"), ("y", "1968"), ("font-size", "12"), ("fill", "#9fb0e0")]
        "FINDINGS (proved) · 194 gears · 859 contains-pairs · 357 meshing (immediate-divisor) lines · 97 free gears · rings [1,44,62,47,23,11,4,2] · depth ≤ 7 (1∣2∣…∣128)",
      Svg.text [("x", "44"), ("y", "1986"), ("font-size", "11"), ("fill", "#6f7eb5")]
        "PIVOT 7^6=117649 → irrep 85 (86 teeth) · DUAL 6^7=279936 → irrep 188 (189 teeth) · generated natively by Lean · #writeirrepgears" ]

/-- Build the full gear-train SVG document string. -/
def buildGears : String :=
  let meshes := group (meshEdges.map meshLine)
  let gears := group (gearTeeth.map gearSvg)
  let doc := document 1880 2010
    [ Svg.raw defsRaw,
      rect 0 0 1880 2010 "url(#ggbg)" "none" [],
      banner,
      ringGuides,
      meshes,
      gears,
      findingsBadge ]
  render doc

/-! ## Commands -/

syntax (name := irrepgearsCmd) "#irrepgears" : command

@[command_elab irrepgearsCmd]
def elabIrrepgears : CommandElab := fun _ => do
  let svg := buildGears
  logInfo s!"[Irrep Gears] {numGears} gears, {meshEdges.length} meshing lines ({containEdges.length} contains-pairs), pivot teeth {pivotTeeth} → {svg.length}-byte animated SVG."

syntax (name := writeirrepgearsCmd) "#writeirrepgears " str : command

@[command_elab writeirrepgearsCmd]
def elabWriteirrepgears : CommandElab := fun stx => do
  match stx with
  | `(#writeirrepgears $p:str) => do
    let path := p.getString
    let svg := buildGears
    IO.FS.writeFile path svg
    logInfo s!"[Irrep Gears] wrote {svg.length} bytes ({numGears} gears, {meshEdges.length} meshing lines) to {path}"
  | _ => throwError "ill-formed #writeirrepgears command"

/-! ## Build-time generation -/

#irrepgears

#writeirrepgears "atlas_irrepgears.svg"

end IrrepGears

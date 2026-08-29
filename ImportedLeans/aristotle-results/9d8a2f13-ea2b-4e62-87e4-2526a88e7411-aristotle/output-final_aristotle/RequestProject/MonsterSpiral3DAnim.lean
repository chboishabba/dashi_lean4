/-
# The six panels, zoomed in and animated

`visualization/monster-spiral-3d.svg` puts six three-dimensional views on one sheet, each seen
from one fixed camera.  This file renders each of those panels **on its own**, enlarged to fill
its own canvas, and **animated**: the camera walks once around the vertical (height) axis, one
frame per azimuth `2πk/N`, with the elevation breathing gently over the same loop.  Each file is
a self-contained SVG flip-book (SMIL `<animate>` on `display`, so it plays in a browser with no
scripting) and loops seamlessly.

* `visualization/monster-spiral-3d-panel-a.svg` — the horn and the universal helix;
* `visualization/monster-spiral-3d-panel-b.svg` — the 110 prime-power heights of `|M|`;
* `visualization/monster-spiral-3d-panel-c.svg` — the tower of the 26 sporadic heights;
* `visualization/monster-spiral-3d-panel-d.svg` — the 24 threads as 24 stacked planes;
* `visualization/monster-spiral-3d-panel-e.svg` — the 15 factor spirals and the running product;
* `visualization/monster-spiral-3d-panel-f.svg` — the landscape `|∑_{n ≤ 200} n^{-s}|`;
* `visualization/monster-spiral-3d-panels.html` — the six of them on one page.

The geometry is exactly the geometry of `RequestProject/MonsterSpiral3DSvg.lean`; only the camera
moves and the scale is refitted.  That this changes nothing about the object is proved in
`RequestProject/SpiralOrbit.lean`: the orbit `rotZ` is a rigid motion (`SpiralOrbit.dist3_rotZ`)
fixing every height (`SpiralOrbit.rotZ_height`) and the horn (`SpiralOrbit.rotZ_mem_horn`), the
zoom is a similarity (`SpiralOrbit.dist3_scale3`), the two commute (`SpiralOrbit.scale3_rotZ`),
and the loop closes exactly after `N` frames (`SpiralOrbit.rotZ_frameAz_last`).

Panel D turns about the axis it draws: the midpoint of the dashed height axis is pinned to the
horizontal centre of the canvas (`PanelAnim.anchor`), and the elevation is held fixed
(`PanelAnim.elAmp = 0`).  Every point `(0, 0, z)` projects to the same screen abscissa, so the
whole axis is then a fixed vertical line and the twenty-four planes turn around it, instead of
the axis drifting sideways as each frame is recentred on its own bounding box.
-/
import RequestProject.MonsterSpiral3DSvg

namespace MonsterSpiral3DAnim

open PrimeFibers Sporadic SporadicSvg MoonshineSvg MonsterSpiralSvg MonsterSpiral3DSvg

set_option autoImplicit false
set_option maxRecDepth 4000000

/-! ## Compact SVG primitives

The flip-book repeats each scene once per frame, so coordinates are rounded to two decimals
(well below a pixel at these scales) to keep the files small. -/

/-- A coordinate, rounded to two decimals. -/
def r2 (x : Float) : String := fmtFixed 2 x

/-- A polyline through already-projected points. -/
def polyR (pts : List (Float × Float)) (col : String) (w : Float) : String :=
  "  <polyline points=\"" ++ String.intercalate " " (pts.map fun q => r2 q.1 ++ "," ++ r2 q.2) ++
    "\" fill=\"none\" stroke=\"" ++ col ++ "\" stroke-width=\"" ++ r2 w ++
    "\" stroke-linejoin=\"round\" stroke-linecap=\"round\"/>"

/-- A dot at an already-projected point. -/
def dotR (q : Float × Float) (rad : Float) (fill stroke : String) : String :=
  "  <circle cx=\"" ++ r2 q.1 ++ "\" cy=\"" ++ r2 q.2 ++ "\" r=\"" ++ r2 rad ++
    "\" fill=\"" ++ fill ++ "\" stroke=\"" ++ stroke ++ "\" stroke-width=\"1.1\"/>"

/-- A segment between already-projected points. -/
def lineR (a b : Float × Float) (col : String) (w : Float) (dash : String) : String :=
  "  <line x1=\"" ++ r2 a.1 ++ "\" y1=\"" ++ r2 a.2 ++ "\" x2=\"" ++ r2 b.1 ++ "\" y2=\"" ++
    r2 b.2 ++ "\" stroke=\"" ++ col ++ "\" stroke-width=\"" ++ r2 w ++ "\"" ++
    (if dash == "" then "" else " stroke-dasharray=\"" ++ dash ++ "\"") ++ "/>"

/-- A projected polyline. -/
def pC (c : Cam) (pts : List P3) (col : String) (w : Float) : String :=
  polyR (pts.map (camProj c)) col w

/-- A projected dot. -/
def dC (c : Cam) (p : P3) (rad : Float) (fill stroke : String) : String :=
  dotR (camProj c p) rad fill stroke

/-- A projected segment. -/
def sC (c : Cam) (a b : P3) (col : String) (w : Float) (dash : String) : String :=
  lineR (camProj c a) (camProj c b) col w dash

/-- A label at a projected point. -/
def tC (c : Cam) (p : P3) (dx dy : Float) (size : Nat) (col anchor weight body : String) :
    String :=
  let q := camProj c p
  textTag (q.1 + dx) (q.2 + dy) size col anchor weight body

/-! ## Fitting the camera

The scene is projected once with unit scale to find its bounding box; a single scale, the
smallest over all frames, is then used throughout, so the object keeps its size as it turns. -/

/-- The smaller of two floats. -/
def fmin (a b : Float) : Float := if a < b then a else b

/-- The larger of two floats. -/
def fmax (a b : Float) : Float := if b < a then a else b

/-- `(minx, miny, maxx, maxy)` of the points projected with unit scale from the origin. -/
def projBox (az el dist : Float) (pts : List P3) : Float × Float × Float × Float :=
  let c : Cam := ⟨az, el, dist, 1.0, 0.0, 0.0⟩
  (pts.map (camProj c)).foldl
    (fun b q => (fmin b.1 q.1, fmin b.2.1 q.2, fmax b.2.2.1 q.1,
      fmax b.2.2.2 q.2))
    (1.0e30, 1.0e30, -1.0e30, -1.0e30)

/-- One animated panel. -/
structure PanelAnim where
  key : String
  title : String
  subs : List String
  foots : List String
  w : Float
  h : Float
  padL : Float
  padT : Float
  padR : Float
  padB : Float
  el : Float
  dist : Float
  az0 : Float
  nFrames : Nat
  dur : Float
  extent : List P3
  scene : Cam → List String
  /-- The point held fixed on the screen while the camera turns.  When it is `some A`, the
  camera turns about the vertical world axis through `A`: since every point `(0,0,z)` projects
  to the same screen abscissa, pinning `A` pins the whole drawn axis, which then stays put — at
  the horizontal centre of the canvas — and the object turns around it.  When it is `none`, each
  frame is centred on its own bounding box instead. -/
  anchor : Option P3 := none
  /-- The amplitude of the gentle rise and fall of the elevation over the loop.  Setting it to
  `0` keeps the camera at a fixed elevation, so the motion is a pure turn. -/
  elAmp : Float := 0.13

/-- The azimuth of frame `k`: one full turn over the loop. -/
def frameAzF (P : PanelAnim) (k : Nat) : Float :=
  P.az0 + twoPiF * Float.ofNat k / Float.ofNat P.nFrames

/-- The elevation of frame `k`: a gentle rise and fall over the same loop. -/
def frameElF (P : PanelAnim) (k : Nat) : Float :=
  P.el + P.elAmp * Float.sin (twoPiF * Float.ofNat k / Float.ofNat P.nFrames)

/-- The largest scale at which frame `k` still fits the canvas. -/
def fitScaleAt (P : PanelAnim) (k : Nat) : Float :=
  let b := projBox (frameAzF P k) (frameElF P k) P.dist P.extent
  let dx := fmax (b.2.2.1 - b.1) 0.000001
  let dy := fmax (b.2.2.2 - b.2.1) 0.000001
  fmin ((P.w - P.padL - P.padR) / dx) ((P.h - P.padT - P.padB) / dy)

/-- The one scale used by every frame. -/
def animScale (P : PanelAnim) : Float :=
  (List.range P.nFrames).foldl (fun acc k => fmin acc (fitScaleAt P k)) 1.0e30

/-- How far the scene reaches to the left, right, above and below the projected anchor, at unit
scale, maximised over the frames. -/
def anchorSpan (P : PanelAnim) (A : P3) : Float × Float × Float × Float :=
  (List.range P.nFrames).foldl
    (fun acc k =>
      let az := frameAzF P k
      let el := frameElF P k
      let a := camProj ⟨az, el, P.dist, 1.0, 0.0, 0.0⟩ A
      let b := projBox az el P.dist P.extent
      (fmax acc.1 (a.1 - b.1), fmax acc.2.1 (b.2.2.1 - a.1),
        fmax acc.2.2.1 (a.2 - b.2.1), fmax acc.2.2.2 (b.2.2.2 - a.2)))
    (0.0, 0.0, 0.0, 0.0)

/-- The layout of a panel: the common scale, and the screen point at which the anchor is held.
With an anchor the horizontal fit is made symmetric about it, so the anchor — hence the whole
drawn axis — sits at the horizontal centre of the drawing area and never moves. -/
def panelLayout (P : PanelAnim) : Float × Float × Float :=
  match P.anchor with
  | none => (animScale P, 0.0, 0.0)
  | some A =>
    let s := anchorSpan P A
    let bw := P.w - P.padL - P.padR
    let bh := P.h - P.padT - P.padB
    let dx := fmax (2.0 * fmax s.1 s.2.1) 0.000001
    let dy := fmax (s.2.2.1 + s.2.2.2) 0.000001
    let sc := fmin (bw / dx) (bh / dy)
    (sc, P.padL + bw / 2.0, P.padT + (bh - sc * dy) / 2.0 + sc * s.2.2.1)

/-- The camera of frame `k`, at the common scale.  Without an anchor the frame is centred on its
own bounding box; with one, the anchor is pinned to its fixed screen point. -/
def frameCam (P : PanelAnim) (L : Float × Float × Float) (k : Nat) : Cam :=
  let sc := L.1
  let az := frameAzF P k
  let el := frameElF P k
  match P.anchor with
  | none =>
    let b := projBox az el P.dist P.extent
    let cx := P.padL + (P.w - P.padL - P.padR) / 2.0 - sc * (b.1 + b.2.2.1) / 2.0
    let cy := P.padT + (P.h - P.padT - P.padB) / 2.0 - sc * (b.2.1 + b.2.2.2) / 2.0
    ⟨az, el, P.dist, sc, cx, cy⟩
  | some A =>
    let a := camProj ⟨az, el, P.dist, 1.0, 0.0, 0.0⟩ A
    ⟨az, el, P.dist, sc, L.2.1 - sc * a.1, L.2.2 - sc * a.2⟩

/-- The `display` schedule that shows frame `i` in its own slot of the loop. -/
def displayValues (n i : Nat) : String :=
  String.intercalate ";" ((List.range n).map fun j => if j == i then "inline" else "none")

/-- The azimuth of frame `k` in whole degrees, reduced to `[0, 360)`. -/
def frameDeg (P : PanelAnim) (k : Nat) : Nat :=
  let d := frameAzF P k * 180.0 / 3.141592653589793
  let r := d - 360.0 * (d / 360.0).floor
  (r + 0.5).floor.toUInt64.toNat

/-- One frame of the flip-book. -/
def frameGroup (P : PanelAnim) (L : Float × Float × Float) (k : Nat) : String :=
  let c := frameCam P L k
  "<g display=\"" ++ (if k == 0 then "inline" else "none") ++ "\">\n" ++
  "  <animate attributeName=\"display\" calcMode=\"discrete\" repeatCount=\"indefinite\" dur=\"" ++
    r2 P.dur ++ "s\" values=\"" ++ displayValues P.nFrames k ++ "\"/>\n" ++
  String.intercalate "\n" (P.scene c) ++ "\n" ++
  textTag (P.w - 24.0) (P.h - 20.0) 12 "#94a3b8" "end" "500"
    ("azimuth " ++ toString (frameDeg P k) ++ "\u00b0   frame " ++ toString (k + 1) ++ "/" ++
      toString P.nFrames) ++ "\n</g>"

/-- The largest font size, at most `maxSize`, at which `body` fits the width `avail`
in the monospace face used throughout (about `0.62·size` per character). -/
def fitSize (maxSize : Nat) (avail : Float) (body : String) : Nat :=
  let n := Float.ofNat body.length
  let s := avail / (0.62 * (if n < 1.0 then 1.0 else n))
  let k := s.floor.toUInt64.toNat
  if k < 7 then 7 else if k > maxSize then maxSize else k

/-- The whole animated panel as a standalone SVG. -/
def renderPanel (P : PanelAnim) : String :=
  let lay := panelLayout P
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt P.w) ++ " " ++
    attr "height" (fmt P.h) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt P.w ++ " " ++ fmt P.h) ++ ">\n" ++
  rectTag 0.0 0.0 P.w P.h "#ffffff" "" 1.0 ++ "\n" ++
  rectTag 12.0 12.0 (P.w - 24.0) (P.h - 24.0) "#ffffff" "#cbd5e1" 1.0 ++ "\n" ++
  textTag 34.0 52.0 (fitSize 20 (P.w - 60.0) P.title) "#0f172a" "start" "700" P.title ++ "\n" ++
  String.intercalate "\n"
    (P.subs.zipIdx.map fun (s, i) =>
      textTag 34.0 (76.0 + 20.0 * Float.ofNat i) (fitSize 12 (P.w - 60.0) s)
        "#475569" "start" "400" s) ++ "\n" ++
  String.intercalate "\n"
    ((List.range P.nFrames).map fun k => frameGroup P lay k) ++ "\n" ++
  String.intercalate "\n"
    (P.foots.zipIdx.map fun (s, i) =>
      textTag 34.0 (P.h - 44.0 + 18.0 * Float.ofNat i) (fitSize 12 (P.w - 60.0) s)
        "#334155" "start" "500" s) ++ "\n" ++
  "</svg>\n"

/-! ## Panel A — the horn and the universal helix -/

def animHelixA : List P3 :=
  (List.range 561).map fun k =>
    let z := aZmax * Float.ofNat k / 560.0
    hornPt aZk z (ang z)

def animRingsA : List (List P3) :=
  (List.range 6).map fun i =>
    let z := Float.ofNat i
    let r := Float.exp (-(ss * z))
    (ring 1.0 0.0 72).map fun q => (q.1 * r, q.2.1 * r, aZk * z)

def animMeridiansA : List (List P3) :=
  (List.range 6).map fun i =>
    let th := twoPiF * Float.ofNat i / 6.0
    (List.range 41).map fun k =>
      let z := aZmax * Float.ofNat k / 40.0
      hornPt aZk z th

def animTermsA : List (Nat × P3) :=
  ((List.range 400).drop 1).filterMap fun n =>
    let m := n + 1
    let z := Float.log (Float.ofNat m)
    if z > aZmax then none else some (m, hornPt aZk z (ang z))

def sceneA (c : Cam) : List String :=
  [sC c (0.0, 0.0, 0.0) (0.0, 0.0, aZk * aZmax) "#0f172a" 1.4 "4 3"] ++
  (animMeridiansA.map fun l => pC c l "#e6ecf3" 1.0) ++
  (animRingsA.map fun l => pC c l "#dbe3ec" 1.0) ++
  [pC c animHelixA "#1d4ed8" 1.9] ++
  (animTermsA.map fun (m, p) =>
    let d := dividesMonster m
    dC c p (if d then 4.4 else 2.4) (if d then "#e6194b" else "#94a3b8")
      (if d then "#ffffff" else "none")) ++
  (([1, 2, 3, 4, 8, 16, 32, 60] : List Nat).map fun n =>
    let z := Float.log (Float.ofNat n)
    tC c (hornPt aZk z (ang z)) 9.0 (-8.0) 12 "#0f172a" "start" "700" ("n=" ++ toString n)) ++
  ((List.range 6).map fun i =>
    tC c (0.0, 0.0, aZk * Float.ofNat i) 7.0 4.0 11 "#64748b" "start" "400"
      ("z=" ++ toString i))

def panelAAnim : PanelAnim where
  key := "a"
  title := "A.  The horn r = e^(-\u03c3z) and the universal helix H(z) = e^(-(\u03c3+it)z)"
  subs := ["height z = log n; the term n^(-s) is the point H(log n)  (natCast_cpow_eq_helixC)",
    "s = 1/2 + i\u03c1\u2081, \u03c1\u2081 = 14.134725;  radius e^(-z/2), turning t per unit height" ++
      "  (norm_helixC, helixC_shift)",
    "red: the n \u2264 244 dividing |M| \u2014 the Monster's own steps inside the \u03b6-walk"]
  foots := ["the camera orbits the height axis; the object does not move" ++
      "  (SpiralOrbit.dist3_rotZ, SpiralOrbit.rotZ_mem_horn)"]
  w := 780.0
  h := 940.0
  padL := 60.0
  padT := 150.0
  padR := 100.0
  padB := 90.0
  el := 0.30
  dist := 9.0
  az0 := 0.85
  nFrames := 24
  dur := 12.0
  extent := animHelixA ++ (animRingsA.flatMap id) ++ [(0.0, 0.0, aZk * aZmax)]
  scene := sceneA

/-! ## Panel B — the 110 prime-power heights on the unrolled cone -/

def animHelixB : List P3 :=
  (List.range 1601).map fun k =>
    let z := bZmax * Float.ofNat k / 1600.0
    conePt bZk bZmax bShrink z (ang z)

def animRingsB : List (List P3) :=
  (List.range 5).map fun i =>
    let z := 8.0 * Float.ofNat i
    let r := 1.0 - bShrink * z / bZmax
    (ring 1.0 0.0 72).map fun q => (q.1 * r, q.2.1 * r, bZk * z)

def animLadderB (c : Cam) (pe : Nat × Nat) : List String :=
  let p := pe.1
  let e := pe.2
  let col := fiberColor p
  (List.range (e + 1)).flatMap fun j =>
    let z := Float.ofNat j * Float.log (Float.ofNat p)
    if z > bZmax then [] else
      let q := conePt bZk bZmax bShrink z (ang z)
      [sC c (0.0, 0.0, q.2.2) q "#cbd5e1" 0.7 "",
       dC c q (if e ≥ 9 then 3.0 else 4.2) col "#ffffff"]

def sceneB (c : Cam) : List String :=
  [sC c (0.0, 0.0, 0.0) (0.0, 0.0, bZk * bZmax) "#0f172a" 1.4 "4 3",
   pC c animHelixB "#c7d2e5" 0.7] ++
  (animRingsB.map fun l => pC c l "#e2e8f0" 0.9) ++
  (mFactors.flatMap (animLadderB c)) ++
  ((List.range 5).map fun i =>
    tC c (0.0, 0.0, bZk * 8.0 * Float.ofNat i) 7.0 4.0 11 "#64748b" "start" "400"
      ("z=" ++ toString (8 * i))) ++
  [tC c (conePt bZk bZmax bShrink (46.0 * Float.log 2.0) (ang (46.0 * Float.log 2.0)))
    10.0 15.0 13 "#e6194b" "start" "700" "2^46"]

def panelBAnim : PanelAnim where
  key := "b"
  title := "B.  The 110 prime-power heights of |M|, on the unrolled cone"
  subs := ["radius plotted as log r = -\u03c3z (log_norm_helixC): the horn becomes a straight" ++
      " cone, so all heights stay visible",
    "the prime p occupies the progression of heights j\u00b7log p  (factorTerm_eq_helixC)" ++
      " \u2014 hence its equiangular spiral",
    "46 heights for 2 (top 46\u00b7log 2 = 31.883, two_fiber_top_height), 20 for 3, 9 for 5," ++
      " 6 for 7, 3 for 13, 2 for 11, one each for the other nine"]
  foots := ["one turn of the camera about the height axis, 24 frames"]
  w := 720.0
  h := 940.0
  padL := 60.0
  padT := 160.0
  padR := 80.0
  padB := 80.0
  el := 0.26
  dist := 10.0
  az0 := 0.85
  nFrames := 24
  dur := 12.0
  extent := animHelixB ++ (animRingsB.flatMap id) ++ [(0.0, 0.0, bZk * bZmax)]
  scene := sceneB

/-! ## Panel C — the tower of heights -/

def animSegmentsC (c : Cam) : List String :=
  mFactors.zipIdx.flatMap fun (pe, i) =>
    let z0 := cumHeights.getD i 0.0
    let z1 := cumHeights.getD (i + 1) 0.0
    let col := fiberColor pe.1
    [sC c (0.0, 0.0, cZk * z0) (0.0, 0.0, cZk * z1) col 10.0 "",
     pC c (ring 0.10 (cZk * z1) 36) "#94a3b8" 0.6] ++
    (if z1 - z0 > 1.6 then
      [tC c (0.0, 0.0, cZk * (z0 + z1) / 2.0) (c.scale * 0.42) 4.0 12 col "start" "700"
        (toString pe.1 ++ "^" ++ toString pe.2 ++ "  (" ++ fmtFixed 2 (z1 - z0) ++ ")")]
     else [])

def sceneC (c : Cam) : List String :=
  [sC c (0.0, 0.0, 0.0) (0.0, 0.0, cZk * monsterHeight) "#e2e8f0" 12.0 ""] ++
  animSegmentsC c ++
  ((List.range 47).map fun k =>
    let z := Float.ofNat k * Float.log 2.0
    sC c (-0.18, 0.0, cZk * z) (-0.06, 0.0, cZk * z) "#e6194b" 1.2 "") ++
  (sortedGroups.flatMap fun G =>
    let z := gHeight G
    [pC c (ring 0.34 (cZk * z) 32) "#a8b4c4" 0.7,
     dC c (0.34 * Float.cos (ang z), 0.34 * Float.sin (ang z), cZk * z) 3.0 "#0f172a" "none"]) ++
  (sortedGroups.zipIdx.map fun (G, i) =>
    let z := gHeight G
    let rad : Float := if i % 2 == 0 then 0.50 else 1.12
    tC c (0.0, 0.0, cZk * z) (-(c.scale * rad)) 3.0 11 "#334155" "end" "500"
      (G.name ++ " " ++ fmtFixed 2 z)) ++
  [tC c (0.0, 0.0, cZk * monsterHeight) 0.0 (-18.0) 14 "#0f172a" "middle" "700"
    ("log|M| = " ++ fmtFixed 3 monsterHeight)]

def panelCAnim : PanelAnim where
  key := "c"
  title := "C.  The tower: the 26 sporadic heights, and the 15 that stack to log|M|"
  subs := ["log|M| = \u2211_p e_p\u00b7log p = 124.13  (monster_height_eq_sum; 124 &lt; log|M|" ++
      " &lt; 125 by monster_height_bounds)",
    "rings: the 26 sporadic orders, from |M11| = 8.98 upwards  (sporadic_height_bounds," ++
      " sporadic_orders_nodup)",
    "red ticks alongside the column: the 47 heights k\u00b7log 2 of the fiber of 2"]
  foots := ["the tower turning on its axis; the fifteen coloured blocks are the prime powers" ++
      " of |M|"]
  w := 1020.0
  h := 1400.0
  padL := 210.0
  padT := 160.0
  padR := 200.0
  padB := 90.0
  el := 0.16
  dist := 14.0
  az0 := 0.80
  nFrames := 24
  dur := 12.0
  extent := (ring 1.15 0.0 24) ++ (ring 1.15 (cZk * monsterHeight) 24) ++
    [(0.0, 0.0, cZk * monsterHeight), (0.0, 0.0, 0.0)]
  scene := sceneC

/-! ## Panel D — the twenty-four threads as twenty-four stacked planes -/

def animPlaneD (c : Cam) (a : Nat) : List String :=
  let zs := dZk * Float.ofNat a
  let vs := (0.0, 0.0) :: threadVerts a 500 ss tt
  let pts : List P3 := vs.map fun z => (dScale * z.1, dScale * z.2, zs)
  let v := threadValue a 500 ss tt
  [pC c pts (threadColor a) 1.5,
   dC c (dScale * v.1, dScale * v.2, zs) 3.2 (threadColor a) "#ffffff",
   tC c (0.0, 0.0, zs) (-11.0) 4.0 11 "#64748b" "end" "500" (toString a)]

def animPtsD : List P3 :=
  ((List.range 24).flatMap fun a =>
    ((0.0, 0.0) :: threadVerts a 500 ss tt).map fun z =>
      (dScale * z.1, dScale * z.2, dZk * Float.ofNat a)) ++
  ((threadChain 500 ss tt).map fun z => (dScale * z.1, dScale * z.2, dZk * 26.5))

def sceneD (c : Cam) : List String :=
  let zc := dZk * 26.5
  let chain := (threadChain 500 ss tt).map fun z => (dScale * z.1, dScale * z.2, zc)
  let fin := (threadChain 500 ss tt).getLastD (0.0, 0.0)
  [sC c (0.0, 0.0, 0.0) (0.0, 0.0, zc) "#cbd5e1" 1.0 "4 3"] ++
  ((List.range 24).flatMap (animPlaneD c)) ++
  [pC c chain "#0f172a" 1.9,
   dC c (dScale * fin.1, dScale * fin.2, zc) 4.4 "#0f172a" "#ffffff"]

def panelDAnim : PanelAnim where
  key := "d"
  title := "D.  The other separation, stacked: the twenty-four threads mod 24"
  subs := ["thread a = \u2211_{n \u2264 500, n \u2261 a (24)} n^(-s), each in its own plane" ++
      " z = a;  they add back up (sum_thread)",
    "the 24 threads are the 24 McKay\u2013Thompson twists Fourier-inverted (thread_eq_fourier)",
    "black, on top: the 24 thread vectors added head to tail = \u2211_{n\u2264500} n^(-s) = " ++
      (let fin := (threadChain 500 ss tt).getLastD (0.0, 0.0)
       fmtFixed 3 fin.1 ++ (if fin.2 < 0.0 then " - " else " + ") ++
         fmtFixed 3 (Float.abs fin.2) ++ "i")]
  foots := ["the powers of 2 visit only the planes 2, 4, 8, 16  (two_pow_mod24_mem_four)"]
  w := 820.0
  h := 940.0
  padL := 70.0
  padT := 150.0
  padR := 70.0
  padB := 80.0
  el := 0.45
  dist := 11.0
  az0 := 0.95
  nFrames := 24
  dur := 12.0
  extent := animPtsD
  scene := sceneD
  -- the drawn (dashed) axis is the segment from `(0,0,0)` to `(0,0,dZk·26.5)`; pinning its
  -- midpoint keeps that axis at the centre of the canvas, so the twenty-four planes turn
  -- around the axis that is displayed instead of the axis drifting across the picture
  anchor := some (0.0, 0.0, dZk * 26.5 / 2.0)
  -- and the elevation is held fixed, so the motion is exactly a turn about that axis
  elAmp := 0.0

/-! ## Panel E — the fifteen factor spirals and the running product -/

def animPlaneE (c : Cam) (i : Nat) (pe : Nat × Nat) : List String :=
  let zs := eZk * Float.ofNat i
  let col := fiberColor pe.1
  let vs := (0.0, 0.0) :: facVerts pe.1 pe.2 ss tt
  let pts : List P3 := vs.map fun z => (eOffL + eScale * (z.1 - eCtrL), eScale * z.2, zs)
  let v := facValue pe.1 pe.2 ss tt
  [pC c pts col 1.6,
   dC c (eOffL + eScale * (v.1 - eCtrL), eScale * v.2, zs) 3.4 col "#ffffff",
   tC c (eOffL - eScale * eCtrL, 0.0, zs) (-11.0) 4.0 11 col "end" "700"
     (toString pe.1 ++ (if pe.2 == 1 then "" else "^" ++ toString pe.2))]

def animPtsE : List P3 :=
  (mFactors.zipIdx.flatMap fun (pe, i) =>
    ((0.0, 0.0) :: facVerts pe.1 pe.2 ss tt).map fun z =>
      (eOffL + eScale * (z.1 - eCtrL), eScale * z.2, eZk * Float.ofNat i)) ++
  ((runningProducts ss tt).zipIdx.map fun (z, i) =>
    (eOffR + eScale * (z.1 - eCtrR), eScale * z.2, eZk * Float.ofNat i))

def sceneE (c : Cam) : List String :=
  let rp := runningProducts ss tt
  let pts : List P3 := rp.zipIdx.map fun (z, i) =>
    (eOffR + eScale * (z.1 - eCtrR), eScale * z.2, eZk * Float.ofNat i)
  let fin := rp.getLastD (0.0, 0.0)
  [sC c (eOffL - eScale * eCtrL, 0.0, 0.0) (eOffL - eScale * eCtrL, 0.0, eZk * 15.0)
      "#e2e8f0" 1.0 "",
   sC c (eOffR - eScale * eCtrR, 0.0, 0.0) (eOffR - eScale * eCtrR, 0.0, eZk * 15.0)
      "#e2e8f0" 1.0 ""] ++
  (mFactors.zipIdx.flatMap fun (pe, i) => animPlaneE c i pe) ++
  [pC c pts "#0f172a" 1.9] ++
  (pts.map fun q => dC c q 3.0 "#0f172a" "#ffffff") ++
  [dC c (eOffR + eScale * (fin.1 - eCtrR), eScale * fin.2, eZk * 15.0) 4.4 "#0f172a" "#ffffff"]

def panelEAnim : PanelAnim where
  key := "e"
  title := "E.  The fifteen factor spirals as fifteen planes, and the product rising through them"
  subs := ["left: \u2211_{j \u2264 e_p} (p^j)^(-s) in the plane of its prime;  right: the" ++
      " running product 1, F\u2082, F\u2082F\u2083, \u2026 one plane per prime",
    "MonsterSpiral.divisorSumC_eq_prod \u2014 the multiplicative separation of the Monster"]
  foots := ["the top of the black path is the whole divisor sum \u2211_{d | |M|} d^(-s) = " ++
      (let fin := (runningProducts ss tt).getLastD (0.0, 0.0)
       fmtFixed 4 fin.1 ++ (if fin.2 < 0.0 then " - " else " + ") ++
         fmtFixed 4 (Float.abs fin.2) ++ "i")]
  w := 1080.0
  h := 940.0
  padL := 90.0
  padT := 130.0
  padR := 90.0
  padB := 80.0
  el := 0.50
  dist := 12.0
  az0 := 0.95
  nFrames := 24
  dur := 12.0
  extent := animPtsE
  scene := sceneE

/-! ## Panel F — the landscape over the s-plane -/

/-- The number of samples along `t`.  The zoomed panel samples `t` four times more finely
than the sheet version: at `\u03c3 \u2248 1/2` the term `200^{-s}` turns once every
`2\u03c0/log 200 = 1.19` in `t`, so the sheet's spacing of `0.67` aliases the ripple, and
`0.25` does not. -/
def animNT : Nat := 161

/-- The `t` of column `j`. -/
def animT (j : Nat) : Float := 40.0 * Float.ofNat j / Float.ofNat (animNT - 1)

/-- A point of the surface, in the coordinates of `MonsterSpiral3DSvg.fPt`. -/
def animFPt (i j : Nat) : P3 :=
  let sig := fSig i
  let t := animT j
  let a := cabs (zetaPartialF sig t)
  let h := if a < 3.2 then a else 3.2
  (1.5 * (sig - 1.25) / 1.25, 2.0 * (t - 20.0) / 20.0, 0.42 * h)

/-- The surface grid, computed once and reused by every frame. -/
def animGridF : List (List P3) :=
  (List.range fNSig).map fun i => (List.range animNT).map fun j => animFPt i j

def sceneF (g : List (List P3)) (c : Cam) : List String :=
  let row5 := g.getD 5 []
  [sC c (-1.5, -2.0, 0.0) (1.5, -2.0, 0.0) "#0f172a" 1.1 "",
   sC c (-1.5, -2.0, 0.0) (-1.5, 2.0, 0.0) "#0f172a" 1.1 "",
   tC c (1.5, -2.0, 0.0) 7.0 15.0 12 "#0f172a" "start" "600" "\u03c3 = 2.4",
   tC c (-1.5, 2.0, 0.0) (-7.0) 15.0 12 "#0f172a" "end" "600" "t = 40"] ++
  (((List.range animNT).filter (fun j => j % 4 == 0)).map fun j =>
    pC c (g.map fun row => row.getD j (0.0, 0.0, 0.0)) "#c3ccd8" 0.55) ++
  (g.zipIdx.map fun (row, i) =>
    pC c row (if i == 5 then "#e6194b" else "#94a3b8") (if i == 5 then 2.2 else 0.8)) ++
  (([14.134725, 21.022040, 25.010858] : List Float).flatMap fun t0 =>
    let j := (t0 * Float.ofNat (animNT - 1) / 40.0 + 0.5).floor.toUInt64.toNat
    let p := row5.getD j (0.0, 0.0, 0.0)
    [dC c p 4.4 "#e6194b" "#ffffff",
     sC c (p.1, p.2.1, 0.0) p "#e6194b" 0.9 "3 3",
     tC c p 8.0 (-7.0) 12 "#e6194b" "start" "600" ("t=" ++ fmtFixed 2 t0)])

def panelFAnim (g : List (List P3)) : PanelAnim where
  key := "f"
  title := "F.  The landscape |\u2211_{n \u2264 200} n^(-s)| over the s-plane"
  subs := ["\u03c3 \u2208 [0.06, 2.4] across, t \u2208 [0, 40] along;  the red rib is the" ++
      " critical line \u03c3 = 1/2, whose dips are the first three zeros of \u03b6",
    "this is the same helix seen as a function of s: the height here is |H| summed," ++
      " the height in A\u2013C is log n"]
  foots := ["orbiting the landscape: the three marked dips stay on the red rib"]
  w := 1240.0
  h := 820.0
  padL := 110.0
  padT := 130.0
  padR := 110.0
  padB := 80.0
  el := 0.42
  dist := 16.0
  az0 := 0.70
  nFrames := 18
  dur := 10.8
  extent := g.flatMap id
  scene := sceneF g

/-! ## The six files -/

/-- The six animated panels, as `(file name, contents)` pairs. -/
def panelAnimFiles : List (String × String) :=
  let g := animGridF
  [("monster-spiral-3d-panel-a.svg", renderPanel panelAAnim),
   ("monster-spiral-3d-panel-b.svg", renderPanel panelBAnim),
   ("monster-spiral-3d-panel-c.svg", renderPanel panelCAnim),
   ("monster-spiral-3d-panel-d.svg", renderPanel panelDAnim),
   ("monster-spiral-3d-panel-e.svg", renderPanel panelEAnim),
   ("monster-spiral-3d-panel-f.svg", renderPanel (panelFAnim g))]

/-- A page holding the six animations. -/
def panelAnimHtml : String :=
  let items : List (String × String) :=
    [("monster-spiral-3d-panel-a.svg",
      "A. The horn and the universal helix H(z) = e^(-(&#963;+it)z)"),
     ("monster-spiral-3d-panel-b.svg",
      "B. The 110 prime-power heights of |M| on the unrolled cone"),
     ("monster-spiral-3d-panel-c.svg",
      "C. The tower: 26 sporadic heights, 15 blocks stacking to log|M| = 124.13"),
     ("monster-spiral-3d-panel-d.svg",
      "D. The 24 threads mod 24 as 24 stacked planes"),
     ("monster-spiral-3d-panel-e.svg",
      "E. The 15 factor spirals and the running product"),
     ("monster-spiral-3d-panel-f.svg",
      "F. The landscape |&#8721;_{n &#8804; 200} n^(-s)| over the s-plane")]
  "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\"/>\n" ++
  "<title>The Monster spiral in 3D \u2014 the six panels, animated</title>\n" ++
  "<style>\n body { font-family: ui-monospace, SFMono-Regular, Menlo, monospace;" ++
  " margin: 24px; color: #0f172a; background: #f8fafc; }\n" ++
  " h1 { font-size: 20px; } p { font-size: 13px; color: #334155; max-width: 1100px; }\n" ++
  " figure { margin: 28px 0; } figcaption { font-size: 13px; margin: 6px 0; }\n" ++
  " img { width: 100%; max-width: 1240px; border: 1px solid #cbd5e1; background: #fff; }\n" ++
  "</style>\n</head>\n<body>\n" ++
  "<h1>The Monster spiral in three dimensions \u2014 each panel zoomed in and animated</h1>\n" ++
  "<p>Each panel of <code>monster-spiral-3d.svg</code> is rendered here on its own canvas," ++
  " with the camera orbiting once around the height axis (24 frames, 12 s; panel F 18 frames)." ++
  " The geometry is unchanged between frames: orbiting is a rigid motion and the zoom is a" ++
  " similarity, both proved in <code>RequestProject/SpiralOrbit.lean</code>.</p>\n" ++
  String.intercalate "\n"
    (items.map fun (f, cap) =>
      "<figure><img src=\"" ++ f ++ "\" alt=\"" ++ cap ++ "\"/><figcaption>" ++ cap ++
        "</figcaption></figure>") ++
  "\n</body>\n</html>\n"

end MonsterSpiral3DAnim

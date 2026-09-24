/-
# The picture in three dimensions

Renders the three-dimensional views of `RequestProject/MonsterSpiral3D.lean`:

* `visualization/monster-spiral-3d.svg` — six perspective-projected panels;
* `visualization/monster-spiral-3d.html` — the same geometry as a rotatable scene
  (drag to turn, wheel to zoom, checkboxes to toggle layers);
* `visualization/monster-spiral-3d.obj` — the curves as Wavefront 3D polylines;
* `visualization/monster_spiral_3d.csv` — the coordinates of the marked points.

The third coordinate is the **height** `z = log n` of `MonsterSpiral3D`: at `s = σ + it` the term
`n^{-s}` lifts to the point `(Re, Im, log n)` of the universal helix `H(z) = e^{-(σ+it)z}`
(`MonsterSpiral3D.natCast_cpow_eq_helixC`), which lies on the horn `r = e^{-σz}`
(`MonsterSpiral3D.norm_helixC`) and turns at the constant rate `t` per unit height
(`MonsterSpiral3D.helixC_shift`).

Only floating-point geometry and string manipulation live here; every claim written on the
pictures is proved in `RequestProject/MonsterSpiral3D.lean` and `RequestProject/MonsterSpiral.lean`.
-/
import RequestProject.MonsterSpiral3D
import RequestProject.MonsterSpiralSvg

namespace MonsterSpiral3DSvg

open PrimeFibers Sporadic SporadicSvg MoonshineSvg MonsterSpiralSvg

set_option autoImplicit false
set_option maxRecDepth 4000000

/-! ## The point of the critical line, and the two radial conventions -/

/-- The ordinate of the first zero of `ζ`, as everywhere else in this project. -/
def tt : Float := 14.134725

/-- The abscissa: the critical line. -/
def ss : Float := 0.5

/-! ## Three-dimensional points, cameras and projection -/

/-- A point of `ℝ³`. -/
abbrev P3 := Float × Float × Float

/-- A camera: azimuth and elevation of the viewing direction, distance (perspective strength),
pixels per world unit, and the screen position of the origin. -/
structure Cam where
  az : Float
  el : Float
  dist : Float
  scale : Float
  cx : Float
  cy : Float

/-- Perspective projection of a 3D point to the screen. -/
def camProj (c : Cam) (p : P3) : Float × Float :=
  let ca := Float.cos c.az
  let sa := Float.sin c.az
  let ce := Float.cos c.el
  let se := Float.sin c.el
  let x := p.1
  let y := p.2.1
  let z := p.2.2
  let rx := -sa * x + ca * y
  let uy := -(se * ca) * x - (se * sa) * y + ce * z
  let dp := (ce * ca) * x + (ce * sa) * y + se * z
  let f := c.dist / (c.dist - dp)
  (c.cx + c.scale * f * rx, c.cy - c.scale * f * uy)

/-- A projected polyline. -/
def pl3 (c : Cam) (pts : List P3) (col : String) (w : Float) : String :=
  polylineTag (pts.map (camProj c)) col w

/-- A projected dot. -/
def dot3 (c : Cam) (p : P3) (r : Float) (fill stroke : String) : String :=
  let q := camProj c p
  circleTag q.1 q.2 r fill stroke

/-- A projected segment. -/
def seg3 (c : Cam) (a b : P3) (col : String) (w : Float) (dash : String) : String :=
  let p := camProj c a
  let q := camProj c b
  lineTag p.1 p.2 q.1 q.2 col w dash

/-- A label at a projected point. -/
def lab3 (c : Cam) (p : P3) (dx dy : Float) (size : Nat) (col anchor weight body : String) :
    String :=
  let q := camProj c p
  textTag (q.1 + dx) (q.2 + dy) size col anchor weight body

/-- A horizontal circle of radius `r` at world height `zw`. -/
def ring (r zw : Float) (n : Nat) : List P3 :=
  (List.range (n + 1)).map fun k =>
    let a := 6.283185307179586 * Float.ofNat k / Float.ofNat n
    (r * Float.cos a, r * Float.sin a, zw)

/-! ## The two radial conventions

`hornPt` is the true geometry: radius `e^{-σz}`, the horn of `MonsterSpiral3D.norm_helixC`.
`conePt` plots the *logarithm* of the radius instead — the unrolling of
`MonsterSpiral3D.log_norm_helixC` — so that the radius falls off linearly with the height and
heights up to `log|M| = 124` stay visible. -/

/-- The true horn point at height `z` and angle `theta`, with the height compressed by `zk`. -/
def hornPt (zk z theta : Float) : P3 :=
  let r := Float.exp (-(ss * z))
  (r * Float.cos theta, r * Float.sin theta, zk * z)

/-- The log-radius cone point: radius `1 − shrink·z/zmax`. -/
def conePt (zk zmax shrink z theta : Float) : P3 :=
  let r := 1.0 - shrink * z / zmax
  (r * Float.cos theta, r * Float.sin theta, zk * z)

/-- The universal angle at height `z`: `−t·z`. -/
def ang (z : Float) : Float := -(tt * z)

/-! ## The data -/

/-- `log |G|` computed from the factorization, for each sporadic group. -/
def gHeight (G : Group) : Float :=
  (G.factors.map fun pe => Float.ofNat pe.2 * Float.log (Float.ofNat pe.1)).foldl (· + ·) 0.0

/-- The twenty-six sporadic groups sorted by height. -/
def sortedGroups : List Group :=
  groups.mergeSort (fun G H => gHeight G ≤ gHeight H)

/-- `log |M| = ∑ e_p log p = 124.13…`. -/
def monsterHeight : Float := gHeight monster

/-- The cumulative heights `0, 46·log 2, 46·log 2 + 20·log 3, …, log|M|` of the fifteen prime
segments of the tower. -/
def cumHeights : List Float :=
  (mFactors.map fun pe => Float.ofNat pe.2 * Float.log (Float.ofNat pe.1)).scanl (· + ·) 0.0

/-- Is `n` a divisor of `|M|`? -/
def dividesMonster (n : Nat) : Bool := n != 0 && monsterOrder % n == 0

/-! ## Panel A — the horn and the universal helix -/

def aCam : Cam := ⟨0.85, 0.30, 9.0, 205.0, 470.0, 700.0⟩

def aZmax : Float := 5.5
def aZk : Float := 0.42

def aHelix : List P3 :=
  (List.range 2001).map fun k =>
    let z := aZmax * Float.ofNat k / 2000.0
    hornPt aZk z (ang z)

def aHornRings : List String :=
  (List.range 6).map fun i =>
    let z := Float.ofNat i
    pl3 aCam (((ring 1.0 0.0 96).map fun q =>
      (q.1 * Float.exp (-(ss * z)), q.2.1 * Float.exp (-(ss * z)), aZk * z))) "#dbe3ec" 1.0

def aMeridians : List String :=
  (List.range 6).map fun i =>
    let th := 6.283185307179586 * Float.ofNat i / 6.0
    pl3 aCam ((List.range 61).map fun k =>
      let z := aZmax * Float.ofNat k / 60.0
      hornPt aZk z th) "#e6ecf3" 1.0

def aTerms : List String :=
  ((List.range 400).drop 1).flatMap fun n =>
    let z := Float.log (Float.ofNat (n + 1))
    if z > aZmax then [] else
      let p := hornPt aZk z (ang z)
      let d := dividesMonster (n + 1)
      [dot3 aCam p (if d then 3.4 else 1.9) (if d then "#e6194b" else "#94a3b8")
        (if d then "#ffffff" else "none")]

def aLabels : List String :=
  ([1, 2, 3, 4, 8, 16, 60] : List Nat).map fun n =>
    let z := Float.log (Float.ofNat n)
    lab3 aCam (hornPt aZk z (ang z)) 7.0 (-6.0) 11 "#0f172a" "start" "600"
      ("n=" ++ toString n)

def panelA : String :=
  String.intercalate "\n"
    ([rectTag 40.0 150.0 860.0 760.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 62.0 190.0 18 "#0f172a" "start" "700"
        "A.  The horn r = e^(-\u03c3z) and the universal helix H(z) = e^(-(\u03c3+it)z)",
      textTag 62.0 212.0 12 "#475569" "start" "400"
        "height z = log n; the term n^(-s) is the point H(log n)  (natCast_cpow_eq_helixC)",
      textTag 62.0 230.0 12 "#475569" "start" "400"
        ("s = 1/2 + i\u03c1\u2081, \u03c1\u2081 = 14.134725;  radius e^(-z/2), turning t per unit" ++
          " height  (norm_helixC, helixC_shift)"),
      seg3 aCam (0.0, 0.0, 0.0) (0.0, 0.0, aZk * aZmax) "#0f172a" 1.4 "4 3"] ++
     aMeridians ++ aHornRings ++
     [pl3 aCam aHelix "#1d4ed8" 1.5] ++ aTerms ++ aLabels ++
     ((List.range 6).map fun i =>
        lab3 aCam (0.0, 0.0, aZk * Float.ofNat i) 6.0 4.0 10 "#64748b" "start" "400"
          ("z=" ++ toString i)) ++
     [textTag 62.0 872.0 12 "#334155" "start" "500"
        "red: the n \u2264 244 dividing |M| \u2014 the Monster's own steps inside the \u03b6-walk",
      textTag 62.0 890.0 12 "#334155" "start" "500"
        "(MonsterSpiral.monsterSpiral_eq_filter_sum)"])

/-! ## Panel B — the Monster's 110 prime-power heights on the unrolled cone -/

def bCam : Cam := ⟨0.85, 0.26, 10.0, 165.0, 1330.0, 790.0⟩

def bZmax : Float := 32.0
def bZk : Float := 0.10
def bShrink : Float := 0.78

def bHelix : List P3 :=
  (List.range 8001).map fun k =>
    let z := bZmax * Float.ofNat k / 8000.0
    conePt bZk bZmax bShrink z (ang z)

def bLadder (pe : Nat × Nat) : List String :=
  let p := pe.1
  let e := pe.2
  let col := fiberColor p
  (List.range (e + 1)).flatMap fun j =>
    let z := Float.ofNat j * Float.log (Float.ofNat p)
    if z > bZmax then [] else
      let q := conePt bZk bZmax bShrink z (ang z)
      [seg3 bCam (0.0, 0.0, q.2.2) q "#cbd5e1" 0.6 "",
       dot3 bCam q (if e ≥ 9 then 2.4 else 3.6) col "#ffffff"]

def panelB : String :=
  String.intercalate "\n"
    ([rectTag 940.0 150.0 820.0 760.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 962.0 190.0 18 "#0f172a" "start" "700"
        "B.  The 110 prime-power heights of |M|, on the unrolled cone",
      textTag 962.0 212.0 12 "#475569" "start" "400"
        ("radius plotted as log r = -\u03c3z (log_norm_helixC): the horn becomes a" ++
          " straight cone, so all heights stay visible"),
      textTag 962.0 230.0 12 "#475569" "start" "400"
        ("the prime p occupies the progression of heights j\u00b7log p" ++
          "  (factorTerm_eq_helixC) \u2014 hence its equiangular spiral"),
      seg3 bCam (0.0, 0.0, 0.0) (0.0, 0.0, bZk * bZmax) "#0f172a" 1.4 "4 3",
      pl3 bCam bHelix "#c7d2e5" 0.6] ++
     (mFactors.flatMap bLadder) ++
     ((List.range 5).map fun i =>
        let z := 8.0 * Float.ofNat i
        pl3 bCam (((ring 1.0 0.0 96).map fun q =>
          let r := 1.0 - bShrink * z / bZmax
          (q.1 * r, q.2.1 * r, bZk * z))) "#e2e8f0" 0.8) ++
     ((List.range 5).map fun i =>
        lab3 bCam (0.0, 0.0, bZk * 8.0 * Float.ofNat i) 6.0 4.0 10 "#64748b" "start" "400"
          ("z=" ++ toString (8 * i))) ++
     [lab3 bCam (conePt bZk bZmax bShrink (46.0 * Float.log 2.0)
        (ang (46.0 * Float.log 2.0))) 9.0 14.0 11 "#e6194b" "start" "700" "2^46",
      textTag 962.0 872.0 12 "#334155" "start" "500"
        ("46 heights for 2 (top 46\u00b7log 2 = 31.883, two_fiber_top_height), 20 for 3," ++
          " 9 for 5, 6 for 7,"),
      textTag 962.0 890.0 12 "#334155" "start" "500"
        "3 for 13, 2 for 11, one each for the other nine supersingular primes"])

/-! ## Panel C — the tower of heights: 124.13 = log |M| -/

def cCam : Cam := ⟨0.80, 0.16, 14.0, 213.0, 470.0, 1985.0⟩

def cZk : Float := 0.031

def cSegments : List String :=
  (mFactors.zipIdx.flatMap fun (pe, i) =>
    let z0 := cumHeights.getD i 0.0
    let z1 := cumHeights.getD (i + 1) 0.0
    let col := fiberColor pe.1
    [seg3 cCam (0.0, 0.0, cZk * z0) (0.0, 0.0, cZk * z1) col 9.0 "",
     pl3 cCam (ring 0.10 (cZk * z1) 48) "#94a3b8" 0.6] ++
    (if z1 - z0 > 1.6 then
      [lab3 cCam (-0.30, 0.0, cZk * (z0 + z1) / 2.0) 12.0 4.0 11 col "start" "700"
        (toString pe.1 ++ "^" ++ toString pe.2 ++ "  (" ++ fmtFixed 2 (z1 - z0) ++ ")")]
     else []))

def cTwoTicks : List String :=
  (List.range 47).map fun k =>
    let z := Float.ofNat k * Float.log 2.0
    seg3 cCam (-0.18, 0.0, cZk * z) (-0.06, 0.0, cZk * z) "#e6194b" 1.1 ""

def cGroupRings : List String :=
  sortedGroups.flatMap fun G =>
    let z := gHeight G
    [pl3 cCam (ring 0.34 (cZk * z) 64) "#a8b4c4" 0.7,
     dot3 cCam (0.34 * Float.cos (ang z), 0.34 * Float.sin (ang z), cZk * z) 2.6 "#0f172a" "none"]

def cGroupLabels : List String :=
  sortedGroups.zipIdx.map fun (G, i) =>
    let z := gHeight G
    let rad : Float := if i % 2 == 0 then 0.52 else 1.15
    lab3 cCam (rad, 0.0, cZk * z) (-8.0) 3.0 9 "#334155" "end" "500"
      (G.name ++ " " ++ fmtFixed 2 z)

def panelC : String :=
  String.intercalate "\n"
    ([rectTag 40.0 950.0 860.0 1080.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 62.0 990.0 18 "#0f172a" "start" "700"
        "C.  The tower: the twenty-six sporadic heights, and the fifteen that stack to log|M|",
      textTag 62.0 1012.0 12 "#475569" "start" "400"
        ("log|M| = \u2211_p e_p\u00b7log p = 124.13  (monster_height_eq_sum;" ++
          " 124 &lt; log|M| &lt; 125 by monster_height_bounds)"),
      textTag 62.0 1030.0 12 "#475569" "start" "400"
        ("rings: the 26 sporadic orders, from |M11| = 8.98 upwards" ++
          "  (sporadic_height_bounds, sporadic_orders_nodup)"),
      textTag 62.0 1048.0 12 "#475569" "start" "400"
        "red ticks alongside the column: the 47 heights k\u00b7log 2 of the fiber of 2",
      seg3 cCam (0.0, 0.0, 0.0) (0.0, 0.0, cZk * monsterHeight) "#e2e8f0" 11.0 ""] ++
     cSegments ++ cTwoTicks ++ cGroupRings ++ cGroupLabels ++
     [lab3 cCam (0.0, 0.0, cZk * monsterHeight) 0.0 (-16.0) 13 "#0f172a" "middle" "700"
        ("log|M| = " ++ fmtFixed 3 monsterHeight),
      textTag 62.0 2000.0 12 "#334155" "start" "500"
        ("the \u03b6-spiral truncated at N = |M| turns by t\u00b7log|M| = " ++
          fmtFixed 1 (tt * monsterHeight) ++ " rad = " ++
          fmtFixed 1 (tt * monsterHeight / twoPi) ++
          " turns  (zeta_turning_eq_t_mul_height)")])

/-! ## Panel D — the twenty-four threads as twenty-four stacked planes -/

def dCam : Cam := ⟨0.95, 0.45, 11.0, 190.0, 1330.0, 1900.0⟩

def dZk : Float := 0.155
def dScale : Float := 0.85

/-- Two hexadecimal digits for a channel in `[0,1]`. -/
def hex2 (x : Float) : String :=
  let v := (x * 255.0 + 0.5).floor
  let n := (if v < 0.0 then 0.0 else if v > 255.0 then 255.0 else v).toUInt64.toNat
  padLeft 2 '0' (String.ofList (Nat.toDigits 16 n))

/-- An `hsl`-style colour with saturation `0.68` and lightness `0.45`, as a hex string (some
SVG renderers do not accept `hsl(...)`). -/
def hueColor (hue : Float) : String :=
  let c : Float := 0.68 * (1.0 - Float.abs (2.0 * 0.45 - 1.0))
  let hp := hue / 60.0
  let x := c * (1.0 - Float.abs (hp - 2.0 * (hp / 2.0).floor - 1.0))
  let m := 0.45 - c / 2.0
  let rgb : Float × Float × Float :=
    if hp < 1.0 then (c, x, 0.0)
    else if hp < 2.0 then (x, c, 0.0)
    else if hp < 3.0 then (0.0, c, x)
    else if hp < 4.0 then (0.0, x, c)
    else if hp < 5.0 then (x, 0.0, c)
    else (c, 0.0, x)
  "#" ++ hex2 (rgb.1 + m) ++ hex2 (rgb.2.1 + m) ++ hex2 (rgb.2.2 + m)

def threadColor (a : Nat) : String :=
  hueColor (360.0 * Float.ofNat a / 24.0)

def dPlane (a : Nat) : List String :=
  let zs := dZk * Float.ofNat a
  let vs := (0.0, 0.0) :: threadVerts a 500 ss tt
  let pts : List P3 := vs.map fun z => (dScale * z.1, dScale * z.2, zs)
  let v := threadValue a 500 ss tt
  [pl3 dCam pts (threadColor a) 1.3,
   dot3 dCam (dScale * v.1, dScale * v.2, zs) 2.8 (threadColor a) "#ffffff",
   lab3 dCam (0.0, 0.0, zs) (-10.0) 4.0 9 "#64748b" "end" "400" (toString a)]

def dChain : List String :=
  let zs := dZk * 26.5
  let pts : List P3 := (threadChain 500 ss tt).map fun z => (dScale * z.1, dScale * z.2, zs)
  let fin := (threadChain 500 ss tt).getLastD (0.0, 0.0)
  [pl3 dCam pts "#0f172a" 1.7,
   dot3 dCam (dScale * fin.1, dScale * fin.2, zs) 4.0 "#0f172a" "#ffffff",
   textTag 962.0 1978.0 12 "#0f172a" "start" "700"
     ("black, on top: the 24 thread vectors added head to tail = \u2211_{n\u2264500} n^(-s) = " ++
       fmtFixed 3 fin.1 ++ (if fin.2 < 0.0 then " - " else " + ") ++
       fmtFixed 3 (Float.abs fin.2) ++ "i")]

def panelD : String :=
  String.intercalate "\n"
    ([rectTag 940.0 950.0 820.0 1080.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 962.0 990.0 18 "#0f172a" "start" "700"
        "D.  The other separation, stacked: the twenty-four threads mod 24",
      textTag 962.0 1012.0 12 "#475569" "start" "400"
        ("thread a = \u2211_{n \u2264 500, n \u2261 a (24)} n^(-s), each in its own plane z = a;" ++
          " they add back up (sum_thread)"),
      textTag 962.0 1030.0 12 "#475569" "start" "400"
        "the 24 threads are the 24 McKay\u2013Thompson twists Fourier-inverted (thread_eq_fourier)",
      seg3 dCam (0.0, 0.0, 0.0) (0.0, 0.0, dZk * 26.5) "#cbd5e1" 1.0 "4 3"] ++
     ((List.range 24).flatMap dPlane) ++ dChain ++
     [textTag 962.0 1998.0 12 "#334155" "start" "500"
        "the powers of 2 visit only the planes 2, 4, 8, 16  (two_pow_mod24_mem_four)"])

/-! ## Panel E — the fifteen factor spirals as fifteen planes, and the running product -/

def eCam : Cam := ⟨0.95, 0.50, 12.0, 135.0, 470.0, 2790.0⟩

def eZk : Float := 0.26
def eScale : Float := 0.85
def eOffL : Float := 1.45
def eOffR : Float := -1.45
/-- The two columns are centred on the mean value of what they carry. -/
def eCtrL : Float := 0.55
def eCtrR : Float := 0.80

def ePlane (i : Nat) (pe : Nat × Nat) : List String :=
  let zs := eZk * Float.ofNat i
  let col := fiberColor pe.1
  let vs := (0.0, 0.0) :: facVerts pe.1 pe.2 ss tt
  let pts : List P3 := vs.map fun z => (eOffL + eScale * (z.1 - eCtrL), eScale * z.2, zs)
  let v := facValue pe.1 pe.2 ss tt
  [pl3 eCam pts col 1.4,
   dot3 eCam (eOffL + eScale * (v.1 - eCtrL), eScale * v.2, zs) 3.0 col "#ffffff",
   lab3 eCam (eOffL - eScale * eCtrL, 0.0, zs) (-10.0) 4.0 9 col "end" "700"
     (toString pe.1 ++ (if pe.2 == 1 then "" else "^" ++ toString pe.2))]

def eRunning : List String :=
  let rp := runningProducts ss tt
  let pts : List P3 := rp.zipIdx.map fun (z, i) =>
    (eOffR + eScale * (z.1 - eCtrR), eScale * z.2, eZk * Float.ofNat i)
  let fin := rp.getLastD (0.0, 0.0)
  [pl3 eCam pts "#0f172a" 1.7] ++
  (rp.zipIdx.map fun (z, i) =>
    dot3 eCam (eOffR + eScale * (z.1 - eCtrR), eScale * z.2, eZk * Float.ofNat i) 2.6 "#0f172a"
      "#ffffff") ++
  [textTag 62.0 2938.0 12 "#0f172a" "start" "700"
     ("the top of the black path is the whole divisor sum \u2211_{d | |M|} d^(-s) = " ++
       fmtFixed 4 fin.1 ++ (if fin.2 < 0.0 then " - " else " + ") ++
       fmtFixed 4 (Float.abs fin.2) ++ "i")]

def panelE : String :=
  String.intercalate "\n"
    ([rectTag 40.0 2070.0 860.0 900.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 62.0 2110.0 18 "#0f172a" "start" "700"
        "E.  The fifteen factor spirals as fifteen planes, and the product rising through them",
      textTag 62.0 2132.0 12 "#475569" "start" "400"
        ("left: \u2211_{j \u2264 e_p} (p^j)^(-s) in the plane of its prime;  right: the running" ++
          " product 1, F\u2082, F\u2082F\u2083, \u2026 one plane per prime"),
      textTag 62.0 2150.0 12 "#475569" "start" "400"
        "MonsterSpiral.divisorSumC_eq_prod \u2014 the multiplicative separation of the Monster",
      seg3 eCam (eOffL - eScale * eCtrL, 0.0, 0.0) (eOffL - eScale * eCtrL, 0.0, eZk * 15.0)
        "#e2e8f0" 1.0 "",
      seg3 eCam (eOffR - eScale * eCtrR, 0.0, 0.0) (eOffR - eScale * eCtrR, 0.0, eZk * 15.0)
        "#e2e8f0" 1.0 ""] ++
     (mFactors.zipIdx.flatMap fun (pe, i) => ePlane i pe) ++ eRunning)

/-! ## Panel F — the surface |∑_{n ≤ K} n^{-s}| over the s-plane -/

def fCam : Cam := ⟨0.70, 0.42, 16.0, 165.0, 1310.0, 2700.0⟩

def fK : Nat := 200
def fNSig : Nat := 26
def fNT : Nat := 61

def zetaPartialF (sig t : Float) : C :=
  ((List.range fK).drop 1).foldl (fun acc n => cadd acc (termN (n + 1) sig t)) (termN 1 sig t)

def fSig (i : Nat) : Float := 0.06 + 2.34 * Float.ofNat i / Float.ofNat (fNSig - 1)
def fT (j : Nat) : Float := 40.0 * Float.ofNat j / Float.ofNat (fNT - 1)

def fPt (i j : Nat) : P3 :=
  let sig := fSig i
  let t := fT j
  let a := cabs (zetaPartialF sig t)
  let h := if a < 3.2 then a else 3.2
  (1.5 * (sig - 1.25) / 1.25, 2.0 * (t - 20.0) / 20.0, 0.42 * h)

def fSurfaceLines : List String :=
  ((List.range fNSig).map fun i =>
    pl3 fCam ((List.range fNT).map fun j => fPt i j)
      (if i == 5 then "#e6194b" else "#94a3b8") (if i == 5 then 2.0 else 0.7)) ++
  ((List.range fNT).map fun j =>
    pl3 fCam ((List.range fNSig).map fun i => fPt i j) "#c3ccd8" 0.5)

def fZeroMarks : List String :=
  ([14.134725, 21.022040, 25.010858] : List Float).flatMap fun t0 =>
    let j := (t0 * Float.ofNat (fNT - 1) / 40.0 + 0.5).floor.toUInt64.toNat
    let p := fPt 5 j
    [dot3 fCam p 4.0 "#e6194b" "#ffffff",
     seg3 fCam (p.1, p.2.1, 0.0) p "#e6194b" 0.8 "3 3",
     lab3 fCam p 7.0 (-6.0) 10 "#e6194b" "start" "600" ("t=" ++ fmtFixed 2 t0)]

def panelF : String :=
  String.intercalate "\n"
    ([rectTag 940.0 2070.0 820.0 900.0 "#ffffff" "#cbd5e1" 1.0,
      textTag 962.0 2110.0 18 "#0f172a" "start" "700"
        "F.  The landscape |\u2211_{n \u2264 200} n^(-s)| over the s-plane",
      textTag 962.0 2132.0 12 "#475569" "start" "400"
        ("\u03c3 \u2208 [0.06, 2.4] across, t \u2208 [0, 40] along;  the red rib is the critical line" ++
          " \u03c3 = 1/2, whose dips are the first three zeros of \u03b6"),
      textTag 962.0 2150.0 12 "#475569" "start" "400"
        ("this is the same helix seen as a function of s: the height here is |H| summed," ++
          " the height in A\u2013C is log n"),
      seg3 fCam (-1.5, -2.0, 0.0) (1.5, -2.0, 0.0) "#0f172a" 1.0 "",
      seg3 fCam (-1.5, -2.0, 0.0) (-1.5, 2.0, 0.0) "#0f172a" 1.0 "",
      lab3 fCam (1.5, -2.0, 0.0) 6.0 14.0 11 "#0f172a" "start" "600" "\u03c3 = 2.4",
      lab3 fCam (-1.5, 2.0, 0.0) (-6.0) 14.0 11 "#0f172a" "end" "600" "t = 40"] ++
     fSurfaceLines ++ fZeroMarks)

/-! ## The document -/

def monsterSpiral3dSvg : String :=
  let width : Float := 1800.0
  let height : Float := 3020.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 62.0 54.0 24 "#0f172a" "start" "700"
    "The same picture in three dimensions: height = log n" ++ "\n" ++
  textTag 62.0 84.0 15 "#334155" "start" "400"
    ("Give the term n^(-s) the height log n.  At s = \u03c3 + it it becomes the point" ++
      " (Re, Im, log n) of the single curve H(z) = e^(-(\u03c3+it)z): a conical helix on the" ++
      " horn r = e^(-\u03c3z), turning t radians per unit of height.") ++ "\n" ++
  textTag 62.0 108.0 15 "#334155" "start" "400"
    ("Every object of this project is then a set of heights on that one curve: a prime p is" ++
      " the progression j\u00b7log p, the Monster is the 424 488 960 heights log d (d | |M|),") ++
    "\n" ++
  textTag 62.0 130.0 15 "#334155" "start" "400"
    ("and the twenty-six sporadic groups are twenty-six rungs up to log|M| = 124.13.") ++
    "\n" ++
  panelA ++ "\n" ++ panelB ++ "\n" ++ panelC ++ "\n" ++ panelD ++ "\n" ++ panelE ++ "\n" ++
  panelF ++ "\n" ++
  "</svg>\n"

/-! ## The Wavefront OBJ export -/

def objPoly (start : Nat) (pts : List P3) : String × Nat :=
  let vs := String.intercalate "\n" (pts.map fun p =>
    "v " ++ fmtFixed 6 p.1 ++ " " ++ fmtFixed 6 p.2.1 ++ " " ++ fmtFixed 6 p.2.2)
  let idx := String.intercalate " " ((List.range pts.length).map fun i => toString (start + i))
  (vs ++ "\nl " ++ idx ++ "\n", start + pts.length)

/-- The curves as 3D polylines: the universal helix on the true horn, the horn's rings and
meridians, and the Monster's fifteen prime ladders on the unrolled cone. -/
def monsterSpiral3dObj : String :=
  let curves : List (String × List P3) :=
    [("helix", (List.range 1601).map fun k =>
        let z := 8.0 * Float.ofNat k / 1600.0
        hornPt 1.0 z (ang z))] ++
    ((List.range 9).map fun i =>
      let z := Float.ofNat i
      ("horn_ring_" ++ toString i,
        (ring 1.0 0.0 72).map fun q =>
          (q.1 * Float.exp (-(ss * z)), q.2.1 * Float.exp (-(ss * z)), z))) ++
    ((List.range 8).map fun i =>
      let th := 6.283185307179586 * Float.ofNat i / 8.0
      ("horn_meridian_" ++ toString i,
        (List.range 41).map fun k => hornPt 1.0 (8.0 * Float.ofNat k / 40.0) th)) ++
    [("cone_helix", (List.range 4001).map fun k =>
        let z := 32.0 * Float.ofNat k / 4000.0
        conePt 1.0 32.0 bShrink z (ang z))] ++
    (mFactors.map fun pe =>
      ("ladder_" ++ toString pe.1,
        (List.range (pe.2 + 1)).map fun j =>
          let z := Float.ofNat j * Float.log (Float.ofNat pe.1)
          conePt 1.0 32.0 bShrink z (ang z)))
  let body := (curves.foldl (fun (acc : String × Nat) c =>
    let (s, n) := objPoly acc.2 c.2
    (acc.1 ++ "o " ++ c.1 ++ "\n" ++ s, n)) ("", 1)).1
  "# The universal helix H(z) = e^(-(1/2 + 14.134725 i) z) and the Monster's prime ladders\n" ++
  "# generated by RequestProject/MonsterSpiral3DSvg.lean\n" ++ body

/-! ## The table of marked points -/

def monsterSpiral3dCsv : String :=
  let hdr := "object,label,height_z,log_radius,radius,angle_rad,turns,dir_x,dir_y,x,y,z\n"
  let row (obj lab : String) (z : Float) : String :=
    let r := Float.exp (-(ss * z))
    let a := ang z
    obj ++ "," ++ lab ++ "," ++ fmtFixed 6 z ++ "," ++ fmtFixed 6 (-(ss * z)) ++ "," ++
      fmtFixed 8 r ++ "," ++ fmtFixed 6 a ++ "," ++ fmtFixed 4 (-a / twoPi) ++ "," ++
      fmtFixed 8 (Float.cos a) ++ "," ++ fmtFixed 8 (Float.sin a) ++ "," ++
      fmtFixed 8 (r * Float.cos a) ++ "," ++ fmtFixed 8 (r * Float.sin a) ++ "," ++
      fmtFixed 6 z
  let twoRows := (List.range 47).map fun k =>
    row "two_fiber" ("2^" ++ toString k) (Float.ofNat k * Float.log 2.0)
  let primeRows := mFactors.map fun pe =>
    row "prime_segment" (toString pe.1 ++ "^" ++ toString pe.2)
      (Float.ofNat pe.2 * Float.log (Float.ofNat pe.1))
  let groupRows := sortedGroups.map fun G => row "sporadic_group" G.name (gHeight G)
  hdr ++ String.intercalate "\n" (twoRows ++ primeRows ++ groupRows) ++ "\n"

/-! ## The rotatable scene -/

def jsonPts (pts : List P3) : String :=
  "[" ++ String.intercalate "," (pts.map fun p =>
    "[" ++ fmtFixed 4 p.1 ++ "," ++ fmtFixed 4 p.2.1 ++ "," ++ fmtFixed 4 p.2.2 ++ "]") ++ "]"

def jsonLayer (name kind col : String) (w : Float) (pts : List P3) : String :=
  "{\"name\":\"" ++ name ++ "\",\"kind\":\"" ++ kind ++ "\",\"color\":\"" ++ col ++
    "\",\"w\":" ++ fmtFixed 2 w ++ ",\"pts\":" ++ jsonPts pts ++ "}"

/-- Scene 1: the true horn, with the universal helix, the horn wireframe, and the terms
`n ≤ 400` (the divisors of `|M|` singled out). -/
def sceneHorn : String :=
  let hz : Float := 0.42
  let helix := jsonLayer "universal helix H(z)" "line" "#1d4ed8" 1.6
    ((List.range 2401).map fun k =>
      let z := 8.0 * Float.ofNat k / 2400.0
      hornPt hz z (ang z))
  let rings := String.intercalate "," ((List.range 9).map fun i =>
    let z := Float.ofNat i
    jsonLayer "horn wireframe" "line" "#cbd5e1" 0.8
      ((ring 1.0 0.0 72).map fun q =>
        (q.1 * Float.exp (-(ss * z)), q.2.1 * Float.exp (-(ss * z)), hz * z)))
  let meridians := String.intercalate "," ((List.range 8).map fun i =>
    let th := 6.283185307179586 * Float.ofNat i / 8.0
    jsonLayer "horn wireframe" "line" "#e2e8f0" 0.8
      ((List.range 41).map fun k => hornPt hz (8.0 * Float.ofNat k / 40.0) th))
  let terms := jsonLayer "terms n \\u2264 400" "dots" "#94a3b8" 2.0
    (((List.range 400).drop 1).map fun n =>
      let z := Float.log (Float.ofNat (n + 1))
      hornPt hz z (ang z))
  let divs := jsonLayer "divisors of |M|" "dots" "#e6194b" 3.4
    ((((List.range 400).drop 1).filter fun n => dividesMonster (n + 1)).map fun n =>
      let z := Float.log (Float.ofNat (n + 1))
      hornPt hz z (ang z))
  let axis := jsonLayer "axis" "line" "#0f172a" 1.0 [(0.0, 0.0, 0.0), (0.0, 0.0, hz * 8.0)]
  "{\"name\":\"true horn  r = e^(-z/2),  z = log n \\u2264 8\",\"layers\":[" ++
    String.intercalate "," [helix, rings, meridians, terms, divs, axis] ++ "]}"

/-- Scene 2: the unrolled cone, carrying the Monster's fifteen prime ladders and the twenty-six
sporadic heights, up to `log|M| = 124.13`. -/
def sceneCone : String :=
  let zk : Float := 0.026
  let zmax : Float := 125.0
  let helix := jsonLayer "universal helix (unrolled)" "line" "#93a7c4" 0.7
    ((List.range 12001).map fun k =>
      let z := 32.0 * Float.ofNat k / 12000.0
      conePt zk zmax 0.8 z (ang z))
  let ladders := String.intercalate "," (mFactors.map fun pe =>
    jsonLayer "prime ladders (110 heights)" "dots" (fiberColor pe.1) 3.2
      ((List.range (pe.2 + 1)).map fun j =>
        let z := Float.ofNat j * Float.log (Float.ofNat pe.1)
        conePt zk zmax 0.8 z (ang z)))
  let towerSegs := String.intercalate "," (mFactors.zipIdx.map fun (pe, i) =>
    jsonLayer "tower of prime heights" "line" (fiberColor pe.1) 6.0
      [(0.0, 0.0, zk * cumHeights.getD i 0.0), (0.0, 0.0, zk * cumHeights.getD (i + 1) 0.0)])
  let groupRings := String.intercalate "," (sortedGroups.map fun G =>
    jsonLayer "sporadic heights" "line" "#a8b4c4" 0.7
      ((ring 1.0 0.0 64).map fun q =>
        let r := 1.0 - 0.8 * gHeight G / zmax
        (q.1 * r, q.2.1 * r, zk * gHeight G)))
  "{\"name\":\"unrolled cone  log r = -z/2,  z = log n \\u2264 log|M| = 124.13\",\"layers\":[" ++
    String.intercalate "," [helix, ladders, towerSegs, groupRings] ++ "]}"

/-- A self-contained rotatable view of the two scenes: drag to turn, wheel to zoom, checkboxes
to toggle the layers. -/
def monsterSpiral3dHtml : String :=
  let data := "[" ++ sceneHorn ++ "," ++ sceneCone ++ "]"
  "<!DOCTYPE html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\"/>\n" ++
  "<title>The Monster and the zeta helix in 3D</title>\n<style>\n" ++
  "body{margin:0;font-family:ui-monospace,SFMono-Regular,Menlo,monospace;background:#ffffff;" ++
  "color:#0f172a}#bar{padding:10px 16px;border-bottom:1px solid #cbd5e1;font-size:13px}" ++
  "#legend{padding:8px 16px;font-size:12px;color:#334155}canvas{display:block;cursor:grab}" ++
  "label{margin-right:14px}\n</style>\n</head>\n<body>\n" ++
  "<div id=\"bar\"><b>height z = log n</b> &nbsp; the term n^(-s) is the point " ++
  "H(z) = e^(-(1/2 + 14.134725 i) z) &nbsp;|&nbsp; drag to rotate, wheel to zoom " ++
  "&nbsp;|&nbsp; scene: <select id=\"scene\"></select></div>\n" ++
  "<div id=\"legend\"></div>\n<canvas id=\"c\"></canvas>\n<script>\n" ++
  "const DATA = " ++ data ++ ";\n" ++
  "const cv = document.getElementById('c'), ctx = cv.getContext('2d');\n" ++
  "let az = 0.85, el = 0.30, zoom = 1.0, cur = 0, off = 0.0;\n" ++
  "const sel = document.getElementById('scene');\n" ++
  "DATA.forEach((s,i)=>{const o=document.createElement('option');o.value=i;" ++
  "o.textContent=s.name;sel.appendChild(o);});\n" ++
  "sel.onchange = e => { cur = +e.target.value; buildLegend(); draw(); };\n" ++
  "let hidden = {};\n" ++
  "function names(){const n=[];DATA[cur].layers.forEach(l=>{if(!n.includes(l.name))n.push(l.name);});" ++
  "return n;}\n" ++
  "function buildLegend(){const d=document.getElementById('legend');d.innerHTML='';" ++
  "names().forEach(n=>{const l=document.createElement('label');const b=document.createElement('input');" ++
  "b.type='checkbox';b.checked=!hidden[n];b.onchange=()=>{hidden[n]=!b.checked;draw();};" ++
  "l.appendChild(b);l.appendChild(document.createTextNode(' '+n));d.appendChild(l);});}\n" ++
  "function resize(){cv.width=window.innerWidth;cv.height=window.innerHeight-96;draw();}\n" ++
  "function proj(p){const ca=Math.cos(az),sa=Math.sin(az),ce=Math.cos(el),se=Math.sin(el);\n" ++
  " const x=p[0],y=p[1],z=p[2]-off;\n" ++
  " const rx=-sa*x+ca*y, uy=-(se*ca)*x-(se*sa)*y+ce*z, dp=(ce*ca)*x+(ce*sa)*y+se*z;\n" ++
  " const D=9.0, f=D/(D-dp), s=Math.min(cv.width,cv.height)*0.26*zoom;\n" ++
  " return [cv.width/2+s*f*rx, cv.height/2-s*f*uy];}\n" ++
  "function draw(){ctx.clearRect(0,0,cv.width,cv.height);\n" ++
  " const sc=DATA[cur]; off = 1.6;\n" ++
  " sc.layers.forEach(l=>{ if(hidden[l.name]) return;\n" ++
  "  if(l.kind==='dots'){ctx.fillStyle=l.color;l.pts.forEach(p=>{const q=proj(p);" ++
  "ctx.beginPath();ctx.arc(q[0],q[1],l.w,0,6.283185);ctx.fill();});}\n" ++
  "  else {ctx.strokeStyle=l.color;ctx.lineWidth=l.w;ctx.beginPath();" ++
  "l.pts.forEach((p,i)=>{const q=proj(p);if(i===0)ctx.moveTo(q[0],q[1]);else ctx.lineTo(q[0],q[1]);});" ++
  "ctx.stroke();}\n" ++
  " });}\n" ++
  "let drag=false,lx=0,ly=0;\n" ++
  "cv.addEventListener('mousedown',e=>{drag=true;lx=e.clientX;ly=e.clientY;});\n" ++
  "window.addEventListener('mouseup',()=>{drag=false;});\n" ++
  "window.addEventListener('mousemove',e=>{if(!drag)return;az+=(e.clientX-lx)*0.008;" ++
  "el+=(e.clientY-ly)*0.006;el=Math.max(-1.4,Math.min(1.4,el));lx=e.clientX;ly=e.clientY;draw();});\n" ++
  "cv.addEventListener('wheel',e=>{e.preventDefault();zoom*=Math.exp(-e.deltaY*0.001);draw();}," ++
  "{passive:false});\n" ++
  "window.addEventListener('resize',resize);\nbuildLegend();resize();\n" ++
  "</script>\n</body>\n</html>\n"

end MonsterSpiral3DSvg

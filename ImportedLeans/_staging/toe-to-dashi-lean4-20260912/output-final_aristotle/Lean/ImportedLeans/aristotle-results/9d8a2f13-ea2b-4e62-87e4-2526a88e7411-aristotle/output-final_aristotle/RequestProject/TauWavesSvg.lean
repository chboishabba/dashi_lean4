/-
# The four three-dimensional views of the fibers of `2` and `3`

Renders the surfaces of `RequestProject/TauWaves.lean` — the smoothed fibers of
`visualization/modular-tau-2-and-3.svg` — as four axonometric panels:

```
view 2      S₂(u,v) = w₂(u)              the fiber of 2, extruded along v
view 3      S₃(u,v) = w₃(v)              the fiber of 3, extruded along u
view 2+3    S₊(u,v) = w₂(u) + w₃(v)      constructive interference
view 2-3    S₋(u,v) = w₂(u) - w₃(v)      destructive interference
```

Here `u` is the height along the fiber of `2` (so `u = k` is the plotted point `n = 2^k` of the
flat picture) and `v` the height along the fiber of `3` (`v = k` is `n = 3^k`), and
`w_p(u) = sin((u+1)θ_p)/sin θ_p` is the wave of `TauWaves.wave`, which passes through every
plotted point of the fiber of `p` (`TauWaves.wave_eq_normTau_two`,
`TauWaves.wave_eq_normTau_three`).

Outputs:

* `visualization/modular-tau-waves-3d.svg` — the four panels;
* `visualization/modular-tau-waves-3d.html` — the same four surfaces, rotatable;
* `visualization/modular_tau_waves.csv` — the sampled heights.

Only floating-point geometry and string manipulation live here; everything asserted on the
pictures (the interpolation, the recovery identities `S₊ ± S₋`, the periods, the amplitude
bounds, the nodal locus and the Helmholtz equation) is proved in `RequestProject/TauWaves.lean`.
-/
import RequestProject.TauWaves
import RequestProject.SporadicSvg

namespace TauWavesSvg

open SporadicSvg

set_option autoImplicit false

/-! ## The two waves, numerically -/

/-- `τ(2)/(2·2^{11/2})`, the Satake parameter of the fiber of `2`. -/
def cos2 : Float := -24.0 / (2.0 * Float.sqrt 2048.0)

/-- `τ(3)/(2·3^{11/2})`, the Satake parameter of the fiber of `3`. -/
def cos3 : Float := 252.0 / (2.0 * Float.sqrt 177147.0)

/-- The Satake angle `θ₂ = arccos(τ(2)/2·2^{11/2}) ≈ 1.83917`. -/
def th2 : Float := Float.acos cos2

/-- The Satake angle `θ₃ = arccos(τ(3)/2·3^{11/2}) ≈ 1.26677`. -/
def th3 : Float := Float.acos cos3

/-- The smoothed fiber of `2`: `w₂(u) = sin((u+1)θ₂)/sin θ₂`. -/
def w2 (u : Float) : Float := Float.sin ((u + 1.0) * th2) / Float.sin th2

/-- The smoothed fiber of `3`: `w₃(v) = sin((v+1)θ₃)/sin θ₃`. -/
def w3 (v : Float) : Float := Float.sin ((v + 1.0) * th3) / Float.sin th3

/-! ## Colour helpers -/

private def clampByte (x : Float) : Nat :=
  let y := if x < 0.0 then 0.0 else if x > 255.0 then 255.0 else x
  y.toUInt64.toNat

private def hex2 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 (min n 255))
  if s.length = 1 then "0" ++ s else s

private def rgbStr (r g b : Float) : String :=
  "#" ++ hex2 (clampByte r) ++ hex2 (clampByte g) ++ hex2 (clampByte b)

/-- A colour of the panel's ramp: `t = 0` is the low colour, `t = 1` the high one, scaled by the
lighting factor `s`. -/
private def ramp (lo hi : Float × Float × Float) (t s : Float) : String :=
  let t := if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t
  rgbStr (s * (lo.1 + (hi.1 - lo.1) * t)) (s * (lo.2.1 + (hi.2.1 - lo.2.1) * t))
    (s * (lo.2.2 + (hi.2.2 - lo.2.2) * t))

/-! ## Geometry -/

/-- Horizontal pixels per unit of height along a fiber. -/
def sxy : Float := 44.0

/-- Vertical pixels per unit of `τ(p^k)/p^{11k/2}` — the same scale in all four panels, so the
interference views are directly comparable with the two pure ones. -/
def sz : Float := 58.0

/-- The largest displayed height along the fiber of `2` (`2^8 = 256`). -/
def uMax : Float := 8.0

/-- The largest displayed height along the fiber of `3` (`3^5 = 243`). -/
def vMax : Float := 5.0

/-- Axonometric projection of `(u, v, z)` into the panel with centre `(ox, oy)`. -/
def proj (ox oy u v z : Float) : Float × Float :=
  let x := u - uMax / 2.0
  let y := v - vMax / 2.0
  (ox + (x - y) * 0.8660254 * sxy, oy + (x + y) * 0.5 * sxy - z * sz)

/-- Depth key for the painter's algorithm: larger is nearer the viewer. -/
def depth (u v : Float) : Float := u + v

private def polygonTag (pts : List (Float × Float)) (fill stroke : String) (sw : Float) :
    String :=
  "  <polygon " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++ " " ++
    attr "fill" fill ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt sw) ++ " " ++ attr "stroke-linejoin" "round" ++ "/>"

/-! ## The panels -/

/-- One view: a surface over the square of heights, with its own colour ramp. -/
structure Panel where
  key : String
  title : String
  eqn : String
  note : String
  f : Float → Float → Float
  lo : Float × Float × Float
  hi : Float × Float × Float
  ox : Float
  oy : Float

def panelTwo : Panel where
  key := "2"
  title := "view 2 \u2014 the fiber of 2"
  eqn := "z = w\u2082(u) = sin((u+1)\u03b8\u2082)/sin \u03b8\u2082"
  note := "\u03b8\u2082 = arccos(\u03c4(2)/2\u00b72^(11/2)) = 1.83917,  period 2\u03c0/\u03b8\u2082 = 3.4163 in u"
  f := fun u _ => w2 u
  lo := (254.0, 226.0, 226.0)
  hi := (153.0, 27.0, 27.0)
  ox := 452.0
  oy := 505.0

def panelThree : Panel where
  key := "3"
  title := "view 3 \u2014 the fiber of 3"
  eqn := "z = w\u2083(v) = sin((v+1)\u03b8\u2083)/sin \u03b8\u2083"
  note := "\u03b8\u2083 = arccos(\u03c4(3)/2\u00b73^(11/2)) = 1.26677,  period 2\u03c0/\u03b8\u2083 = 4.9599 in v"
  f := fun _ v => w3 v
  lo := (219.0, 234.0, 254.0)
  hi := (29.0, 78.0, 216.0)
  ox := 1252.0
  oy := 505.0

def panelSum : Panel where
  key := "2+3"
  title := "view 2+3 \u2014 constructive interference"
  eqn := "z = w\u2082(u) + w\u2083(v)"
  note := "crests add where both fibers are high; |z| \u2264 1/sin \u03b8\u2082 + 1/sin \u03b8\u2083 = 2.085"
  f := fun u v => w2 u + w3 v
  lo := (237.0, 233.0, 254.0)
  hi := (91.0, 33.0, 182.0)
  ox := 452.0
  oy := 1150.0

def panelDiff : Panel where
  key := "2-3"
  title := "view 2\u22123 \u2014 destructive interference"
  eqn := "z = w\u2082(u) \u2212 w\u2083(v)"
  note := "the white curve is the nodal set w\u2082(u) = w\u2083(v): the two fibers cancel exactly"
  f := fun u v => w2 u - w3 v
  lo := (209.0, 250.0, 229.0)
  hi := (4.0, 120.0, 87.0)
  ox := 1252.0
  oy := 1150.0

def panels : List Panel := [panelTwo, panelThree, panelSum, panelDiff]

/-! ## The mesh -/

/-- Quads across the fiber-of-`2` direction. -/
def nu : Nat := 36

/-- Quads across the fiber-of-`3` direction. -/
def nv : Nat := 26

def uAt (i : Nat) : Float := uMax * Float.ofNat i / Float.ofNat nu
def vAt (j : Nat) : Float := vMax * Float.ofNat j / Float.ofNat nv

/-- The largest `|z|` over the panel's domain, used to normalise its colour ramp. -/
def ampOf (P : Panel) : Float :=
  ((List.range (nu + 1)).flatMap fun i =>
      (List.range (nv + 1)).map fun j => (P.f (uAt i) (vAt j)).abs).foldl
    (fun a b => if a < b then b else a) 0.001

/-- Lambert shading from the surface gradient. -/
def shade (P : Panel) (u v : Float) : Float :=
  let h := 0.05
  let du := (P.f (u + h) v - P.f (u - h) v) / (2.0 * h)
  let dv := (P.f u (v + h) - P.f u (v - h)) / (2.0 * h)
  let nx := -du
  let ny := -dv
  let nz := 1.0
  let len := Float.sqrt (nx * nx + ny * ny + nz * nz)
  let d := (nx * 0.42 + ny * 0.35 + nz * 0.84) / len
  let d := if d < 0.0 then 0.0 else d
  0.58 + 0.42 * d

/-- One quad of the mesh, with its depth key. -/
def quadOf (P : Panel) (amp : Float) (i j : Nat) : Float × String :=
  let u0 := uAt i
  let u1 := uAt (i + 1)
  let v0 := vAt j
  let v1 := vAt (j + 1)
  let z00 := P.f u0 v0
  let z10 := P.f u1 v0
  let z11 := P.f u1 v1
  let z01 := P.f u0 v1
  let uc := (u0 + u1) / 2.0
  let vc := (v0 + v1) / 2.0
  let zc := (z00 + z10 + z11 + z01) / 4.0
  let t := (zc / amp + 1.0) / 2.0
  let col := ramp P.lo P.hi t (shade P uc vc)
  (depth uc vc,
    polygonTag [proj P.ox P.oy u0 v0 z00, proj P.ox P.oy u1 v0 z10,
      proj P.ox P.oy u1 v1 z11, proj P.ox P.oy u0 v1 z01] col col 0.5)

/-- The whole surface together with the marks that lie on it (dots, nodal points), drawn
far-to-near so that near crests hide what is behind them. -/
def surfaceSvg (P : Panel) (marks : List (Float × String)) : String :=
  let amp := ampOf P
  let quads := (List.range nu).flatMap fun i =>
    (List.range nv).map fun j => quadOf P amp i j
  let sorted := (quads ++ marks).mergeSort (fun a b => a.1 ≤ b.1)
  String.intercalate "\n" (sorted.map (fun q => q.2))

/-! ## Frame, sample points and nodal curves -/

/-- The floor rectangle `z = 0` and its two labelled edges. -/
def frameSvg (P : Panel) : String :=
  let p := proj P.ox P.oy
  let corner := [p 0.0 0.0 0.0, p uMax 0.0 0.0, p uMax vMax 0.0, p 0.0 vMax 0.0, p 0.0 0.0 0.0]
  let uticks := (List.range 9).map fun k =>
    let u := Float.ofNat k
    let a := p u 0.0 0.0
    let b := p u (-0.28) 0.0
    lineTag a.1 a.2 b.1 b.2 "#94a3b8" 0.9 "" ++ "\n" ++
      textTag (b.1 - 4.0) (b.2 + 12.0) 11 "#64748b" "end" "500" ("2^" ++ toString k)
  let vticks := (List.range 6).map fun k =>
    let v := Float.ofNat k
    let a := p 0.0 v 0.0
    let b := p (-0.28) v 0.0
    lineTag a.1 a.2 b.1 b.2 "#94a3b8" 0.9 "" ++ "\n" ++
      textTag (b.1 + 5.0) (b.2 + 12.0) 11 "#64748b" "start" "500" ("3^" ++ toString k)
  let zaxis :=
    let a := p 0.0 0.0 (-2.2)
    let b := p 0.0 0.0 2.2
    lineTag a.1 a.2 b.1 b.2 "#cbd5e1" 1.0 "3 3"
  String.intercalate "\n"
    (polylineTag corner "#94a3b8" 1.1 :: zaxis :: (uticks ++ vticks))

/-- The plotted points of `modular-tau-2-and-3.svg`, lifted onto the surface: the lattice of
integer heights `(j, k)`, i.e. the pairs `(2^j, 3^k)`. -/
def latticeMarks (P : Panel) (col : String) : List (Float × String) :=
  (List.range 9).flatMap fun j =>
    (List.range 6).map fun k =>
      let u := Float.ofNat j
      let v := Float.ofNat k
      let q := proj P.ox P.oy u v (P.f u v)
      (depth u v + 0.02, circleTag q.1 q.2 3.0 col "#ffffff")

/-- The section curve of the surface at `v = v₀` (a copy of the fiber of `2`). -/
def uCurve (P : Panel) (v0 : Float) (col : String) (width : Float) : String :=
  polylineTag ((List.range 161).map fun i =>
    let u := uMax * Float.ofNat i / 160.0
    proj P.ox P.oy u v0 (P.f u v0)) col width

/-- The section curve of the surface at `u = u₀` (a copy of the fiber of `3`). -/
def vCurve (P : Panel) (u0 : Float) (col : String) (width : Float) : String :=
  polylineTag ((List.range 161).map fun j =>
    let v := vMax * Float.ofNat j / 160.0
    proj P.ox P.oy u0 v (P.f u0 v)) col width

/-- Points of the nodal set `z = 0` of the panel, found by sign changes along `v`. -/
def nodalMarks (P : Panel) (col : String) : List (Float × String) :=
  (List.range 193).flatMap fun i =>
    let u := uMax * Float.ofNat i / 192.0
    (List.range 240).filterMap fun j =>
      let v0 := vMax * Float.ofNat j / 240.0
      let v1 := vMax * Float.ofNat (j + 1) / 240.0
      let a := P.f u v0
      let b := P.f u v1
      if (a ≤ 0.0 && b > 0.0) || (a ≥ 0.0 && b < 0.0) then
        let v := v0 + (v1 - v0) * (a / (a - b))
        let q := proj P.ox P.oy u v 0.0
        some (depth u v + 0.01, circleTag q.1 q.2 1.5 col col)
      else none

/-! ## Panel assembly -/

def panelBody (P : Panel) : String :=
  let markCol :=
    if P.key = "2" then "#b91c1c"
    else if P.key = "3" then "#1d4ed8"
    else if P.key = "2+3" then "#6d28d9" else "#047857"
  let marks : List (Float × String) :=
    if P.key = "2" then
      (List.range 9).map fun k =>
        let u := Float.ofNat k
        let q := proj P.ox P.oy u 0.0 (w2 u)
        (depth u 0.0 + 0.02, circleTag q.1 q.2 4.0 "#b91c1c" "#ffffff")
    else if P.key = "3" then
      (List.range 6).map fun k =>
        let v := Float.ofNat k
        let q := proj P.ox P.oy uMax v (w3 v)
        (depth uMax v + 0.02, circleTag q.1 q.2 4.0 "#1d4ed8" "#ffffff")
    else nodalMarks P "#ffffff" ++ latticeMarks P markCol
  let curves :=
    if P.key = "2" then
      uCurve P 0.0 "#7f1d1d" 2.0 ++ "\n" ++
        String.intercalate "\n" ((List.range 9).map fun k =>
          let u := Float.ofNat k
          let q := proj P.ox P.oy u 0.0 (w2 u)
          textTag q.1 (q.2 - 11.0) 10 "#7f1d1d" "middle" "600" (fmtFixed 3 (w2 u)))
    else if P.key = "3" then
      vCurve P uMax "#1e3a8a" 2.0 ++ "\n" ++
        String.intercalate "\n" ((List.range 6).map fun k =>
          let v := Float.ofNat k
          let q := proj P.ox P.oy uMax v (w3 v)
          textTag (q.1 + 8.0) (q.2 - 8.0) 10 "#1e3a8a" "start" "600" (fmtFixed 3 (w3 v)))
    else
      uCurve P 0.0 "#1f2937" 1.3 ++ "\n" ++ vCurve P uMax "#1f2937" 1.3
  String.intercalate "\n"
    [ textTag (P.ox - 380.0) (P.oy - 300.0) 17 "#0f172a" "start" "700" P.title,
      textTag (P.ox - 380.0) (P.oy - 279.0) 13 markCol "start" "600" P.eqn,
      frameSvg P,
      surfaceSvg P marks,
      curves,
      textTag (P.ox - 380.0) (P.oy + 268.0) 12 "#475569" "start" "400" P.note,
      textTag (P.ox - 380.0) (P.oy + 286.0) 11 "#64748b" "start" "400"
        ("u = height along the fiber of 2 (u = k is n = 2^k),  " ++
          "v = height along the fiber of 3 (v = k is n = 3^k)") ]

/-! ## The document -/

def headerSvg : String :=
  String.intercalate "\n"
    [ textTag 72.0 58.0 25 "#0f172a" "start" "700"
        ("Smoothing modular-tau-2-and-3.svg: the fibers of 2 and 3 as surfaces, and their" ++
          " interference"),
      textTag 72.0 88.0 14 "#334155" "start" "400"
        ("Along the fiber of a prime p the Hecke recursion makes the Deligne-normalised" ++
          " coefficients \u03c4(p^k)/p^(11k/2) a sampled sine wave:"),
      textTag 72.0 110.0 14 "#334155" "start" "400"
        ("\u03c4(p^k)/p^(11k/2) = sin((k+1)\u03b8_p)/sin \u03b8_p  with  cos \u03b8_p =" ++
          " \u03c4(p)/(2p^(11/2))   (TauWaves.wave_eq_normTau_two / _three)."),
      textTag 72.0 132.0 14 "#334155" "start" "400"
        ("The four panels are the two waves and their sum and difference over the square of" ++
          " heights (u, v); all four solve \u03b8\u2082\u207b\u00b2\u2202\u00b2z/\u2202u\u00b2" ++
          " + \u03b8\u2083\u207b\u00b2\u2202\u00b2z/\u2202v\u00b2 = \u2212z."),
      textTag 72.0 154.0 13 "#64748b" "start" "400"
        ("Dots mark the points actually plotted in the flat picture; heights are drawn to one" ++
          " common vertical scale.") ]

def footerSvg : String :=
  String.intercalate "\n"
    [ textTag 72.0 1470.0 13 "#334155" "start" "600"
        "Proved in RequestProject/TauWaves.lean:",
      textTag 72.0 1492.0 12 "#475569" "start" "400"
        ("wave_eq_normTau_two / _three \u2014 the smooth waves pass through every plotted point" ++
          " of the two fibers (2^k \u2264 256, 3^k \u2264 243);"),
      textTag 72.0 1512.0 12 "#475569" "start" "400"
        ("sum_add_diff / sum_sub_diff \u2014 (2+3) + (2\u22123) = 2\u00b7(view 2) and (2+3)" ++
          " \u2212 (2\u22123) = 2\u00b7(view 3): the interference views carry both fibers;"),
      textTag 72.0 1532.0 12 "#475569" "start" "400"
        ("diffSurface_eq_zero_iff \u2014 the white nodal curve is exactly {w\u2082(u) =" ++
          " w\u2083(v)};  abs_sumSurface_le / abs_diffSurface_le \u2014 |z| \u2264 2.085;"),
      textTag 72.0 1552.0 12 "#475569" "start" "400"
        ("sumSurface_helmholtz / diffSurface_helmholtz / twoSurface_helmholtz /" ++
          " threeSurface_helmholtz \u2014 one standing-wave equation for all four views.") ]

/-- The four-panel figure. -/
def wavesSvg : String :=
  let width := 1680.0
  let height := 1600.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  headerSvg ++ "\n" ++
  String.intercalate "\n" (panels.map panelBody) ++ "\n" ++
  footerSvg ++ "\n</svg>\n"

/-! ## Data -/

/-- The sampled heights of the four views on a quarter-integer grid. -/
def wavesCsv : String :=
  let header := "u,v,w2_u,w3_v,sum,diff\n"
  let rows := (List.range 33).flatMap fun i =>
    (List.range 21).map fun j =>
      let u := Float.ofNat i / 4.0
      let v := Float.ofNat j / 4.0
      String.intercalate ","
        [fmtFixed 2 u, fmtFixed 2 v, fmtFixed 6 (w2 u), fmtFixed 6 (w3 v),
          fmtFixed 6 (w2 u + w3 v), fmtFixed 6 (w2 u - w3 v)] ++ "\n"
  header ++ String.join rows

/-! ## The rotatable version -/

/-- A self-contained page showing the same four surfaces, rotatable with the mouse. -/
def wavesHtml : String :=
"<!DOCTYPE html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\"/>
<title>Fibers of 2 and 3 as surfaces: interference</title>
<style>
 body { margin:0; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; color:#0f172a;
        background:#ffffff; }
 h1 { font-size:19px; margin:16px 20px 4px; }
 p  { font-size:13px; margin:2px 20px; color:#334155; }
 #grid { display:grid; grid-template-columns:1fr 1fr; gap:8px; padding:12px 20px 24px; }
 .cell { border:1px solid #e2e8f0; border-radius:8px; padding:6px; }
 .cap { font-size:13px; font-weight:600; margin:2px 6px 6px; }
 canvas { width:100%; height:420px; display:block; cursor:grab; }
</style>
</head>
<body>
<h1>Smoothing the fibers of 2 and 3 into surfaces, and their interference</h1>
<p>w<sub>p</sub>(x) = sin((x+1)&theta;<sub>p</sub>)/sin &theta;<sub>p</sub>, with
   cos &theta;<sub>p</sub> = &tau;(p)/(2p<sup>11/2</sup>); at integer x the wave equals the
   plotted coefficient &tau;(p<sup>x</sup>)/p<sup>11x/2</sup>.</p>
<p>Drag any panel to rotate (all four turn together); wheel to zoom.</p>
<div id=\"grid\"></div>
<script>
const TH2 = Math.acos(-24/(2*Math.pow(2,5.5)));
const TH3 = Math.acos(252/(2*Math.pow(3,5.5)));
const w2 = u => Math.sin((u+1)*TH2)/Math.sin(TH2);
const w3 = v => Math.sin((v+1)*TH3)/Math.sin(TH3);
const views = [
 {name:'view 2 \\u2014 fiber of 2:  z = w\\u2082(u)', f:(u,v)=>w2(u), lo:[254,226,226], hi:[153,27,27]},
 {name:'view 3 \\u2014 fiber of 3:  z = w\\u2083(v)', f:(u,v)=>w3(v), lo:[219,234,254], hi:[29,78,216]},
 {name:'view 2+3 \\u2014 constructive:  z = w\\u2082(u)+w\\u2083(v)', f:(u,v)=>w2(u)+w3(v), lo:[237,233,254], hi:[91,33,182]},
 {name:'view 2\\u22123 \\u2014 destructive:  z = w\\u2082(u)\\u2212w\\u2083(v)', f:(u,v)=>w2(u)-w3(v), lo:[209,250,229], hi:[4,120,87]}
];
let az = 0.7, el = 0.55, zoom = 1.0;
const NU = 40, NV = 30, UMAX = 8, VMAX = 5;
const canvases = [];
const grid = document.getElementById('grid');
views.forEach(v => {
  const d = document.createElement('div'); d.className = 'cell';
  const c = document.createElement('div'); c.className = 'cap'; c.textContent = v.name;
  const cv = document.createElement('canvas');
  d.appendChild(c); d.appendChild(cv); grid.appendChild(d);
  canvases.push({cv:cv, view:v});
});
function project(x,y,z,W,H,s){
  const ca=Math.cos(az), sa=Math.sin(az), ce=Math.cos(el), se=Math.sin(el);
  const rx = ca*x - sa*y;
  const ry = sa*x + ca*y;
  return [W/2 + s*rx, H/2 + s*(ry*se - z*ce*1.25)];
}
function draw(entry){
  const cv = entry.cv, view = entry.view;
  const dpr = window.devicePixelRatio || 1;
  const W = cv.clientWidth, H = cv.clientHeight;
  cv.width = W*dpr; cv.height = H*dpr;
  const ctx = cv.getContext('2d');
  ctx.setTransform(dpr,0,0,dpr,0,0);
  ctx.clearRect(0,0,W,H);
  const s = zoom * Math.min(W, H) / 11.0;
  let amp = 0.001;
  for(let i=0;i<=NU;i++) for(let j=0;j<=NV;j++)
    amp = Math.max(amp, Math.abs(view.f(i*UMAX/NU, j*VMAX/NV)));
  const quads = [];
  for(let i=0;i<NU;i++) for(let j=0;j<NV;j++){
    const u0=i*UMAX/NU, u1=(i+1)*UMAX/NU, v0=j*VMAX/NV, v1=(j+1)*VMAX/NV;
    const cs = [[u0,v0],[u1,v0],[u1,v1],[u0,v1]].map(([u,v]) =>
      project(u-UMAX/2, v-VMAX/2, view.f(u,v), W, H, s));
    const uc=(u0+u1)/2, vc=(v0+v1)/2, zc=view.f(uc,vc);
    const ca=Math.cos(az), sa=Math.sin(az);
    const dep = (uc-UMAX/2)*sa + (vc-VMAX/2)*ca;
    const h=0.05;
    const du=(view.f(uc+h,vc)-view.f(uc-h,vc))/(2*h);
    const dv=(view.f(uc,vc+h)-view.f(uc,vc-h))/(2*h);
    const L=Math.sqrt(du*du+dv*dv+1);
    const lam=Math.max(0,(-du*0.42-dv*0.35+0.84)/L);
    const sh=0.58+0.42*lam;
    const t=Math.min(1,Math.max(0,(zc/amp+1)/2));
    const col='rgb('+view.lo.map((c,k)=>Math.round(sh*(c+(view.hi[k]-c)*t))).join(',')+')';
    quads.push({d:dep, pts:cs, col:col});
  }
  quads.sort((a,b)=>a.d-b.d);
  quads.forEach(q => {
    ctx.beginPath();
    ctx.moveTo(q.pts[0][0], q.pts[0][1]);
    for(let k=1;k<4;k++) ctx.lineTo(q.pts[k][0], q.pts[k][1]);
    ctx.closePath();
    ctx.fillStyle=q.col; ctx.strokeStyle=q.col; ctx.lineWidth=0.6;
    ctx.fill(); ctx.stroke();
  });
  ctx.fillStyle='#0f172a';
  for(let j=0;j<=8;j++) for(let k=0;k<=5;k++){
    const p = project(j-UMAX/2, k-VMAX/2, view.f(j,k), W, H, s);
    ctx.beginPath(); ctx.arc(p[0],p[1],2.6,0,6.2832); ctx.fill();
  }
}
function drawAll(){ canvases.forEach(draw); }
let dragging=false, lx=0, ly=0;
document.addEventListener('mousedown', e => { dragging=true; lx=e.clientX; ly=e.clientY; });
document.addEventListener('mouseup', () => { dragging=false; });
document.addEventListener('mousemove', e => {
  if(!dragging) return;
  az += (e.clientX-lx)*0.008; el += (e.clientY-ly)*0.006;
  el = Math.max(-1.4, Math.min(1.4, el));
  lx=e.clientX; ly=e.clientY; drawAll();
});
document.addEventListener('wheel', e => {
  zoom *= (e.deltaY>0 ? 0.94 : 1.06);
  zoom = Math.max(0.3, Math.min(4.0, zoom));
  drawAll();
}, {passive:true});
window.addEventListener('resize', drawAll);
drawAll();
</script>
</body>
</html>
"

end TauWavesSvg

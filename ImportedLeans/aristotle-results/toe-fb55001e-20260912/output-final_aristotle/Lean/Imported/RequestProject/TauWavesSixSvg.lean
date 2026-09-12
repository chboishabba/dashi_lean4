/-
# Six fibers with multiplicity, in three dimensions

Renders the objects of `RequestProject/TauWavesSix.lean` — the smoothed fibers of the six small
primes of the Monster, each taken with the multiplicity it has in

```
|M| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71
```

— as six axonometric panels:

```
A  the six waves            w_p(u), p = 2, 3, 5, 7, 11, 13, one curtain each
B  the same, with multiplicity   m_p w_p(u):  46, 20, 9, 6, 2, 3 copies
C  the build-up, prime by prime  primeStack j, j = 1 … 6
D  the build-up surface          z = buildSurface(u, t), t = 0 … 86 copies
E  46 w₂(u) + rest(v)            the 2-part against the other five primes, constructive
F  46 w₂(u) − rest(v)            the same, destructive (white nodal curve)
```

Outputs:

* `visualization/monster-tau-waves-six.svg` — the six panels;
* `visualization/monster-tau-waves-six.html` — the surfaces of D, E, F, rotatable;
* `visualization/monster_tau_waves_six.csv` — the sampled heights.

Only floating-point geometry and string manipulation live here; everything asserted on the
pictures is proved in `RequestProject/TauWavesSix.lean`.
-/
import RequestProject.TauWavesSix
import RequestProject.SporadicSvg

namespace TauWavesSixSvg

open SporadicSvg

set_option autoImplicit false

/-! ## The six waves, numerically -/

/-- `τ(p)` for the six small primes. -/
def tauOf (p : Nat) : Float :=
  if p = 2 then -24.0
  else if p = 3 then 252.0
  else if p = 5 then 4830.0
  else if p = 7 then -16744.0
  else if p = 11 then 534612.0
  else -577738.0

/-- The multiplicity of the fiber of `p` in `|M|`. -/
def multOf (p : Nat) : Float :=
  if p = 2 then 46.0
  else if p = 3 then 20.0
  else if p = 5 then 9.0
  else if p = 7 then 6.0
  else if p = 11 then 2.0
  else 3.0

/-- The Satake angle `θ_p = arccos(τ(p)/2p^{11/2})`. -/
def thetaOf (p : Nat) : Float :=
  let x := Float.ofNat p
  Float.acos (tauOf p / (2.0 * Float.sqrt (x * x * x * x * x * x * x * x * x * x * x)))

/-- The smoothed fiber of `p`: `w_p(u) = sin((u+1)θ_p)/sin θ_p`. -/
def wv (p : Nat) (u : Float) : Float :=
  Float.sin ((u + 1.0) * thetaOf p) / Float.sin (thetaOf p)

def sixPrimes : List Nat := [2, 3, 5, 7, 11, 13]

/-- The largest `k` with `p^k ≤ 256`, i.e. the number of plotted points on the fiber of `p`. -/
def kMaxOf (p : Nat) : Nat :=
  if p = 2 then 8 else if p = 3 then 5 else if p = 5 then 3 else 2

/-- The stack: the six waves with their Monster multiplicities. -/
def stackF (u : Float) : Float :=
  (sixPrimes.map fun p => multOf p * wv p u).foldl (· + ·) 0.0

/-- The stack after the first `j` primes. -/
def primeStackF (j : Nat) (u : Float) : Float :=
  ((sixPrimes.take j).map fun p => multOf p * wv p u).foldl (· + ·) 0.0

/-- The ramp of a block of `len` copies starting at copy `offset`. -/
def blockRampF (t offset len : Float) : Float :=
  let x := t - offset
  let y := if x < len then x else len
  if y < 0.0 then 0.0 else y

/-- The build-up surface: `t` copies laid down, in the order `2,…,2,3,…,3,5,…,13`. -/
def buildF (u t : Float) : Float :=
  blockRampF t 0.0 46.0 * wv 2 u + blockRampF t 46.0 20.0 * wv 3 u
    + blockRampF t 66.0 9.0 * wv 5 u + blockRampF t 75.0 6.0 * wv 7 u
    + blockRampF t 81.0 2.0 * wv 11 u + blockRampF t 83.0 3.0 * wv 13 u

/-- The `2`-part of the Monster as a wave. -/
def twoPartF (u : Float) : Float := 46.0 * wv 2 u

/-- The other five small primes, with multiplicity. -/
def restF (v : Float) : Float :=
  20.0 * wv 3 v + 9.0 * wv 5 v + 6.0 * wv 7 v + 2.0 * wv 11 v + 3.0 * wv 13 v

/-! ## Colour helpers -/

private def clampByte (x : Float) : Nat :=
  let y := if x < 0.0 then 0.0 else if x > 255.0 then 255.0 else x
  y.toUInt64.toNat

private def hex2 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 (min n 255))
  if s.length = 1 then "0" ++ s else s

private def rgbStr (r g b : Float) : String :=
  "#" ++ hex2 (clampByte r) ++ hex2 (clampByte g) ++ hex2 (clampByte b)

private def ramp (lo hi : Float × Float × Float) (t s : Float) : String :=
  let t := if t < 0.0 then 0.0 else if t > 1.0 then 1.0 else t
  rgbStr (s * (lo.1 + (hi.1 - lo.1) * t)) (s * (lo.2.1 + (hi.2.1 - lo.2.1) * t))
    (s * (lo.2.2 + (hi.2.2 - lo.2.2) * t))

/-- A washed-out version of a colour: `f = 0` is white, `f = 1` the colour itself. -/
private def lighten (c : Float × Float × Float) (f : Float) : Float × Float × Float :=
  (255.0 - (255.0 - c.1) * f, 255.0 - (255.0 - c.2.1) * f, 255.0 - (255.0 - c.2.2) * f)

private def polygonTag (pts : List (Float × Float)) (fill stroke : String) (sw : Float) :
    String :=
  "  <polygon " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++ " " ++
    attr "fill" fill ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt sw) ++ " " ++ attr "stroke-linejoin" "round" ++ "/>"

/-! ## Panels -/

/-- One curtain of a ribbon panel: a wave drawn at its own depth `v`. -/
structure Ribbon where
  v : Float
  /-- The RGB triple this curtain is shaded with. -/
  tint : Float × Float × Float
  deep : String
  label : String
  /-- Dots at the integer heights `u = 0, …, dots`. -/
  dots : Nat
  g : Float → Float

/-- A panel: either a surface over the rectangle of heights, or a family of curtains. -/
structure Panel where
  key : String
  title : String
  eqn : String
  note : String
  /-- `true` for a surface panel, `false` for a ribbon panel. -/
  isSurface : Bool
  f : Float → Float → Float
  ribbons : List Ribbon
  uMax : Float
  vMax : Float
  su : Float
  sv : Float
  zHalf : Float
  nu : Nat
  nv : Nat
  lo : Float × Float × Float
  hi : Float × Float × Float
  ox : Float
  oy : Float
  uTick : Nat → String
  uTickN : Nat
  vTick : Nat → String
  vTickN : Nat
  vTickStep : Float
  nodal : Bool
  /-- Section curves at distinguished values of `v`, drawn on top and labelled. -/
  stages : List (Float × String)

def uAt (P : Panel) (i : Nat) : Float := P.uMax * Float.ofNat i / Float.ofNat P.nu
def vAt (P : Panel) (j : Nat) : Float := P.vMax * Float.ofNat j / Float.ofNat P.nv

/-- The largest `|z|` on the panel, used both for the colour ramp and the vertical scale. -/
def ampOf (P : Panel) : Float :=
  let vals :=
    if P.isSurface then
      (List.range (P.nu + 1)).flatMap fun i =>
        (List.range (P.nv + 1)).map fun j => (P.f (uAt P i) (vAt P j)).abs
    else
      P.ribbons.flatMap fun R =>
        (List.range (P.nu + 1)).map fun i => (R.g (uAt P i)).abs
  vals.foldl (fun a b => if a < b then b else a) 0.001

/-- Pixels per unit of height on this panel (`amp` is `ampOf P`, passed in so that it is
computed once per panel). -/
def szOf (P : Panel) (amp : Float) : Float := P.zHalf / amp

/-- Axonometric projection of `(u, v, z)`. -/
def proj (P : Panel) (amp u v z : Float) : Float × Float :=
  let x := (u - P.uMax / 2.0) * P.su
  let y := (v - P.vMax / 2.0) * P.sv
  (P.ox + (x - y) * 0.8660254, P.oy + (x + y) * 0.5 - z * szOf P amp)

def depth (P : Panel) (u v : Float) : Float := u * P.su + v * P.sv

/-- Lambert shading from the surface gradient. -/
def shade (P : Panel) (amp u v : Float) : Float :=
  let h := 0.04 * P.uMax
  let k := 0.04 * P.vMax
  let du := (P.f (u + h) v - P.f (u - h) v) / (2.0 * h) * P.uMax
  let dv := (P.f u (v + k) - P.f u (v - k)) / (2.0 * k) * P.vMax
  let nx := -du / amp
  let ny := -dv / amp
  let len := Float.sqrt (nx * nx + ny * ny + 1.0)
  let d := (nx * 0.42 + ny * 0.35 + 0.84) / len
  let d := if d < 0.0 then 0.0 else d
  0.58 + 0.42 * d

def quadOf (P : Panel) (amp : Float) (i j : Nat) : Float × String :=
  let u0 := uAt P i
  let u1 := uAt P (i + 1)
  let v0 := vAt P j
  let v1 := vAt P (j + 1)
  let z00 := P.f u0 v0
  let z10 := P.f u1 v0
  let z11 := P.f u1 v1
  let z01 := P.f u0 v1
  let uc := (u0 + u1) / 2.0
  let vc := (v0 + v1) / 2.0
  let zc := (z00 + z10 + z11 + z01) / 4.0
  let t := (zc / amp + 1.0) / 2.0
  let col := ramp P.lo P.hi t (shade P amp uc vc)
  (depth P uc vc,
    polygonTag [proj P amp u0 v0 z00, proj P amp u1 v0 z10, proj P amp u1 v1 z11,
      proj P amp u0 v1 z01] col col 0.5)

/-- A curtain: the region between the wave and the floor, at one depth. -/
def curtainOf (P : Panel) (amp : Float) (R : Ribbon) (i : Nat) : Float × String :=
  let u0 := uAt P i
  let u1 := uAt P (i + 1)
  let z0 := R.g u0
  let z1 := R.g u1
  let zc := (z0 + z1) / 2.0
  let t := (zc / amp + 1.0) / 2.0
  let col := ramp (lighten R.tint 0.16) R.tint t 1.0
  (depth P ((u0 + u1) / 2.0) R.v,
    polygonTag [proj P amp u0 R.v 0.0, proj P amp u0 R.v z0, proj P amp u1 R.v z1,
      proj P amp u1 R.v 0.0] col col 0.4)

/-- The floor rectangle and its ticks. -/
def frameSvg (P : Panel) (amp : Float) : String :=
  let pr := proj P amp
  let corner :=
    [pr 0.0 0.0 0.0, pr P.uMax 0.0 0.0, pr P.uMax P.vMax 0.0, pr 0.0 P.vMax 0.0, pr 0.0 0.0 0.0]
  let uticks := (List.range (P.uTickN + 1)).map fun k =>
    let u := Float.ofNat k * P.uMax / Float.ofNat P.uTickN
    let a := pr u 0.0 0.0
    let b := pr u (-0.03 * P.vMax) 0.0
    lineTag a.1 a.2 b.1 b.2 "#94a3b8" 0.9 "" ++ "\n" ++
      textTag (b.1 - 3.0) (b.2 + 12.0) 11 "#64748b" "end" "500" (P.uTick k)
  let vticks := (List.range (P.vTickN + 1)).map fun k =>
    let v := Float.ofNat k * P.vTickStep
    let a := pr 0.0 v 0.0
    let b := pr (-0.03 * P.uMax) v 0.0
    lineTag a.1 a.2 b.1 b.2 "#94a3b8" 0.9 "" ++ "\n" ++
      textTag (b.1 + 5.0) (b.2 + 12.0) 11 "#64748b" "start" "500" (P.vTick k)
  let zaxis :=
    let a := pr 0.0 0.0 (-amp)
    let b := pr 0.0 0.0 amp
    lineTag a.1 a.2 b.1 b.2 "#cbd5e1" 1.0 "3 3"
  String.intercalate "\n" (polylineTag corner "#94a3b8" 1.1 :: zaxis :: (uticks ++ vticks))

/-- Points of the nodal set `z = 0`, found by sign changes along `v`. -/
def nodalMarks (P : Panel) (amp : Float) : List (Float × String) :=
  (List.range 129).flatMap fun i =>
    let u := P.uMax * Float.ofNat i / 128.0
    (List.range 192).filterMap fun j =>
      let v0 := P.vMax * Float.ofNat j / 192.0
      let v1 := P.vMax * Float.ofNat (j + 1) / 192.0
      let a := P.f u v0
      let b := P.f u v1
      if (a ≤ 0.0 && b > 0.0) || (a ≥ 0.0 && b < 0.0) then
        let v := v0 + (v1 - v0) * (a / (a - b))
        let q := proj P amp u v 0.0
        some (depth P u v + 0.01, circleTag q.1 q.2 1.5 "#ffffff" "#ffffff")
      else none

/-- The body of one panel: floor, surface (or curtains), curves, dots, captions. -/
def panelBody (P : Panel) : String :=
  let amp := ampOf P
  let pieces : List (Float × String) :=
    if P.isSurface then
      ((List.range P.nu).flatMap fun i => (List.range P.nv).map fun j => quadOf P amp i j)
        ++ (if P.nodal then nodalMarks P amp else [])
    else
      P.ribbons.flatMap fun R =>
        let curtains := (List.range P.nu).map fun i => curtainOf P amp R i
        let crest :=
          (depth P P.uMax R.v + 0.005,
            polylineTag ((List.range 161).map fun i =>
              let u := P.uMax * Float.ofNat i / 160.0
              proj P amp u R.v (R.g u)) R.deep 2.0)
        let dots := (List.range (R.dots + 1)).map fun k =>
          let u := Float.ofNat k
          let q := proj P amp u R.v (R.g u)
          (depth P u R.v + 0.01, circleTag q.1 q.2 3.4 R.deep "#ffffff")
        let tag :=
          let q := proj P amp 0.0 R.v 0.0
          (depth P 0.0 R.v + 0.02,
            textTag (q.1 - 12.0) (q.2 + 4.0) 12 R.deep "end" "700" R.label)
        curtains ++ (crest :: tag :: dots)
  let sorted := pieces.mergeSort (fun a b => a.1 ≤ b.1)
  let sectionCurves :=
    if P.isSurface then
      polylineTag ((List.range 161).map fun i =>
          let u := P.uMax * Float.ofNat i / 160.0
          proj P amp u P.vMax (P.f u P.vMax)) "#1f2937" 1.4 ++ "\n" ++
        polylineTag ((List.range 161).map fun j =>
          let v := P.vMax * Float.ofNat j / 160.0
          proj P amp P.uMax v (P.f P.uMax v)) "#1f2937" 1.4
    else ""
  let stageCurves := String.intercalate "\n"
    ((List.range P.stages.length).map fun k =>
      let st := P.stages[k]!
      let curve := (List.range 97).map fun i =>
        let u := P.uMax * Float.ofNat i / 96.0
        proj P amp u st.1 (P.f u st.1)
      let start := curve.headD (0.0, 0.0)
      let ly := P.oy - 232.0 + 20.0 * Float.ofNat k
      let lx := P.ox - 400.0
      polylineTag curve "#0f172a" 1.7 ++ "\n" ++
        lineTag (lx + 168.0) (ly - 4.0) start.1 start.2 "#94a3b8" 0.8 "2 3" ++ "\n" ++
        textTag lx ly 11 "#0f172a" "start" "700" st.2)
  String.intercalate "\n"
    [ textTag (P.ox - 400.0) (P.oy - 300.0) 17 "#0f172a" "start" "700" P.title,
      textTag (P.ox - 400.0) (P.oy - 279.0) 13 "#334155" "start" "600" P.eqn,
      frameSvg P amp,
      String.intercalate "\n" (sorted.map fun q => q.2),
      sectionCurves,
      stageCurves,
      textTag (P.ox - 400.0) (P.oy + 288.0) 12 "#475569" "start" "400" P.note,
      textTag (P.ox - 400.0) (P.oy + 306.0) 11 "#94a3b8" "start" "400"
        ("vertical scale: 1 unit = " ++ fmtFixed 2 (szOf P amp) ++ " px,  max |z| = " ++
          fmtFixed 3 amp) ]

/-! ## The six panels -/

private def redLo : Float × Float × Float := (254.0, 226.0, 226.0)
private def redHi : Float × Float × Float := (153.0, 27.0, 27.0)
private def blueLo : Float × Float × Float := (219.0, 234.0, 254.0)
private def blueHi : Float × Float × Float := (29.0, 78.0, 216.0)
private def violetLo : Float × Float × Float := (237.0, 233.0, 254.0)
private def violetHi : Float × Float × Float := (91.0, 33.0, 182.0)
private def greenLo : Float × Float × Float := (209.0, 250.0, 229.0)
private def greenHi : Float × Float × Float := (4.0, 120.0, 87.0)
private def amberLo : Float × Float × Float := (254.0, 243.0, 199.0)
private def amberHi : Float × Float × Float := (146.0, 64.0, 14.0)
private def slateLo : Float × Float × Float := (226.0, 232.0, 240.0)
private def slateHi : Float × Float × Float := (15.0, 23.0, 42.0)

def primeRgb (p : Nat) : Float × Float × Float :=
  if p = 2 then (185.0, 28.0, 28.0)
  else if p = 3 then (29.0, 78.0, 216.0)
  else if p = 5 then (4.0, 120.0, 87.0)
  else if p = 7 then (180.0, 83.0, 9.0)
  else if p = 11 then (109.0, 40.0, 217.0)
  else (190.0, 18.0, 60.0)

def primeCol (p : Nat) : String :=
  if p = 2 then "#b91c1c"
  else if p = 3 then "#1d4ed8"
  else if p = 5 then "#047857"
  else if p = 7 then "#b45309"
  else if p = 11 then "#6d28d9"
  else "#be123c"

/-- Panel A: the six waves, one curtain per prime. -/
def panelWaves : Panel where
  key := "A"
  title := "A \u2014 the six fibers as waves"
  eqn := "z = w_p(u) = sin((u+1)\u03b8_p)/sin \u03b8_p,  p = 2, 3, 5, 7, 11, 13"
  note := "each wave passes through the plotted points \u03c4(p^k)/p^(11k/2) of its fiber (dots)"
  isSurface := false
  f := fun u _ => wv 2 u
  ribbons := sixPrimes.map fun p =>
    { v := Float.ofNat (sixPrimes.idxOf p), tint := primeRgb p, deep := primeCol p,
      label := "p = " ++ toString p, dots := kMaxOf p, g := fun u => wv p u }
  uMax := 8.0
  vMax := 5.0
  su := 44.0
  sv := 52.0
  zHalf := 135.0
  nu := 64
  nv := 6
  lo := slateLo
  hi := slateHi
  ox := 470.0
  oy := 620.0
  uTick := fun k => "u=" ++ toString k
  uTickN := 8
  vTick := fun k => "p=" ++ toString (sixPrimes[k]!)
  vTickN := 5
  vTickStep := 1.0
  nodal := false
  stages := []

/-- Panel B: the same six waves, each taken with its Monster multiplicity. -/
def panelMult : Panel where
  key := "B"
  title := "B \u2014 the same six waves, with multiplicity"
  eqn := "z = m_p w_p(u),  (m_2,\u2026,m_13) = (46, 20, 9, 6, 2, 3) = the exponents of |M|"
  note := "the 2-part dominates: 46 copies of w\u2082 against 20, 9, 6, 2, 3 copies of the rest"
  isSurface := false
  f := fun u _ => 46.0 * wv 2 u
  ribbons := sixPrimes.map fun p =>
    { v := Float.ofNat (sixPrimes.idxOf p), tint := primeRgb p, deep := primeCol p,
      label := toString (multOf p).toUInt64.toNat ++ "\u00d7" ++ toString p,
      dots := kMaxOf p, g := fun u => multOf p * wv p u }
  uMax := 8.0
  vMax := 5.0
  su := 44.0
  sv := 52.0
  zHalf := 135.0
  nu := 64
  nv := 6
  lo := amberLo
  hi := amberHi
  ox := 1330.0
  oy := 620.0
  uTick := fun k => "u=" ++ toString k
  uTickN := 8
  vTick := fun k => "p=" ++ toString (sixPrimes[k]!)
  vTickN := 5
  vTickStep := 1.0
  nodal := false
  stages := []

/-- Panel C: the build-up, one prime at a time. -/
def panelPrimeStack : Panel where
  key := "C"
  title := "C \u2014 building the stack up, one prime at a time"
  eqn := "z = primeStack j (u) = \u2211_{i \u2264 j} m_{p_i} w_{p_i}(u),  j = 1, \u2026, 6"
  note := "the last curtain is the full stack 46w\u2082+20w\u2083+9w\u2085+6w\u2087+2w\u2081\u2081+3w\u2081\u2083"
  isSurface := false
  f := fun u _ => stackF u
  ribbons := (List.range 6).map fun j =>
    { v := Float.ofNat j, tint := primeRgb (sixPrimes[j]!), deep := primeCol (sixPrimes[j]!),
      label := "+" ++ toString (sixPrimes[j]!), dots := 8, g := fun u => primeStackF (j + 1) u }
  uMax := 8.0
  vMax := 5.0
  su := 44.0
  sv := 52.0
  zHalf := 135.0
  nu := 64
  nv := 6
  lo := violetLo
  hi := violetHi
  ox := 470.0
  oy := 1440.0
  uTick := fun k => "u=" ++ toString k
  uTickN := 8
  vTick := fun k => "j=" ++ toString (k + 1)
  vTickN := 5
  vTickStep := 1.0
  nodal := false
  stages := []

/-- Panel D: the continuous build-up surface, copy by copy up to `t = 86`. -/
def panelBuild : Panel where
  key := "D"
  title := "D \u2014 the build-up surface: 86 copies, laid down one at a time"
  eqn := "z = buildSurface(u, t),  t = number of copies laid down, 0 \u2264 t \u2264 86"
  note :=
    "blocks 2\u00d746 | 3\u00d720 | 5\u00d79 | 7\u00d76 | 11\u00d72 | 13\u00d73; back edge u = 0 is the straight ramp z = t"
  isSurface := true
  f := fun u t => buildF u t
  ribbons := []
  uMax := 8.0
  vMax := 86.0
  su := 42.0
  sv := 3.6
  zHalf := 165.0
  nu := 48
  nv := 86
  lo := blueLo
  hi := blueHi
  ox := 1330.0
  oy := 1440.0
  uTick := fun k => "u=" ++ toString k
  uTickN := 8
  vTick := fun k => "t=" ++ toString (k * 10)
  vTickN := 8
  vTickStep := 10.0
  nodal := false
  stages := [(26.0, "t = 26:  2^26"), (46.0, "t = 46:  2^46 complete"),
    (66.0, "t = 66:  + 3^20"), (75.0, "t = 75:  + 5^9"), (81.0, "t = 81:  + 7^6"),
    (83.0, "t = 83:  + 11^2"), (86.0, "t = 86:  + 13^3 = the full stack")]

/-- Panel E: the 2-part against the other five primes, constructive. -/
def panelSum : Panel where
  key := "E"
  title := "E \u2014 the 2-part against the other five primes: constructive"
  eqn := "z = 46 w\u2082(u) + (20w\u2083 + 9w\u2085 + 6w\u2087 + 2w\u2081\u2081 + 3w\u2081\u2083)(v)"
  note := "on the diagonal u = v this is the whole stack; z(0,0) = 46 + 40 = 86 exponents"
  isSurface := true
  f := fun u v => twoPartF u + restF v
  ribbons := []
  uMax := 8.0
  vMax := 5.0
  su := 46.0
  sv := 62.0
  zHalf := 150.0
  nu := 56
  nv := 44
  lo := greenLo
  hi := greenHi
  ox := 470.0
  oy := 2310.0
  uTick := fun k => "2^" ++ toString k
  uTickN := 8
  vTick := fun k => "v=" ++ toString k
  vTickN := 5
  vTickStep := 1.0
  nodal := true
  stages := []

/-- Panel F: the same two groups, destructive. -/
def panelDiff : Panel where
  key := "F"
  title := "F \u2014 the 2-part against the other five primes: destructive"
  eqn := "z = 46 w\u2082(u) \u2212 (20w\u2083 + 9w\u2085 + 6w\u2087 + 2w\u2081\u2081 + 3w\u2081\u2083)(v)"
  note := "the white curve is the nodal set 46w\u2082(u) = rest(v): the 2-part cancels the rest"
  isSurface := true
  f := fun u v => twoPartF u - restF v
  ribbons := []
  uMax := 8.0
  vMax := 5.0
  su := 46.0
  sv := 62.0
  zHalf := 150.0
  nu := 56
  nv := 44
  lo := redLo
  hi := redHi
  ox := 1330.0
  oy := 2310.0
  uTick := fun k => "2^" ++ toString k
  uTickN := 8
  vTick := fun k => "v=" ++ toString k
  vTickN := 5
  vTickStep := 1.0
  nodal := true
  stages := []

def panels : List Panel := [panelWaves, panelMult, panelPrimeStack, panelBuild, panelSum,
  panelDiff]

/-! ## The document -/

def headerSvg : String :=
  String.intercalate "\n"
    [ textTag 72.0 58.0 25 "#0f172a" "start" "700"
        ("The six small primes of the Monster as modular waves, each taken as often as it" ++
          " divides |M|"),
      textTag 72.0 88.0 14 "#334155" "start" "400"
        ("Along the fiber of a prime p the Hecke recursion makes the Deligne-normalised" ++
          " coefficients of \u0394 = \u03b7\u00b2\u2074 a sampled sine wave:"),
      textTag 72.0 110.0 14 "#334155" "start" "400"
        ("\u03c4(p^k)/p^(11k/2) = sin((k+1)\u03b8_p)/sin \u03b8_p  with  cos \u03b8_p =" ++
          " \u03c4(p)/(2p^(11/2))  \u2014  proved for p = 2, 3, 5, 7, 11, 13."),
      textTag 72.0 132.0 14 "#334155" "start" "400"
        ("|M| = 2^46 \u00b7 3^20 \u00b7 5^9 \u00b7 7^6 \u00b7 11^2 \u00b7 13^3 \u00b7 17 \u00b7" ++
          " 19 \u00b7 23 \u00b7 29 \u00b7 31 \u00b7 41 \u00b7 47 \u00b7 59 \u00b7 71, so the six" ++
          " waves enter with multiplicities 46, 20, 9, 6, 2, 3 \u2014 86 copies in all."),
      textTag 72.0 154.0 13 "#64748b" "start" "400"
        ("Panels A\u2013C build the stack up (wave by wave, then prime by prime); D is the" ++
          " continuous build-up in the copy-count t; E, F interfere the 2-part with the rest.") ]

def footerSvg : String :=
  String.intercalate "\n"
    [ textTag 72.0 2700.0 13 "#334155" "start" "600"
        "Proved in RequestProject/TauWavesSix.lean:",
      textTag 72.0 2722.0 12 "#475569" "start" "400"
        ("abs_satakeCos_lt_one_of_sq and its six corollaries \u2014 Deligne's bound |\u03c4(p)|" ++
          " &lt; 2p^(11/2) at p = 2, 3, 5, 7, 11, 13, so all six angles \u03b8_p are real;"),
      textTag 72.0 2742.0 12 "#475569" "start" "400"
        ("wave_eq_normTau_five / _seven / _eleven / _thirteen \u2014 the four new waves pass" ++
          " through the plotted points of their fibers (dots in panels A, B);"),
      textTag 72.0 2762.0 12 "#475569" "start" "400"
        ("primeStack_six, copyStack_86, buildSurface_86 \u2014 the three build-ups all close on" ++
          " the stack 46w\u2082+20w\u2083+9w\u2085+6w\u2087+2w\u2081\u2081+3w\u2081\u2083;"),
      textTag 72.0 2782.0 12 "#475569" "start" "400"
        ("copyStack_at_zero, buildSurface_at_zero \u2014 over u = 0 the build-up is the ramp" ++
          " z = t: the 86 steps are the 86 prime-power points of the six small fibers;"),
      textTag 72.0 2802.0 12 "#475569" "start" "400"
        ("stackWave_zero = 86 = \u2211 v_p(|M|) over the six small primes;  abs_stackWave_le" ++
          " \u2014 the stack's amplitude;  deriv_deriv_stackWave \u2014 all six Satake" ++
          " frequencies are visible in it;"),
      textTag 72.0 2822.0 12 "#475569" "start" "400"
        ("sum6_add_diff6 / sum6_sub_diff6 \u2014 panels E and F recover the 2-part and the" ++
          " rest;  diffSurface6_eq_zero_iff \u2014 the white nodal curve of panel F.") ]

/-- The six-panel figure. -/
def wavesSixSvg : String :=
  let width := 2200.0
  let height := 2880.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  headerSvg ++ "\n" ++
  String.intercalate "\n" (panels.map panelBody) ++ "\n" ++
  footerSvg ++ "\n</svg>\n"

/-! ## Data -/

/-- The six waves, the stack, the six partial stacks and the build-up, on a quarter-integer
grid of heights. -/
def wavesSixCsv : String :=
  let header :=
    "u,w2,w3,w5,w7,w11,w13,stack,stage1,stage2,stage3,stage4,stage5,stage6,build_t46,build_t86\n"
  let rows := (List.range 33).map fun i =>
    let u := Float.ofNat i / 4.0
    String.intercalate ","
      ([fmtFixed 2 u] ++ (sixPrimes.map fun p => fmtFixed 6 (wv p u)) ++
        [fmtFixed 6 (stackF u)] ++
        ((List.range 6).map fun j => fmtFixed 6 (primeStackF (j + 1) u)) ++
        [fmtFixed 6 (buildF u 46.0), fmtFixed 6 (buildF u 86.0)]) ++ "\n"
  header ++ String.join rows

/-! ## The rotatable version -/

private def gridJson (P : Panel) : String :=
  let rows := (List.range (P.nu + 1)).map fun i =>
    "[" ++ String.intercalate ","
      ((List.range (P.nv + 1)).map fun j => fmtFixed 4 (P.f (uAt P i) (vAt P j))) ++ "]"
  "{\"name\":\"" ++ P.title ++ "\",\"eqn\":\"" ++ P.eqn ++ "\",\"uMax\":" ++ fmt P.uMax ++
    ",\"vMax\":" ++ fmt P.vMax ++ ",\"z\":[" ++ String.intercalate "," rows ++ "]}"

/-- A self-contained page with the three surface panels, rotatable with the mouse. -/
def wavesSixHtml : String :=
  let data := "[" ++ String.intercalate ","
    ((panels.filter fun P => P.isSurface).map gridJson) ++ "]"
"<!DOCTYPE html>
<html lang=\"en\">
<head>
<meta charset=\"utf-8\"/>
<title>Six small primes of the Monster as modular waves</title>
<style>
 body { margin:0; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; color:#0f172a;
        background:#ffffff; }
 h1 { font-size:19px; margin:16px 20px 4px; }
 p  { font-size:13px; margin:2px 20px; color:#334155; }
 #grid { display:grid; grid-template-columns:1fr 1fr 1fr; gap:8px; padding:12px 20px 24px; }
 .cell { border:1px solid #e2e8f0; border-radius:8px; padding:6px; }
 .cap { font-size:12px; font-weight:600; margin:2px 6px 6px; }
 canvas { width:100%; height:420px; display:block; cursor:grab; }
</style>
</head>
<body>
<h1>The six small primes of the Monster as modular waves, with multiplicity</h1>
<p>|M| = 2^46 &middot; 3^20 &middot; 5^9 &middot; 7^6 &middot; 11^2 &middot; 13^3 &middot; 17 &middot; 19 &middot; 23 &middot; 29 &middot; 31 &middot; 41 &middot; 47 &middot; 59 &middot; 71 &mdash; the fiber of p enters the stack v_p(|M|) times, 86 copies in all.</p>
<p>Drag to rotate all three surfaces together; wheel to zoom.</p>
<div id=\"grid\"></div>
<script>
const DATA = " ++ data ++ ";
let rot = 0.7, tilt = 0.62, zoom = 1.0;
const cells = [];
const host = document.getElementById('grid');
for (const d of DATA) {
  const cell = document.createElement('div'); cell.className = 'cell';
  const cap = document.createElement('div'); cap.className = 'cap';
  cap.textContent = d.name + '   ' + d.eqn;
  const cv = document.createElement('canvas');
  cell.appendChild(cap); cell.appendChild(cv); host.appendChild(cell);
  cells.push({d: d, cv: cv});
}
function draw(cell) {
  const d = cell.d, cv = cell.cv;
  const w = cv.clientWidth, h = cv.clientHeight;
  cv.width = w * devicePixelRatio; cv.height = h * devicePixelRatio;
  const ctx = cv.getContext('2d');
  ctx.setTransform(devicePixelRatio,0,0,devicePixelRatio,0,0);
  ctx.clearRect(0,0,w,h);
  const nu = d.z.length - 1, nv = d.z[0].length - 1;
  let amp = 1e-6;
  for (let i=0;i<=nu;i++) for (let j=0;j<=nv;j++) amp = Math.max(amp, Math.abs(d.z[i][j]));
  const s = zoom * Math.min(w, h) / 2.6;
  const proj = (i,j,z) => {
    const x = (i/nu - 0.5), y = (j/nv - 0.5), zz = z/amp*0.55;
    const cx = Math.cos(rot), sx = Math.sin(rot);
    const X = x*cx - y*sx, Y = x*sx + y*cx;
    return [w/2 + X*s, h/2 + (Y*Math.sin(tilt) - zz*Math.cos(tilt))*s];
  };
  const quads = [];
  for (let i=0;i<nu;i++) for (let j=0;j<nv;j++) {
    const zc = (d.z[i][j]+d.z[i+1][j]+d.z[i+1][j+1]+d.z[i][j+1])/4;
    const cx = Math.cos(rot), sx = Math.sin(rot);
    const x = ((i+0.5)/nu - 0.5), y = ((j+0.5)/nv - 0.5);
    const dep = (x*sx + y*cx);
    quads.push([dep, i, j, zc]);
  }
  quads.sort((a,b) => a[0]-b[0]);
  for (const q of quads) {
    const i = q[1], j = q[2], t = (q[3]/amp + 1)/2;
    const r = Math.round(240 - 200*t), g = Math.round(240 - 150*t), b = Math.round(250 - 60*t);
    const p0 = proj(i,j,d.z[i][j]), p1 = proj(i+1,j,d.z[i+1][j]);
    const p2 = proj(i+1,j+1,d.z[i+1][j+1]), p3 = proj(i,j+1,d.z[i][j+1]);
    ctx.beginPath(); ctx.moveTo(p0[0],p0[1]); ctx.lineTo(p1[0],p1[1]);
    ctx.lineTo(p2[0],p2[1]); ctx.lineTo(p3[0],p3[1]); ctx.closePath();
    ctx.fillStyle = 'rgb('+r+','+g+','+b+')'; ctx.fill();
    ctx.strokeStyle = 'rgba(0,0,0,0.05)'; ctx.stroke();
  }
}
function drawAll() { for (const c of cells) draw(c); }
let dragging = false, lx = 0, ly = 0;
addEventListener('mousedown', e => { dragging = true; lx = e.clientX; ly = e.clientY; });
addEventListener('mouseup', () => { dragging = false; });
addEventListener('mousemove', e => {
  if (!dragging) return;
  rot += (e.clientX - lx) * 0.008; tilt += (e.clientY - ly) * 0.006;
  tilt = Math.max(0.05, Math.min(1.5, tilt));
  lx = e.clientX; ly = e.clientY; drawAll();
});
addEventListener('wheel', e => { zoom *= (e.deltaY < 0 ? 1.08 : 0.93); drawAll(); },
  {passive: true});
addEventListener('resize', drawAll);
drawAll();
</script>
</body>
</html>
"

end TauWavesSixSvg

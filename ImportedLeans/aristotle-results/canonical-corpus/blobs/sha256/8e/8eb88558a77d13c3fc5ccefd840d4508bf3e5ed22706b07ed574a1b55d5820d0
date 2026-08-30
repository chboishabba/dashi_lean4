/-
# The two pictures of `T_j`

This file renders the two geometries of `RequestProject/MoonshineBridge.lean`:

* `visualization/moonshine-domain-coloring.svg` — domain-coloured phase maps on the upper
  half-plane `ℍ`, hue `= arg`, brightness `= |·|`;
* `visualization/moonshine-trajectories.svg` — the `s`-plane: the trajectories of
  `T_0(1/2 + it)` and `T_12(1/2 + it)`, and a phase map of the partial sum in `s`.

Only floating-point geometry and string manipulation live here; every mathematical claim
written on the pictures is proved in `RequestProject/MoonshineBridge.lean`.
-/
import RequestProject.MoonshineBridge
import RequestProject.SporadicSvg

namespace MoonshineSvg

open SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 200000

/-! ## Floating-point complex arithmetic -/

/-- A complex number as a pair of `Float`s. -/
abbrev C := Float × Float

def cadd (a b : C) : C := (a.1 + b.1, a.2 + b.2)
def csub (a b : C) : C := (a.1 - b.1, a.2 - b.2)
def cmul (a b : C) : C := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def cdiv (a b : C) : C :=
  let d := b.1 * b.1 + b.2 * b.2
  ((a.1 * b.1 + a.2 * b.2) / d, (a.2 * b.1 - a.1 * b.2) / d)
def cscale (r : Float) (a : C) : C := (r * a.1, r * a.2)
def cabs (a : C) : Float := Float.sqrt (a.1 * a.1 + a.2 * a.2)
def carg (a : C) : Float := Float.atan2 a.2 a.1
def cone : C := (1.0, 0.0)

def twoPi : Float := 6.283185307179586

/-- `e^{iθ}`. -/
def cexpi (theta : Float) : C := (Float.cos theta, Float.sin theta)

/-! ## The functions plotted on the upper half-plane -/

/-- `q = e^{2πiτ}` at `τ = x + iy`. -/
def qOf (x y : Float) : C := cscale (Float.exp (-(twoPi * y))) (cexpi (twoPi * x))

/-- `T_j(τ) = w/(1 − w)` with `w = e^{2πi(τ + j/24)}`, the closed form proved in
`MoonshineBridge.mtQ_eq_div`. -/
def mtQF (j : Nat) (x y : Float) : C :=
  let w := qOf (x + Float.ofNat j / 24.0) y
  cdiv w (csub cone w)

/-- `z^24` by repeated squaring. -/
def cpow24 (z : C) : C :=
  let z2 := cmul z z
  let z4 := cmul z2 z2
  let z8 := cmul z4 z4
  let z16 := cmul z8 z8
  cmul z16 z8

/-- The modular discriminant `Δ(τ) = η(τ)^24 = q ∏_{m ≥ 1} (1 − q^m)^24`, truncated at `m ≤ M`:
the genuine modular form, for comparison with the moonshine series. -/
def deltaF (M : Nat) (x y : Float) : C :=
  let q := qOf x y
  let r := (List.range M).foldl
    (fun (acc : C × C) _ =>
      let qm := cmul acc.2 q
      (cmul acc.1 (cpow24 (csub cone qm)), qm))
    (cone, cone)
  cmul q r.1

/-! ## The functions plotted on the `s`-plane -/

/-- `∑_{n = 1}^{K} e^{2πijn/24} n^{-s}` at `s = σ + it`: the truncated `j`-th McKay–Thompson
series in the Dirichlet grading. -/
def mtSF (j K : Nat) (sigma t : Float) : C :=
  ((List.range (K + 1)).drop 1).foldl
    (fun (acc : C) (n : Nat) =>
      let ln := Float.log (Float.ofNat n)
      let r := Float.exp (-(sigma * ln))
      let ang := -(t * ln) + twoPi * Float.ofNat (j * n % 24) / 24.0
      cadd acc (cscale r (cexpi ang)))
    (0.0, 0.0)

/-! ## Colour -/

def clamp01 (x : Float) : Float := if x < 0.0 then 0.0 else if x > 1.0 then 1.0 else x

def hexDigit (n : Nat) : Char :=
  ("0123456789abcdef".toList).getD n '0'

def byteHex (x : Float) : String :=
  let n := ((clamp01 x) * 255.0 + 0.5).floor.toUInt64.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

/-- HSV → `#rrggbb`, with `h ∈ [0,1)`. -/
def hsvHex (h s v : Float) : String :=
  let h6 := (h - h.floor) * 6.0
  let i := h6.floor
  let f := h6 - i
  let p := v * (1.0 - s)
  let q := v * (1.0 - s * f)
  let w := v * (1.0 - s * (1.0 - f))
  let rgb : Float × Float × Float :=
    if i < 1.0 then (v, w, p)
    else if i < 2.0 then (q, v, p)
    else if i < 3.0 then (p, v, w)
    else if i < 4.0 then (p, q, v)
    else if i < 5.0 then (w, p, v)
    else (v, p, q)
  "#" ++ byteHex rgb.1 ++ byteHex rgb.2.1 ++ byteHex rgb.2.2

/-- The domain-colouring rule: hue from the argument, brightness from the modulus
(`MoonshineBridge.hue`, `MoonshineBridge.brightness`), with light bands on the powers of two
of the modulus as magnitude contours.  The modulus is compressed by a cube root first, which
is still strictly increasing (`MoonshineBridge.brightnessR_cbrt_strictMonoOn`), so that the
small values high in the upper half-plane stay legible. -/
def domainColorGen (expo lo : Float) (z : C) : String :=
  let m := Float.pow (cabs z) expo
  let h := carg z / twoPi + 0.5
  let b := m / (1.0 + m)
  let lg := if cabs z > 0.0 then Float.log (cabs z) / 0.6931471805599453 else 0.0
  let fr := lg - lg.floor
  let v := (lo + (1.0 - lo) * b) * (0.80 + 0.20 * fr)
  hsvHex h 1.0 (clamp01 v)

/-- The rule used on the upper half-plane, where `|T_j|` is small: the modulus is compressed by
a cube root, and the brightness floor is high. -/
def domainColor : C → String := domainColorGen (1.0 / 3.0) 0.48

/-- The rule used on the `s`-plane, where `|T_j|` is of order one: no compression and a low
floor, so that the points where the series is small come out dark. -/
def domainColorS : C → String := domainColorGen 1.0 0.08

/-! ## Rendering helpers -/

def f1 (x : Float) : String := fmtFixed 1 x

def cellTag (x y c : Nat) (fill : String) : String :=
  "<rect x=\"" ++ toString x ++ "\" y=\"" ++ toString y ++ "\" width=\"" ++ toString c ++
    "\" height=\"" ++ toString c ++ "\" fill=\"" ++ fill ++ "\"/>"

/-- A domain-coloured panel: `nx × ny` square cells of side `cell` pixels, with top-left corner
`(ox, oy)`, covering the rectangle `[x0, x1] × [y0, y1]` of the plane, the second coordinate
increasing upwards. -/
def phasePanel (col : C → String) (ox oy nx ny cell : Nat) (x0 x1 y0 y1 : Float)
    (f : Float → Float → C) : String :=
  String.intercalate "\n"
    ((List.range ny).flatMap fun jj =>
      (List.range nx).map fun i =>
        let x := x0 + (Float.ofNat i + 0.5) * (x1 - x0) / Float.ofNat nx
        let y := y1 - (Float.ofNat jj + 0.5) * (y1 - y0) / Float.ofNat ny
        cellTag (ox + i * cell) (oy + jj * cell) cell (col (f x y)))

/-! ## Picture 1 : the phase maps on the upper half-plane -/

private def nxH : Nat := 120
private def nyH : Nat := 95
private def cellH : Nat := 4
private def pw : Float := 480.0
private def ph : Float := 380.0
private def imLo : Float := 0.045
private def imHi : Float := 0.845
private def pTop : Float := 180.0
private def px0 : Float := 90.0
private def px1 : Float := 640.0
private def px2 : Float := 1190.0

private def frameTag (ox oy w h : Float) : String :=
  rectTag ox oy w h "none" "#0f172a" 1.0

/-- The 24 vertical strips: `T_j(τ) = T_0(τ + j/24)` (`MoonshineBridge.mtQ_eq_shift`). -/
private def stripOverlay (ox : Float) : String :=
  String.intercalate "\n"
    ((List.range 25).map fun j =>
      let x := ox + pw * Float.ofNat j / 24.0
      lineTag x pTop x (pTop + ph) "#ffffff" (if j % 24 == 0 then 1.6 else 0.6) "4 4")

private def stripLabels (ox : Float) : String :=
  String.intercalate "\n"
    ([0, 4, 8, 12, 16, 20, 24].map fun j =>
      textTag (ox + pw * Float.ofNat j / 24.0) (pTop + ph + 18.0) 13 "#334155" "middle" "400"
        (if j == 24 then "24=0" else toString j))

private def reTicks (ox : Float) : String :=
  String.intercalate "\n"
    ([(0.0, "0"), (0.25, "1/4"), (0.5, "1/2"), (0.75, "3/4"), (1.0, "1")].map
      fun (v, lab) =>
        let x := ox + pw * v
        lineTag x (pTop + ph) x (pTop + ph + 6.0) "#334155" 1.0 "" ++ "\n" ++
        textTag x (pTop + ph + 38.0) 14 "#0f172a" "middle" "400" lab)

private def imTicks (ox : Float) : String :=
  String.intercalate "\n"
    ([(0.1, "0.1"), (0.3, "0.3"), (0.5, "0.5"), (0.7, "0.7")].map fun (v, lab) =>
      let y := pTop + ph * (imHi - v) / (imHi - imLo)
      lineTag (ox - 6.0) y ox y "#334155" 1.0 "" ++ "\n" ++
      textTag (ox - 12.0) (y + 5.0) 13 "#0f172a" "end" "400" lab)

private def hueBar (ox oy : Float) : String :=
  String.intercalate "\n"
    ((List.range 60).map fun i =>
      let a := -3.141592653589793 + twoPi * (Float.ofNat i + 0.5) / 60.0
      rectTag (ox + 8.0 * Float.ofNat i) oy 8.4 24.0 (hsvHex (a / twoPi + 0.5) 1.0 0.95) "" 1.0)

private def brightBar (ox oy : Float) : String :=
  String.intercalate "\n"
    ((List.range 60).map fun i =>
      let m := Float.pow
        (Float.exp (-4.605170185988091 + 9.210340371976184 * (Float.ofNat i + 0.5) / 60.0))
        (1.0 / 3.0)
      let b := m / (1.0 + m)
      rectTag (ox + 8.0 * Float.ofNat i) oy 8.4 24.0 (hsvHex 0.0 0.0 (0.48 + 0.52 * b)) "" 1.0)

private def claimLines : List String :=
  ["T_j(\u03c4) = \u2211_{n\u22651} tr(j|V\u2099) q\u207f  with  tr(j|V\u2099) = e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074        [mtQ, gradedTrace_natCast]",
   "T_j(\u03c4) = T_0(\u03c4 + j/24) \u2014 the character twist is a translation by 1/24: the 24 strips        [mtQ_eq_shift]",
   "T_j(\u03c4 + 1) = T_j(\u03c4),  T_{j+24} = T_j \u2014 horizontal period 1, and the 24 strips close up        [mtQ_period_one, mtQ_period_24]",
   "T_j(\u03c4) = w/(1 \u2212 w),  w = e\u00b2\u03c0\u2071\u207d\u03c4\u207a\u02b2\u141f\u00b2\u2074\u207e \u2014 the closed form evaluated at every pixel        [mtQ_eq_div]",
   "|T_j(\u03c4) \u2212 w| \u2264 |w|\u00b2/(1\u2212|w|),  |w| = e\u207b\u00b2\u03c0\u1d35\u1d50\u03c4 \u2014 high up, the leading term dictates the colour        [norm_mtQ_sub_leading_le]",
   "T_0(\u03c4), \u2026, T_23(\u03c4) are pairwise distinct at every point of \u210d        [mtQ_injOn]",
   "T_12(\u03c4) = T_0(\u03c4 + 1/2) = \u2211 (\u22121)\u207f q\u207f \u2014 the order-two twist, a half-period shift        [mtQ_twelve_eq_half_shift]",
   "hue = arg/2\u03c0 \u2208 (\u22121/2, 1/2],  brightness = |z|/(1+|z|) \u2208 [0,1), strictly increasing in |z|        [hue_mem_Ioc, brightness_lt_brightness]",
   "\u0394 = \u03b7\u00b2\u2074 = q\u220f(1\u2212q\u1d50)\u00b2\u2074 is the modular form whose coefficients \u03c4(n) the rest of the project studies        [RamanujanTau]"]

def domainColoringSvg : String :=
  let head :=
    "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1760\" height=\"1000\" " ++
      "viewBox=\"0 0 1760 1000\">\n" ++
    "  <rect width=\"1760\" height=\"1000\" fill=\"#f8fafc\"/>\n" ++
    textTag 880.0 54.0 30 "#0f172a" "middle" "700"
      "McKay\u2013Thompson series of the \u03b6-moonshine module on the upper half-plane" ++ "\n" ++
    textTag 880.0 88.0 17 "#334155" "middle" "400"
      ("domain colouring:  hue = arg,  brightness = |\u00b7| ;   q = e\u00b2\u03c0\u2071\u03c4,   " ++
       "T_j(\u03c4) = \u2211_{n\u22651} e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 q\u207f = w/(1\u2212w),  w = e\u00b2\u03c0\u2071\u207d\u03c4\u207a\u02b2\u141f\u00b2\u2074\u207e") ++ "\n" ++
    textTag 880.0 114.0 15 "#64748b" "middle" "400"
      "window:  Re \u03c4 \u2208 [0, 1] (one period),  Im \u03c4 \u2208 [0.045, 0.845];  120 \u00d7 95 cells per panel"
  let panel1 :=
    phasePanel domainColor 90 180 nxH nyH cellH 0.0 1.0 imLo imHi (fun x y => mtQF 0 x y)
  let panel2 :=
    phasePanel domainColor 640 180 nxH nyH cellH 0.0 1.0 imLo imHi (fun x y => mtQF 12 x y)
  let panel3 :=
    phasePanel domainColor 1190 180 nxH nyH cellH 0.0 1.0 imLo imHi (fun x y => deltaF 20 x y)
  let overlays :=
    String.intercalate "\n"
      [stripOverlay px0, stripLabels px0,
       frameTag px0 pTop pw ph, frameTag px1 pTop pw ph, frameTag px2 pTop pw ph,
       reTicks px0, reTicks px1, reTicks px2, imTicks px0,
       textTag (px0 + pw / 2.0) (pTop - 14.0) 19 "#0f172a" "middle" "700" "T\u2080(\u03c4) = \u2211 q\u207f",
       textTag (px1 + pw / 2.0) (pTop - 14.0) 19 "#0f172a" "middle" "700"
         "T\u2081\u2082(\u03c4) = \u2211 (\u22121)\u207f q\u207f",
       textTag (px2 + pw / 2.0) (pTop - 14.0) 19 "#0f172a" "middle" "700"
         "\u0394(\u03c4) = \u03b7(\u03c4)\u00b2\u2074",
       textTag (px0 + pw / 2.0) (pTop + ph + 60.0) 14 "#334155" "middle" "400"
         "the identity element:  T\u2080 = \u03b6 on the s-side",
       textTag (px0 + pw / 2.0) (pTop + ph + 80.0) 14 "#334155" "middle" "400"
         "white lines: the 24 strips of width 1/24 (label = j)",
       textTag (px1 + pw / 2.0) (pTop + ph + 60.0) 14 "#334155" "middle" "400"
         "the order-two twist:  T\u2081\u2082(\u03c4) = T\u2080(\u03c4 + 1/2)",
       textTag (px1 + pw / 2.0) (pTop + ph + 80.0) 14 "#334155" "middle" "400"
         "on the s-side:  T\u2081\u2082(s) = (2\u00b9\u207b\u02e2 \u2212 1) \u03b6(s)",
       textTag (px2 + pw / 2.0) (pTop + ph + 60.0) 14 "#334155" "middle" "400"
         "a genuine modular form (weight 12), for comparison",
       textTag (px2 + pw / 2.0) (pTop + ph + 80.0) 14 "#334155" "middle" "400"
         "product truncated at m \u2264 20",
       textTag (px0 + pw / 2.0) (pTop + ph + 38.0) 14 "#0f172a" "middle" "400" "Re \u03c4",
       textTag (px0 - 52.0) (pTop + ph / 2.0) 14 "#0f172a" "middle" "400" "Im \u03c4"]
  let legend :=
    String.intercalate "\n"
      [hueBar 90.0 700.0,
       textTag 90.0 748.0 13 "#334155" "start" "400" "\u2212\u03c0",
       textTag 330.0 748.0 13 "#334155" "middle" "400" "0",
       textTag 570.0 748.0 13 "#334155" "end" "400" "\u03c0",
       textTag 90.0 690.0 15 "#0f172a" "start" "700" "hue  =  arg T_j(\u03c4)",
       brightBar 90.0 790.0,
       textTag 90.0 838.0 13 "#334155" "start" "400" "|T| = 0.01",
       textTag 330.0 838.0 13 "#334155" "middle" "400" "1",
       textTag 570.0 838.0 13 "#334155" "end" "400" "100",
       textTag 90.0 780.0 15 "#0f172a" "start" "700"
         ("brightness  increasing in  |T_j(\u03c4)|  (m\u141f\u00b3/(1+m\u141f\u00b3), m = |T_j|), " ++
          " banded on the powers of 2 of |T_j|"),
       textTag 90.0 890.0 14 "#64748b" "start" "400"
         ("the pole of T\u2080 at q = 1 (\u03c4 \u2192 0 along the real axis) is the white/dark " ++
          "singularity at the bottom edge; each twist moves it to \u03c4 = \u2212j/24")]
  let claims :=
    String.intercalate "\n"
      (textTag 640.0 690.0 16 "#0f172a" "start" "700"
        "what the picture claims, proved in RequestProject/MoonshineBridge.lean :" ::
       (claimLines.zipIdx.map fun (line, i) =>
          textTag 640.0 (720.0 + 26.0 * Float.ofNat i) 14 "#334155" "start" "400"
            ("\u2022  " ++ line)))
  head ++ "\n  <g shape-rendering=\"crispEdges\">\n" ++ panel1 ++ "\n" ++ panel2 ++ "\n" ++
    panel3 ++ "\n  </g>\n" ++ overlays ++ "\n" ++ legend ++ "\n" ++ claims ++ "\n</svg>\n"

/-! ## Picture 2 : the `s`-plane -/

/-- `2^{1-s}` at `s = σ + it`. -/
def twoPow1ms (sigma t : Float) : C :=
  let l2 := 0.6931471805599453
  cscale (Float.exp ((1.0 - sigma) * l2)) (cexpi (-(t * l2)))

/-- The truncation length of every Dirichlet series in the trajectory plot. -/
def trajK : Nat := 500

/-- The number of sample points of the trajectories. -/
def trajN : Nat := 600

/-- The largest `t` plotted. -/
def trajT : Float := 30.0

def trajPts (j : Nat) : List C :=
  (List.range (trajN + 1)).map fun k => mtSF j trajK 0.5 (trajT * Float.ofNat k / Float.ofNat trajN)

private def trOX : Float := 90.0
private def trOY : Float := 150.0
private def trS : Float := 620.0
private def trR : Float := 11.0

private def trX (re : Float) : Float := trOX + trS / 2.0 + trS * re / (2.0 * trR)
private def trY (im : Float) : Float := trOY + trS / 2.0 - trS * im / (2.0 * trR)

private def trajPath (j : Nat) (colour : String) (width : Float) : String :=
  polylineTag ((trajPts j).map fun z => (trX z.1, trY z.2)) colour width

private def trajGrid : String :=
  String.intercalate "\n"
    (([-10.0, -5.0, 5.0, 10.0].flatMap fun v =>
        [lineTag (trX v) trOY (trX v) (trOY + trS) "#cbd5e1" 0.8 "3 3",
         lineTag trOX (trY v) (trOX + trS) (trY v) "#cbd5e1" 0.8 "3 3",
         textTag (trX v) (trY 0.0 + 16.0) 12 "#64748b" "middle" "400" (fmtFixed 0 v),
         textTag (trX 0.0 - 8.0) (trY v + 4.0) 12 "#64748b" "end" "400" (fmtFixed 0 v)]) ++
     [lineTag trOX (trY 0.0) (trOX + trS) (trY 0.0) "#0f172a" 1.0 "5 4",
      lineTag (trX 0.0) trOY (trX 0.0) (trOY + trS) "#0f172a" 1.0 "5 4",
      rectTag trOX trOY trS trS "none" "#0f172a" 1.0])

/-- The marks at `t = 5, 10, …, 30` on the two main trajectories. -/
private def trajMarks (j : Nat) (colour : String) : String :=
  String.intercalate "\n"
    (([5.0, 10.0, 15.0, 20.0, 25.0, 30.0] : List Float).map fun t =>
      let z := mtSF j trajK 0.5 t
      circleTag (trX z.1) (trY z.2) 3.4 colour "#ffffff" ++ "\n" ++
      textTag (trX z.1 + 9.0) (trY z.2 - 7.0) 11 colour "start" "700" (fmtFixed 0 t))

private def sPanelY : Float := 150.0
private def sPanelW : Float := 400.0
private def sPanelH : Float := 480.0
private def sx0 : Float := 830.0
private def sx1 : Float := 1290.0
private def sigLo : Float := 0.0
private def sigHi : Float := 2.5
private def tHi : Float := 40.0

private def sX (ox sigma : Float) : Float := ox + sPanelW * (sigma - sigLo) / (sigHi - sigLo)
private def sY (t : Float) : Float := sPanelY + sPanelH * (tHi - t) / tHi

private def sPanelAxes (ox : Float) : String :=
  String.intercalate "\n"
    ([rectTag ox sPanelY sPanelW sPanelH "none" "#0f172a" 1.0,
      lineTag (sX ox 0.5) sPanelY (sX ox 0.5) (sPanelY + sPanelH) "#ffffff" 1.6 "6 4",
      textTag (sX ox 0.5) (sPanelY - 8.0) 12 "#0f172a" "middle" "700" "\u03c3 = 1/2"] ++
     ([(0.0, "0"), (0.5, "1/2"), (1.0, "1"), (2.0, "2"), (2.5, "2.5")].map fun (v, lab) =>
        textTag (sX ox v) (sPanelY + sPanelH + 18.0) 12 "#334155" "middle" "400" lab) ++
     [textTag (ox + sPanelW / 2.0) (sPanelY + sPanelH + 38.0) 13 "#0f172a" "middle" "400"
        "\u03c3 = Re s"])

private def sPanelTTicks (ox : Float) : String :=
  String.intercalate "\n"
    (([0.0, 10.0, 20.0, 30.0, 40.0] : List Float).map fun t =>
      textTag (ox - 10.0) (sY t + 4.0) 12 "#334155" "end" "400" (fmtFixed 0 t))

/-- The zeros of the order-two factor `2^{1-s} - 1`, at `s = 1 + 2\u03c0ik/log 2`
(`MoonshineBridge.two_cpow_one_sub_eq_one`); their spacing is `2\u03c0/log 2 = 9.0647...`. -/
private def etaZeroMarks : String :=
  String.intercalate "\n"
    (([1, 2, 3, 4] : List Nat).map fun k =>
      let t := 9.064720283654388 * Float.ofNat k
      circleTag (sX sx1 1.0) (sY t) 5.0 "none" "#ffffff")

/-- The numeric check of `MoonshineBridge.altPartial_eq` printed on the picture, at
`s = 1/2 + 7i` with `M = 250`. -/
def checkLHS : C := mtSF 12 500 0.5 7.0
def checkRHS : C :=
  csub (cmul (twoPow1ms 0.5 7.0) (mtSF 0 250 0.5 7.0)) (mtSF 0 500 0.5 7.0)

private def cstr (z : C) : String :=
  fmtFixed 6 z.1 ++ (if z.2 < 0.0 then " - " ++ fmtFixed 6 (-z.2) else " + " ++ fmtFixed 6 z.2)
    ++ "i"

private def sClaimLines : List String :=
  ["T_j(s) = \u2211_{n\u22651} tr(j|V\u2099) n\u207b\u02e2  \u2014 the same graded module, in the Dirichlet grading        [ZetaMoonshine.mtSeries]",
   "T_0(s) = \u03b6(s) \u2014 the identity element gives back the moonshine function, as T_1 = J for the Monster        [mtSeries_zero_eq_riemannZeta]",
   "T_12(s) = \u2211 (\u22121)\u207f n\u207b\u02e2 = (2\u00b9\u207b\u02e2 \u2212 1) \u03b6(s) \u2014 the order-two twist is the Dirichlet eta function        [mtSeries_twelve]",
   "\u2211_{n\u22642M} (\u22121)\u207f n\u207b\u02e2 = 2\u00b9\u207b\u02e2 \u2211_{m\u2264M} m\u207b\u02e2 \u2212 \u2211_{n\u22642M} n\u207b\u02e2 \u2014 exact at every truncation, which is what is plotted        [altPartial_eq]",
   "the 24 series are pairwise distinct, and \u03b6 = \u2211_a (isotypic component)        [gradedTrace_injective, riemannZeta_eq_sum_isotypic]"]

def trajectorySvg : String :=
  let head :=
    "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1760\" height=\"1180\" " ++
      "viewBox=\"0 0 1760 1180\">\n" ++
    "  <rect width=\"1760\" height=\"1180\" fill=\"#f8fafc\"/>\n" ++
    "  <defs><clipPath id=\"trajclip\"><rect x=\"90\" y=\"150\" width=\"620\" height=\"620\"/>" ++
      "</clipPath></defs>\n" ++
    textTag 880.0 54.0 30 "#0f172a" "middle" "700"
      "The same series on the s-plane:  T_j(s) = \u2211 e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 n\u207b\u02e2" ++ "\n" ++
    textTag 880.0 88.0 17 "#334155" "middle" "400"
      ("left: the trajectories of T_j(1/2 + it) in \u2102 for t : 0 \u2192 30 (truncated at n \u2264 500);  " ++
       "right: domain colouring of the same partial sums on the s-plane") ++ "\n" ++
    textTag 880.0 114.0 15 "#64748b" "middle" "400"
      "same colour rule as the upper-half-plane picture:  hue = arg,  brightness increasing in |\u00b7|"
  let traj :=
    String.intercalate "\n"
      [trajGrid,
       "  <g clip-path=\"url(#trajclip)\">",
       trajPath 6 "#a78bfa" 1.2,
       trajPath 8 "#6ee7b7" 1.2,
       trajPath 0 "#1f4fd8" 2.0,
       trajPath 12 "#c81e30" 2.0,
       trajMarks 0 "#1f4fd8",
       trajMarks 12 "#c81e30",
       "  </g>",
       textTag (trOX + trS / 2.0) (trOY - 14.0) 19 "#0f172a" "middle" "700"
         "T_j(1/2 + it),  t : 0 \u2192 30",
       textTag (trOX + trS + 6.0) (trY 0.0 + 16.0) 12 "#64748b" "start" "400" "Re T_j",
       textTag (trX 0.0 + 8.0) (trOY + 14.0) 12 "#64748b" "start" "400" "Im T_j",
       textTag trOX (trOY + trS + 28.0) 14 "#1f4fd8" "start" "700"
         "T\u2080(s) = \u03b6(s)  (Riemann zeta)",
       textTag trOX (trOY + trS + 50.0) 14 "#c81e30" "start" "700"
         "T\u2081\u2082(s) = (2\u00b9\u207b\u02e2 \u2212 1)\u03b6(s)  (order-two twist)",
       textTag trOX (trOY + trS + 72.0) 13 "#7c5cd6" "start" "400"
         "faint: T\u2086 (order 4) and T\u2088 (order 3)",
       textTag trOX (trOY + trS + 94.0) 13 "#64748b" "start" "400"
         ("dots: t = 5, 10, \u2026, 30.  The T\u2080 curve enters the frame from outside: at t = 0 " ++
          "the truncated \u2211_{n\u2264500} n\u207b\u00b9\u141f\u00b2 = " ++ fmtFixed 3 (mtSF 0 500 0.5 0.0).1 ++ ".")]
  let maps :=
    String.intercalate "\n"
      ["  <g shape-rendering=\"crispEdges\">",
       phasePanel domainColorS 830 150 100 120 4 sigLo sigHi 0.0 tHi (fun sg t => mtSF 0 400 sg t),
       phasePanel domainColorS 1290 150 100 120 4 sigLo sigHi 0.0 tHi (fun sg t => mtSF 12 400 sg t),
       "  </g>",
       sPanelAxes sx0, sPanelAxes sx1, sPanelTTicks sx0,
       lineTag (sX sx0 1.0) sPanelY (sX sx0 1.0) (sPanelY + sPanelH) "#0f172a" 1.0 "2 4",
       lineTag (sX sx1 1.0) sPanelY (sX sx1 1.0) (sPanelY + sPanelH) "#0f172a" 1.0 "2 4",
       etaZeroMarks,
       textTag (sx0 - 40.0) (sPanelY + sPanelH / 2.0) 13 "#0f172a" "middle" "400" "t",
       textTag (sx0 + sPanelW / 2.0) (sPanelY - 30.0) 18 "#0f172a" "middle" "700"
         "T\u2080(s)  \u2192  \u03b6(s)",
       textTag (sx1 + sPanelW / 2.0) (sPanelY - 30.0) 18 "#0f172a" "middle" "700"
         "T\u2081\u2082(s)  \u2192  (2\u00b9\u207b\u02e2\u22121)\u03b6(s)",
       textTag (sx0 + sPanelW / 2.0) (sPanelY + sPanelH + 60.0) 13 "#334155" "middle" "400"
         "partial sum \u2211_{n\u2264400} n\u207b\u02e2 on \u03c3 \u2208 [0, 2.5], t \u2208 [0, 40]",
       textTag (sx1 + sPanelW / 2.0) (sPanelY + sPanelH + 60.0) 13 "#334155" "middle" "400"
         "partial sum \u2211_{n\u2264400} (\u22121)\u207f n\u207b\u02e2 on the same window",
       textTag (sx0 + sPanelW / 2.0) (sPanelY + sPanelH + 82.0) 13 "#64748b" "middle" "400"
         ("the series converges to \u03b6 only right of \u03c3 = 1 (dotted); " ++
          "left of it this is the truncated series itself"),
       textTag (sx1 + sPanelW / 2.0) (sPanelY + sPanelH + 82.0) 13 "#64748b" "middle" "400"
         ("the alternating series converges for \u03c3 > 0;  white rings: the zeros of " ++
          "2\u00b9\u207b\u02e2 \u2212 1 at s = 1 + 2\u03c0ik/log 2  [two_cpow_one_sub_eq_one]")]
  let claims :=
    String.intercalate "\n"
      (textTag 90.0 920.0 16 "#0f172a" "start" "700"
        ("what the picture claims, proved in RequestProject/MoonshineBridge.lean and " ++
         "RequestProject/ZetaMoonshine.lean :") ::
       (sClaimLines.zipIdx.map fun (line, i) =>
          textTag 90.0 (952.0 + 26.0 * Float.ofNat i) 14 "#334155" "start" "400"
            ("\u2022  " ++ line)) ++
       [textTag 90.0 (952.0 + 26.0 * 5.0 + 14.0) 14 "#0f172a" "start" "700"
          ("numeric check of the fourth line at s = 1/2 + 7i, M = 250:   left  = " ++
           cstr checkLHS),
        textTag 90.0 (952.0 + 26.0 * 6.0 + 14.0) 14 "#0f172a" "start" "700"
          ("                                                            right = " ++
           cstr checkRHS)])
  head ++ "\n" ++ traj ++ "\n" ++ maps ++ "\n" ++ claims ++ "\n</svg>\n"

/-! ## The table -/

def trajectoryCsv : String :=
  let rows := (List.range 121).map fun k =>
    let t := 0.25 * Float.ofNat k
    let z0 := mtSF 0 trajK 0.5 t
    let z12 := mtSF 12 trajK 0.5 t
    let rhs := csub (cmul (twoPow1ms 0.5 t) (mtSF 0 250 0.5 t)) (mtSF 0 500 0.5 t)
    String.intercalate ","
      [fmtFixed 2 t, fmtFixed 6 z0.1, fmtFixed 6 z0.2, fmtFixed 6 (cabs z0),
       fmtFixed 6 z12.1, fmtFixed 6 z12.2, fmtFixed 6 (cabs z12),
       fmtFixed 6 rhs.1, fmtFixed 6 rhs.2]
  String.intercalate "\n"
    (("t,re_T0,im_T0,abs_T0,re_T12,im_T12,abs_T12,re_rhs_altPartial,im_rhs_altPartial" ::
      rows)) ++ "\n"

end MoonshineSvg

/-
# The first pane of `moonshine-trajectories.svg`, zoomed

This renders `visualization/moonshine-trajectories-zoom.svg`: a detailed view of the spiral
pane of `visualization/moonshine-trajectories.svg`, i.e. of the curves

```
t ↦ T_j(1/2 + it) = ∑_{n ≤ 500} e^{2πijn/24} n^{-1/2-it},   t : 0 → 30.
```

Four panels:

* **A** — the central window `|Re|, |Im| ≤ 3.6` of the original pane (which was `± 11`), with the
  curves drawn from 1800 samples and coloured along `t`, a tick every `Δt = 1`, and the three
  first Riemann zeros marked; an inset shows the original frame and this zoom box.
* **B** — a further zoom, `|Re|, |Im| ≤ 0.4`, on the passages of `T_12` next to the origin: since
  `T_12(s) = (2^{1−s} − 1) ζ(s)`, they happen exactly at the zeros of `ζ`.
* **C** — the spiral itself: the partial-sum polygon `∑_{n ≤ N} n^{-1/2-it}`, `N = 1 … 500`, at a
  fixed `t`; its step lengths are `n^{-1/2}` and it turns by `t·log((n+1)/n)` at the `n`-th
  vertex, a total turning of `t·log N` (`MoonshineZoom.sum_turn`).
* **D** — `|T_0|` and `|T_12|` against `t`, with the dips at the Riemann zeros.

Only floating-point geometry and string manipulation live here; the structural claims written
on the picture are proved in `RequestProject/MoonshineZoom.lean`.
-/
import RequestProject.MoonshineZoom
import RequestProject.MoonshineBridgeSvg

namespace MoonshineZoomSvg

open SporadicSvg MoonshineSvg

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## Sampling the curves -/

/-- The truncation length used everywhere in this picture. -/
def zK : Nat := 500

/-- `T_j(1/2 + it)` for `t = t0, …, t1` in `steps` steps. -/
def sampleCurve (j : Nat) (t0 t1 : Float) (steps : Nat) : List C :=
  (List.range (steps + 1)).map fun k =>
    mtSF j zK 0.5 (t0 + (t1 - t0) * Float.ofNat k / Float.ofNat steps)

/-- The first three nontrivial zeros of `ζ` (their ordinates). -/
def zeroTs : List Float := [14.134725, 21.022040, 25.010858]

/-! ## Colour ramps along the parameter -/

/-- Deep blue → violet, as `t` runs from `0` to `30`: the `T_0 = ζ` curve. -/
def rampZeta (u : Float) : String := hsvHex (0.62 + 0.16 * u) (0.95 - 0.25 * u) (0.55 + 0.35 * u)

/-- Crimson → amber: the `T_12` curve. -/
def rampAlt (u : Float) : String := hsvHex (0.99 + 0.11 * u) (0.95 - 0.20 * u) (0.62 + 0.30 * u)

/-- A polyline whose segments are coloured by the position along the curve. -/
def gradPath (pts : List C) (proj : C → Float × Float) (ramp : Float → String) (w : Float) :
    String :=
  let n := pts.length
  let arr := pts.toArray
  String.intercalate "\n"
    ((List.range (n - 1)).map fun k =>
      let p := proj (arr.getD k (0.0, 0.0))
      let q := proj (arr.getD (k + 1) (0.0, 0.0))
      let u := Float.ofNat k / Float.ofNat (max 1 (n - 1))
      lineTag p.1 p.2 q.1 q.2 (ramp u) w "")

/-! ## Panel A : the central window of the original pane -/

private def aOX : Float := 90.0
private def aOY : Float := 205.0
private def aS : Float := 700.0
private def aR : Float := 3.6

private def aX (re : Float) : Float := aOX + aS / 2.0 + aS * re / (2.0 * aR)
private def aY (im : Float) : Float := aOY + aS / 2.0 - aS * im / (2.0 * aR)
private def aP (z : C) : Float × Float := (aX z.1, aY z.2)

private def aGrid : String :=
  String.intercalate "\n"
    ((([-3.0, -2.0, -1.0, 1.0, 2.0, 3.0] : List Float).flatMap fun v =>
        [lineTag (aX v) aOY (aX v) (aOY + aS) "#e2e8f0" 0.9 "3 3",
         lineTag aOX (aY v) (aOX + aS) (aY v) "#e2e8f0" 0.9 "3 3",
         textTag (aX v) (aY 0.0 + 15.0) 11 "#94a3b8" "middle" "400" (fmtFixed 0 v),
         textTag (aX 0.0 - 7.0) (aY v + 4.0) 11 "#94a3b8" "end" "400" (fmtFixed 0 v)]) ++
     (([0.5, 1.0, 2.0, 3.0] : List Float).map fun r =>
        circleTag (aX 0.0) (aY 0.0) (aS * r / (2.0 * aR)) "none" "#f1f5f9") ++
     [lineTag aOX (aY 0.0) (aOX + aS) (aY 0.0) "#0f172a" 1.0 "6 4",
      lineTag (aX 0.0) aOY (aX 0.0) (aOY + aS) "#0f172a" 1.0 "6 4",
      rectTag aOX aOY aS aS "none" "#0f172a" 1.0])

/-- The tick dots at `t = 1, 2, …, 30` on a curve, with the multiples of 5 labelled. -/
private def aTicks (j : Nat) (dot lab : String) (dx dy : Float) : String :=
  String.intercalate "\n"
    ((List.range 30).map fun k =>
      let t := Float.ofNat (k + 1)
      let z := mtSF j zK 0.5 t
      let big := (k + 1) % 5 == 0
      circleTag (aX z.1) (aY z.2) (if big then 3.6 else 1.9) dot "#ffffff" ++
        (if big then
          "\n" ++ textTag (aX z.1 + dx) (aY z.2 + dy) 12 lab "start" "700" (fmtFixed 0 t)
         else ""))

/-- A ring on `T_12` at each of the first three zeros of `ζ` — all three sit on top of the
origin at this magnification, which is what panel B opens up. -/
private def aZeroRings : String :=
  String.intercalate "\n"
    ((zeroTs.map fun t =>
        let z := mtSF 12 zK 0.5 t
        circleTag (aX z.1) (aY z.2) 10.0 "none" "#0f172a") ++
     [lineTag (aX 0.0 + 10.0) (aY 0.0) (aX 1.15) (aY 0.72) "#0f172a" 0.9 "3 2",
      rectTag (aX 1.18) (aY 0.72 - 15.0) 118.0 19.0 "#ffffff" "none" 0.85,
      textTag (aX 1.22) (aY 0.72 - 2.0) 12 "#0f172a" "start" "700"
        "\u03c1\u2081, \u03c1\u2082, \u03c1\u2083  (panel B)"])

/-- The inset: the whole original frame `|Re|, |Im| ≤ 11` with this zoom box drawn on it. -/
private def aInset : String :=
  let ix := aOX + 14.0
  let iy := aOY + 14.0
  let isz := 168.0
  let iR := 11.0
  let px : Float → Float := fun re => ix + isz / 2.0 + isz * re / (2.0 * iR)
  let py : Float → Float := fun im => iy + isz / 2.0 - isz * im / (2.0 * iR)
  let pp : C → Float × Float := fun z => (px z.1, py z.2)
  String.intercalate "\n"
    [rectTag ix iy isz isz "#ffffff" "#94a3b8" 0.92,
     lineTag ix (py 0.0) (ix + isz) (py 0.0) "#cbd5e1" 0.8 "",
     lineTag (px 0.0) iy (px 0.0) (iy + isz) "#cbd5e1" 0.8 "",
     "  <g clip-path=\"url(#zinset)\">",
     polylineTag ((sampleCurve 0 0.0 30.0 700).map pp) "#1f4fd8" 0.7,
     polylineTag ((sampleCurve 12 0.0 30.0 700).map pp) "#c81e30" 0.7,
     "  </g>",
     rectTag (px (-aR)) (py aR) (isz * aR / iR) (isz * aR / iR) "none" "#0f172a" 1.0,
     textTag (ix + isz / 2.0) (iy + isz + 15.0) 11 "#475569" "middle" "400"
       "the original pane (\u00b111);  box = this zoom"]

private def panelA : String :=
  String.intercalate "\n"
    [aGrid,
     "  <g clip-path=\"url(#zclipA)\">",
     gradPath (sampleCurve 6 0.0 30.0 900) aP (fun _ => "#ddd6fe") 0.9,
     gradPath (sampleCurve 8 0.0 30.0 900) aP (fun _ => "#ccfbf1") 0.9,
     gradPath (sampleCurve 0 0.0 30.0 1800) aP rampZeta 2.1,
     gradPath (sampleCurve 12 0.0 30.0 1800) aP rampAlt 2.1,
     aTicks 0 "#1e3a8a" "#1e3a8a" 7.0 (-8.0),
     aTicks 12 "#9f1239" "#9f1239" 7.0 14.0,
     aZeroRings,
     "  </g>",
     aInset,
     textTag (aOX + aS / 2.0) (aOY - 44.0) 21 "#0f172a" "middle" "700"
       "A.   T_j(1/2 + it),  t : 0 \u2192 30,  zoomed to |Re|, |Im| \u2264 3.6",
     textTag (aOX + aS / 2.0) (aOY - 22.0) 14 "#475569" "middle" "400"
       ("blue \u2192 violet: T\u2080 = \u03b6 ;   crimson \u2192 amber: T\u2081\u2082 = (2\u00b9\u207b\u02e2\u22121)\u03b6 ;   " ++
        "faint: T\u2086, T\u2088 ;   1800 samples, \u0394t = 1/60"),
     textTag (aOX + aS + 6.0) (aY 0.0 + 15.0) 11 "#64748b" "start" "400" "Re",
     textTag (aX 0.0 + 7.0) (aOY + 13.0) 11 "#64748b" "start" "400" "Im"]

/-! ## Panel B : the passages of `T_12` next to the origin -/

private def bOX : Float := 880.0
private def bOY : Float := 205.0
private def bS : Float := 380.0
private def bR : Float := 0.4

private def bX (re : Float) : Float := bOX + bS / 2.0 + bS * re / (2.0 * bR)
private def bY (im : Float) : Float := bOY + bS / 2.0 - bS * im / (2.0 * bR)
private def bP (z : C) : Float × Float := (bX z.1, bY z.2)

private def bGrid : String :=
  String.intercalate "\n"
    ((([-0.3, -0.2, -0.1, 0.1, 0.2, 0.3] : List Float).flatMap fun v =>
        [lineTag (bX v) bOY (bX v) (bOY + bS) "#e2e8f0" 0.8 "3 3",
         lineTag bOX (bY v) (bOX + bS) (bY v) "#e2e8f0" 0.8 "3 3"]) ++
     (([0.1, 0.2, 0.3] : List Float).map fun r =>
        circleTag (bX 0.0) (bY 0.0) (bS * r / (2.0 * bR)) "none" "#e2e8f0") ++
     [lineTag bOX (bY 0.0) (bOX + bS) (bY 0.0) "#0f172a" 0.9 "6 4",
      lineTag (bX 0.0) bOY (bX 0.0) (bOY + bS) "#0f172a" 0.9 "6 4",
      textTag (bX 0.3) (bY 0.0 + 14.0) 11 "#94a3b8" "middle" "400" "0.3",
      textTag (bX 0.0 - 6.0) (bY 0.3 + 4.0) 11 "#94a3b8" "end" "400" "0.3",
      rectTag bOX bOY bS bS "none" "#0f172a" 1.0])

/-- The three near-origin passages, sampled finely on `t ∈ [ρ − 0.7, ρ + 0.7]`. -/
private def bPasses : String :=
  String.intercalate "\n"
    (zeroTs.flatMap fun t0 =>
      [gradPath (sampleCurve 12 (t0 - 0.7) (t0 + 0.7) 700) bP rampAlt 2.0])

/-- The three closest approaches, with a leader line to a label placed away from the origin. -/
private def bMarks : String :=
  let offs : List (Float × Float) := [(-0.26, 0.22), (0.20, 0.26), (0.24, -0.20)]
  String.intercalate "\n"
    ((zeroTs.zipIdx.flatMap fun (t, i) =>
      let z := mtSF 12 zK 0.5 t
      let o := offs.getD i (0.0, 0.0)
      [lineTag (bX z.1) (bY z.2) (bX o.1) (bY o.2) "#0f172a" 0.8 "3 2",
       circleTag (bX z.1) (bY z.2) 4.2 "#9f1239" "#ffffff",
       textTag (bX o.1) (bY o.2 - 6.0) 13 "#0f172a" "middle" "700"
         ("\u03c1" ++ toString (i + 1))]) ++
     (zeroTs.zipIdx.map fun (t, i) =>
      let z := mtSF 12 zK 0.5 t
      textTag (bOX) (bOY + bS + 62.0 + 19.0 * Float.ofNat i) 13 "#334155" "start" "400"
        ("\u03c1" ++ toString (i + 1) ++ " :  t = " ++ fmtFixed 6 t ++ ",   |T\u2081\u2082| = " ++
          fmtFixed 4 (cabs z) ++ ",   |T\u2080| = " ++ fmtFixed 4 (cabs (mtSF 0 zK 0.5 t)))))

private def panelB : String :=
  String.intercalate "\n"
    [bGrid,
     "  <g clip-path=\"url(#zclipB)\">",
     gradPath (sampleCurve 0 0.0 30.0 1400) bP (fun _ => "#bfdbfe") 1.2,
     gradPath (sampleCurve 12 0.0 30.0 1800) bP (fun _ => "#fecdd3") 1.2,
     bPasses,
     "  </g>",
     bMarks,
     circleTag (bX 0.0) (bY 0.0) 2.6 "#0f172a" "#0f172a",
     textTag (bOX + bS / 2.0) (bOY - 44.0) 20 "#0f172a" "middle" "700"
       "B.   zoomed again:  |Re|, |Im| \u2264 0.4",
     textTag (bOX + bS / 2.0) (bOY - 22.0) 14 "#475569" "middle" "400"
       "T\u2081\u2082 grazes 0 exactly at the zeros of \u03b6",
     textTag (bOX) (bOY + bS + 24.0) 12 "#334155" "start" "400"
       ("T\u2081\u2082(s) = (2\u00b9\u207b\u02e2 \u2212 1)\u03b6(s) vanishes at every zero \u03c1 of \u03b6;"),
     textTag (bOX) (bOY + bS + 41.0) 12 "#334155" "start" "400"
       ("the \u2248 0.022 left over is the tail n > 500.")]

/-! ## Panel C : the spiral -/

private def cOX : Float := 1330.0
private def cOY : Float := 205.0
private def cS : Float := 380.0
private def cR : Float := 1.45

private def cX (re : Float) : Float := cOX + cS / 2.0 + cS * re / (2.0 * cR)
private def cY (im : Float) : Float := cOY + cS / 2.0 - cS * im / (2.0 * cR)
private def cP (z : C) : Float × Float := (cX z.1, cY z.2)

/-- `t` at which the polygon is drawn: the third zero of `ζ`, where the whole partial sum of
`T_12` is next to `0`. -/
private def cT : Float := 25.010858

/-- The partial sums `∑_{n ≤ N} n^{-1/2-it}`, `N = 0, 1, …, K`: the vertices of the polygon. -/
def polygonPts (t : Float) (K : Nat) : List C :=
  (List.range (K + 1)).map fun m => mtSF 0 m 0.5 t

private def cGrid : String :=
  String.intercalate "\n"
    ((([-1.0, -0.5, 0.5, 1.0] : List Float).flatMap fun v =>
        [lineTag (cX v) cOY (cX v) (cOY + cS) "#e2e8f0" 0.8 "3 3",
         lineTag cOX (cY v) (cOX + cS) (cY v) "#e2e8f0" 0.8 "3 3"]) ++
     [lineTag cOX (cY 0.0) (cOX + cS) (cY 0.0) "#0f172a" 0.9 "6 4",
      lineTag (cX 0.0) cOY (cX 0.0) (cOY + cS) "#0f172a" 0.9 "6 4",
      textTag (cX 1.0) (cY 0.0 + 14.0) 11 "#94a3b8" "middle" "400" "1",
      textTag (cX 0.0 - 6.0) (cY 1.0 + 4.0) 11 "#94a3b8" "end" "400" "1",
      rectTag cOX cOY cS cS "none" "#0f172a" 1.0])

private def cMarks : String :=
  String.intercalate "\n"
    (([1, 2, 3, 5, 12, 60, 500] : List Nat).map fun m =>
      let z := mtSF 0 m 0.5 cT
      circleTag (cX z.1) (cY z.2) 3.0 "#0f172a" "#ffffff" ++ "\n" ++
      textTag (cX z.1 + 7.0) (cY z.2 - 6.0) 11 "#0f172a" (if m == 1 then "end" else "start")
        "700" ("N=" ++ toString m))

private def panelC : String :=
  String.intercalate "\n"
    [cGrid,
     "  <g clip-path=\"url(#zclipC)\">",
     gradPath (polygonPts cT zK) cP
       (fun u => hsvHex (0.55 - 0.55 * u) (0.85) (0.35 + 0.55 * u)) 1.5,
     cMarks,
     "  </g>",
     textTag (cOX + cS / 2.0) (cOY - 44.0) 20 "#0f172a" "middle" "700"
       "C.   where the spiralling comes from",
     textTag (cOX + cS / 2.0) (cOY - 22.0) 14 "#475569" "middle" "400"
       ("the polygon \u2211_{n \u2264 N} n\u207b\u00b9\u141f\u00b2\u207b\u2071\u1d57 at fixed t = 25.010858 (= \u03c1\u2083)"),
     textTag (cOX) (cOY + cS + 24.0) 12 "#334155" "start" "400"
       ("step n: length n\u207b\u00b9\u141f\u00b2, turn t\u00b7log((n+1)/n)"),
     textTag (cOX) (cOY + cS + 41.0) 12 "#334155" "start" "400"
       ("total turning t\u00b7log 500 = " ++ fmtFixed 2 (cT * Float.log 500.0) ++
        " rad = " ++ fmtFixed 2 (cT * Float.log 500.0 / twoPi) ++ " turns"),
     textTag (cOX) (cOY + cS + 58.0) 12 "#334155" "start" "400"
       ("[sum_turn];  outer loops of radius \u2248 \u221aN/t = " ++
        fmtFixed 3 (Float.sqrt 500.0 / cT))]

/-! ## Panel D : the moduli against `t` -/

private def dOX : Float := 880.0
private def dOY : Float := 745.0
private def dW : Float := 830.0
private def dH : Float := 190.0
private def dTMax : Float := 30.0
private def dVMax : Float := 3.6

private def dX (t : Float) : Float := dOX + dW * t / dTMax
private def dY (v : Float) : Float := dOY + dH - dH * v / dVMax

private def dGrid : String :=
  String.intercalate "\n"
    ((([0.0, 5.0, 10.0, 15.0, 20.0, 25.0, 30.0] : List Float).flatMap fun t =>
        [lineTag (dX t) dOY (dX t) (dOY + dH) "#e2e8f0" 0.8 "3 3",
         textTag (dX t) (dOY + dH + 16.0) 12 "#475569" "middle" "400" (fmtFixed 0 t)]) ++
     (([1.0, 2.0, 3.0] : List Float).flatMap fun v =>
        [lineTag dOX (dY v) (dOX + dW) (dY v) "#e2e8f0" 0.8 "3 3",
         textTag (dOX - 8.0) (dY v + 4.0) 11 "#94a3b8" "end" "400" (fmtFixed 0 v)]) ++
     (zeroTs.map fun t => lineTag (dX t) dOY (dX t) (dOY + dH) "#0f172a" 0.9 "2 3") ++
     [rectTag dOX dOY dW dH "none" "#0f172a" 1.0])

private def dCurve (j : Nat) (colour : String) (w : Float) : String :=
  polylineTag
    ((List.range 1501).map fun k =>
      let t := dTMax * Float.ofNat k / 1500.0
      (dX t, dY (min dVMax (cabs (mtSF j zK 0.5 t)))))
    colour w

private def panelD : String :=
  String.intercalate "\n"
    [dGrid,
     "  <g clip-path=\"url(#zclipD)\">",
     dCurve 0 "#1f4fd8" 1.8,
     dCurve 12 "#c81e30" 1.8,
     "  </g>",
     String.intercalate "\n"
       (zeroTs.zipIdx.map fun (t, i) =>
         textTag (dX t + 4.0) (dOY + 14.0) 12 "#0f172a" "start" "700"
           ("\u03c1" ++ toString (i + 1))),
     textTag (dOX + dW / 2.0) (dOY - 40.0) 21 "#0f172a" "middle" "700"
       "D.   |T\u2080(1/2+it)| and |T\u2081\u2082(1/2+it)| against t",
     textTag (dOX + dW / 2.0) (dOY - 18.0) 14 "#475569" "middle" "400"
       "dotted verticals: the first three zeros of \u03b6 \u2014 the red curve dips to \u2248 0 at each",
     textTag (dOX + dW / 2.0) (dOY + dH + 36.0) 13 "#334155" "middle" "400" "t"]

/-! ## The whole picture -/

private def zoomClaims : List String :=
  ["n\u207b\u207d\u03c3\u207a\u2071\u1d57\u207e = n\u207b\u03c3 e\u207b\u2071\u1d57\u02e1\u1d52\u1d4d\u207f \u2014 the n-th step of the polygon has length n\u207b\u03c3 (= 1/\u221an here) and argument \u2212t\u00b7log n        [cpow_neg_eq_polar, norm_mtTerm]",
   "the step lengths shrink: ‖term n+1‖ \u2264 ‖term n‖ for \u03c3 \u2265 0        [norm_mtTerm_antitone]",
   "consecutive steps differ by a rotation through turn t n = t\u00b7log((n+1)/n), and the scaling (n/(n+1))^\u03c3        [mtTerm_succ_eq]",
   "the turning telescopes: \u2211_{1 \u2264 n \u2264 N−1} t\u00b7log((n+1)/n) = t\u00b7log N \u2014 panel C makes t\u00b7log 500 / 2\u03c0 = 24.74 full turns        [sum_turn]",
   "turn t (n+1) \u2264 turn t n, while the total turning \u2192 \u221e: the spiral opens out and winds forever        [turn_antitone, sum_turn_tendsto_atTop]",
   "the curve's velocity in t is \u2211_{n \u2264 K} (\u2212i log n) e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 n\u207b\u02e2, of size log n \u00b7 n\u207b\u03c3 per term        [hasDerivAt_mtPartial, norm_deriv_term]",
   "T\u2081\u2082(s) = (2\u00b9\u207b\u02e2 \u2212 1)\u03b6(s), so panels B and D see the zeros of \u03b6; T\u2080 = \u03b6, whose partial sums do not converge on the critical line        [mtSeries_twelve, mtSeries_zero_eq_riemannZeta]"]

def zoomSvg : String :=
  let head :=
    "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1760\" height=\"1260\" " ++
      "viewBox=\"0 0 1760 1260\">\n" ++
    "  <rect width=\"1760\" height=\"1260\" fill=\"#f8fafc\"/>\n" ++
    "  <defs>\n" ++
    "    <clipPath id=\"zclipA\"><rect x=\"90\" y=\"205\" width=\"700\" height=\"700\"/></clipPath>\n" ++
    "    <clipPath id=\"zclipB\"><rect x=\"880\" y=\"205\" width=\"380\" height=\"380\"/></clipPath>\n" ++
    "    <clipPath id=\"zclipC\"><rect x=\"1330\" y=\"205\" width=\"380\" height=\"380\"/></clipPath>\n" ++
    "    <clipPath id=\"zclipD\"><rect x=\"880\" y=\"745\" width=\"830\" height=\"190\"/></clipPath>\n" ++
    "    <clipPath id=\"zinset\"><rect x=\"104\" y=\"219\" width=\"168\" height=\"168\"/></clipPath>\n" ++
    "  </defs>\n" ++
    textTag 880.0 52.0 30 "#0f172a" "middle" "700"
      ("Zoom on the trajectory pane:  T_j(1/2 + it) = \u2211_{n \u2264 500} " ++
       "e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 n\u207b\u00b9\u141f\u00b2\u207b\u2071\u1d57") ++ "\n" ++
    textTag 880.0 84.0 17 "#334155" "middle" "400"
      ("the first pane of moonshine-trajectories.svg, magnified: the same 24 McKay\u2013Thompson " ++
       "series of the \u03b6-moonshine module, on the critical line") ++ "\n" ++
    textTag 880.0 110.0 15 "#64748b" "middle" "400"
      ("A: the central 3.6-box of the original \u00b111 frame \u00b7 B: a 0.4-box on the origin \u00b7 " ++
       "C: the partial-sum polygon that produces the spiral \u00b7 D: the moduli")
  let legend :=
    String.intercalate "\n"
      [textTag 90.0 948.0 15 "#1e3a8a" "start" "700"
         "T\u2080(1/2+it) = \u03b6(1/2+it) truncated at n \u2264 500 (blue \u2192 violet as t : 0 \u2192 30)",
       textTag 90.0 970.0 15 "#9f1239" "start" "700"
         "T\u2081\u2082(1/2+it) = (2\u00b9\u207b\u02e2\u22121)\u03b6(1/2+it) truncated (crimson \u2192 amber);  dots every \u0394t = 1, labels every 5",
       textTag 90.0 992.0 14 "#7c5cd6" "start" "400"
         "faint: T\u2086 (order 4) and T\u2088 (order 3) \u2014 the other twists thread the same tangle",
       textTag 90.0 1014.0 14 "#475569" "start" "400"
         ("T\u2080 leaves the box: at t = 0 the truncated \u2211_{n\u2264500} n\u207b\u00b9\u141f\u00b2 = " ++
          fmtFixed 3 (mtSF 0 zK 0.5 0.0).1 ++ ", and it reaches |T\u2080| \u2248 10 near t \u2248 3")]
  let claims :=
    String.intercalate "\n"
      (textTag 90.0 1058.0 16 "#0f172a" "start" "700"
        "what the zoom claims, proved in RequestProject/MoonshineZoom.lean :" ::
       (zoomClaims.zipIdx.map fun (line, i) =>
          textTag 90.0 (1086.0 + 24.0 * Float.ofNat i) 13 "#334155" "start" "400"
            ("\u2022  " ++ line)))
  head ++ "\n" ++ panelA ++ "\n" ++ panelB ++ "\n" ++ panelC ++ "\n" ++ panelD ++ "\n" ++
    legend ++ "\n" ++ claims ++ "\n</svg>\n"

/-! ## The table behind the zoom -/

/-- The polygon of panel C: `N`, the partial sum, its modulus, the step length `N^{-1/2}` and
the turning angle `t·log((N+1)/N)` at the `N`-th vertex, together with the accumulated turning
`t·log N` and the number of turns. -/
def zoomCsv : String :=
  let rows := ([1, 2, 3, 5, 8, 12, 20, 35, 60, 100, 170, 300, 500] : List Nat).map fun m =>
    let z := mtSF 0 m 0.5 cT
    let fm := Float.ofNat m
    String.intercalate ","
      [toString m, fmtFixed 6 z.1, fmtFixed 6 z.2, fmtFixed 6 (cabs z),
       fmtFixed 6 (1.0 / Float.sqrt fm),
       fmtFixed 6 (cT * Float.log ((fm + 1.0) / fm)),
       fmtFixed 6 (cT * Float.log fm),
       fmtFixed 4 (cT * Float.log fm / twoPi)]
  String.intercalate "\n"
    (("N,re_partial,im_partial,abs_partial,step_length,turn_at_N,total_turning,turns" ::
      rows)) ++ "\n"

end MoonshineZoomSvg

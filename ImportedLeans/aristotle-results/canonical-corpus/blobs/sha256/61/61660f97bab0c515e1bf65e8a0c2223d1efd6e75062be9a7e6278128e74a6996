/-
# The spectrum picture: the twenty-six sporadic groups as curves in `s`

`visualization/sporadic-zeta-spectrum.svg` draws, for each of the twenty-six sporadic simple
groups, the curve

```
s ↦ ∑_{d ∣ |G|} d^{-s}  =  ∏_{p^e ‖ |G|} (1 + p^{-s} + ⋯ + p^{-es}),
```

at `s = 1, 2, 3, 4, 5`. The vertical coordinate is `log₁₀ (value - 1)`, the excess over the
trivial divisor `1`, so the collapse of the whole table towards `1` is visible as a descent of
roughly one decade every two steps. The red curve is `ζ(s) - 1`; it lies above all
twenty-six at every `s > 1`, and at `s = 1` it leaves the picture altogether (`ζ(1) = ∞`).

Everything drawn is the exact rational number `SporadicSpectrum.massQ G s`, whose relation to
the divisor sum is proved in `RequestProject/SporadicSpectrum.lean`
(`SporadicSpectrum.divisorSum_order_nat`), and the drawn window really contains the whole
table (`curves_within_window` below).

`visualization/sporadic_zeta_spectrum.csv` carries the same numbers.
-/
import RequestProject.SporadicSpectrum
import RequestProject.SporadicSvg

namespace SporadicSpectrumSvg

open Sporadic SporadicSpectrum SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

/-! ## The data of the picture -/

/-- The values of `s` at which the curves are sampled. -/
def sValues : List ℕ := [1, 2, 3, 4, 5]

/-- The plotted value of a group at `s`: its exact Dirichlet mass, as a float. -/
def massF (G : Group) (s : ℕ) : Float := (massQ G s : Float)

/-- The vertical coordinate: `log₁₀ (mass - 1)`. -/
def log10F (x : Float) : Float := Float.log x / Float.log 10.0

/-- The bottom and top of the drawn window, in `log₁₀ (value - 1)`. -/
def yLo : Float := -1.5
def yHi : Float := 0.9

/-- **The window contains all twenty-six curves.** At each sampled `s` the excess mass lies
between `1/32 = 10^(-1.505…)` and `7 = 10^(0.845…)`, the two ends of the drawn vertical axis,
so no curve is clipped. -/
theorem curves_within_window : ∀ G ∈ groups, ∀ s ∈ sValues,
    1 / 32 < massQ G s - 1 ∧ massQ G s - 1 < 7 := by
  intro G hG s hs
  have h1 : 1 ≤ s ∧ s ≤ 5 := by
    fin_cases hs <;> exact ⟨by norm_num, by norm_num⟩
  exact massQ_in_window G hG s h1.1 h1.2

/-- The rows of the picture: the twenty-six groups, heaviest first at `s = 1`. -/
def rowsSorted : List Group :=
  List.insertionSort (fun a b => massQ b 1 ≤ massQ a 1) groups

/-- The rows of the picture are exactly the twenty-six sporadic groups, reordered. -/
theorem rowsSorted_perm : rowsSorted.Perm groups :=
  List.perm_insertionSort _ _

theorem rowsSorted_length : rowsSorted.length = 26 :=
  rowsSorted_perm.length_eq.trans length_groups

/-- `ζ(s) - 1` at the sampled integers `s = 2, 3, 4, 5` (`ζ(1)` is infinite). -/
def zetaExcess : List (ℕ × Float) :=
  [(2, 0.6449340668482264), (3, 0.20205690315959429),
   (4, 0.08232323371113819), (5, 0.03692775514336993)]

/-! ## Geometry -/

private def plotLeft : Float := 210.0
private def plotRight : Float := 900.0
private def plotTop : Float := 190.0
private def plotBot : Float := 760.0

private def xOfS (s : ℕ) : Float :=
  plotLeft + (Float.ofNat s - 1.0) / 4.0 * (plotRight - plotLeft)

private def yOfV (v : Float) : Float :=
  plotBot - (v - yLo) / (yHi - yLo) * (plotBot - plotTop)

private def curveColor (G : Group) : String :=
  let t := Float.ofNat (G.exponent 2) / 46.0
  if t > 0.8 then "#b91c1c" else if t > 0.55 then "#c2410c"
  else if t > 0.35 then "#2563eb" else "#0f766e"

private def curveOpacity (G : Group) : Float :=
  0.35 + 0.65 * Float.ofNat (G.exponent 2) / 46.0

private def curvePoints (G : Group) : List (Float × Float) :=
  sValues.map fun s => (xOfS s, yOfV (log10F (massF G s - 1.0)))

private def curveSvg (G : Group) : String :=
  polylineTag (curvePoints G) (curveColor G) (1.0 + 1.6 * curveOpacity G) ++ "\n" ++
  String.intercalate "\n" ((curvePoints G).map fun q =>
    circleTag q.1 q.2 2.4 (curveColor G) "")

private def zetaPoints : List (Float × Float) :=
  zetaExcess.map fun se => (xOfS se.1, yOfV (log10F se.2))

private def yTicks : List Float := [-1.5, -1.0, -0.5, 0.0, 0.5, 0.9]

private def axisSvg : String :=
  String.intercalate "\n" (yTicks.map fun v =>
    lineTag plotLeft (yOfV v) plotRight (yOfV v) "#e5e9f0" 1.0 "" ++ "\n" ++
    textTag (plotLeft - 14.0) (yOfV v + 4.0) 12 "#6b7280" "end" "500" (fmtFixed 1 v)) ++
  "\n" ++
  String.intercalate "\n" (sValues.map fun s =>
    lineTag (xOfS s) plotTop (xOfS s) (plotBot + 8.0) "#e5e9f0" 1.0 "" ++ "\n" ++
    textTag (xOfS s) (plotBot + 30.0) 14 "#111827" "middle" "700" ("s = " ++ toString s))

/-- The extreme groups at each end, labelled on the picture. -/
private def labelled : List (String × ℕ × Float) :=
  [("M", 1, 8.0), ("B", 1, -6.0), ("Fi24'", 1, -16.0), ("M11", 1, 14.0), ("J1", 1, -4.0),
   ("J3", 5, 14.0), ("M", 5, -8.0)]

private def labelSvg (e : String × ℕ × Float) : String :=
  match groups.find? (fun G => G.name = e.1) with
  | none => ""
  | some G =>
      let s := e.2.1
      let x := xOfS s
      let y := yOfV (log10F (massF G s - 1.0))
      let anchor := if s = 1 then "end" else "start"
      let dx := if s = 1 then -10.0 else 10.0
      textTag (x + dx) (y + e.2.2) 12 (curveColor G) anchor "700" G.name

/-! ## The table panel -/

private def tableLeft : Float := 990.0
private def tableTop : Float := 190.0
private def rowH : Float := 21.5

private def colX (j : ℕ) : Float := tableLeft + 108.0 + Float.ofNat j * 78.0

private def tableHeader : String :=
  textTag tableLeft (tableTop - 14.0) 12 "#6b7280" "start" "700" "group" ++ "\n" ++
  String.intercalate "\n" (sValues.zipIdx.map fun (s, j) =>
    textTag (colX j) (tableTop - 14.0) 12 "#6b7280" "middle" "700" ("s=" ++ toString s))

private def tableRow (i : ℕ) (G : Group) : String :=
  let y := tableTop + Float.ofNat i * rowH
  textTag tableLeft y 12 "#111827" "start" "700" G.name ++ "\n" ++
  textTag (tableLeft + 56.0) y 11 "#9ca3af" "start" "500"
    ("2^" ++ toString (G.exponent 2)) ++ "\n" ++
  String.intercalate "\n" (sValues.zipIdx.map fun (s, j) =>
    textTag (colX j) y 11 (curveColor G) "middle" "500" (fmtFixed 4 (massF G s)))

private def zetaRow : String :=
  let y := tableTop + 26.0 * rowH + 6.0
  textTag tableLeft y 12 "#dc2626" "start" "700" "ζ(s)" ++ "\n" ++
  textTag (colX 0) y 11 "#dc2626" "middle" "500" "∞" ++ "\n" ++
  String.intercalate "\n" (zetaExcess.zipIdx.map fun (se, j) =>
    textTag (colX (j + 1)) y 11 "#dc2626" "middle" "500" (fmtFixed 4 (1.0 + se.2)))

/-! ## The picture -/

/-- The spectrum picture: twenty-six curves `s ↦ ∑_{d ∣ |G|} d^{-s}`, against `ζ`. -/
def sporadicSpectrumSvg : String :=
  let width : Float := 1520.0
  let height : Float := 880.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 52.0 22 "#111827" "start" "700"
    "The zeta spectrum of the twenty-six sporadic groups: the whole table as a function of s" ++
    "\n" ++
  textTag 60.0 80.0 14 "#4b5563" "start" "400"
    ("each curve is one group, plotted as log10 of the excess mass" ++
      " \u2211_{d | |G|} d^(-s) - 1 at s = 1, 2, 3, 4, 5") ++ "\n" ++
  textTag 60.0 100.0 14 "#4b5563" "start" "400"
    ("the values are exact rationals; the curves decrease and every unit step of s at least" ++
      " halves the excess, so the table collapses to 1") ++ "\n" ++
  textTag 60.0 120.0 14 "#4b5563" "start" "400"
    ("the red curve is \u03b6(s) - 1, above all twenty-six for s > 1;" ++
      " at s = 1 it is off the picture (\u03b6(1) = \u221e) while the sporadic masses stay finite:" ++
      " |M| has \u03c3(|M|)/|M| = 6.9802") ++ "\n" ++
  textTag 60.0 140.0 14 "#4b5563" "start" "400"
    ("warmer curves carry higher powers of 2; the Monster, 2^46, is the top curve at every" ++
      " sampled s, and the spread narrows from 3.32 at s = 1 to 0.00007 at s = 5") ++ "\n" ++
  axisSvg ++ "\n" ++
  textTag (plotLeft - 14.0) (plotTop - 24.0) 12 "#6b7280" "end" "700" "log10(value - 1)" ++
    "\n" ++
  String.intercalate "\n" (rowsSorted.map curveSvg) ++ "\n" ++
  polylineTag zetaPoints "#dc2626" 2.2 ++ "\n" ++
  String.intercalate "\n" (zetaPoints.map fun q => circleTag q.1 q.2 3.0 "#dc2626" "") ++
    "\n" ++
  textTag (xOfS 2 + 10.0) (yOfV (log10F 0.6449340668482264) - 10.0) 12 "#dc2626" "start" "700"
    "\u03b6(s) - 1" ++ "\n" ++
  textTag (xOfS 1) (plotTop - 10.0) 12 "#dc2626" "middle" "700" "\u03b6(1) = \u221e" ++ "\n" ++
  String.intercalate "\n" (labelled.map labelSvg) ++ "\n" ++
  tableHeader ++ "\n" ++
  String.intercalate "\n" (rowsSorted.zipIdx.map fun (G, i) => tableRow i G) ++ "\n" ++
  zetaRow ++ "\n" ++
  textTag 60.0 (plotBot + 66.0) 13 "#4b5563" "start" "500"
    ("the ranking is not the same at every s: the Monster is the largest at every s," ++
      " but the smallest group changes from M11 (s = 1, 2) to J3 (s = 3, 4), and J1 and J3" ++
      " swap between s = 1 and s = 2") ++ "\n" ++
  textTag 60.0 (plotBot + 88.0) 13 "#4b5563" "start" "500"
    ("all values are the rational numbers proved in RequestProject/SporadicSpectrum.lean;" ++
      " the drawn window contains the whole table (curves_within_window)") ++
  "\n</svg>\n"

/-! ## The same numbers as a table -/

private def csvRow (G : Group) : String :=
  G.name ++ "," ++ toString (G.exponent 2) ++ "," ++
    String.intercalate "," (sValues.map fun s => fmtFixed 9 (massF G s))

/-- The twenty-six masses at `s = 1, …, 5`. -/
def sporadicSpectrumCsv : String :=
  "name,two_exponent,mass_s1,mass_s2,mass_s3,mass_s4,mass_s5\n" ++
    String.intercalate "\n" (rowsSorted.map csvRow) ++ "\n"

end SporadicSpectrumSvg

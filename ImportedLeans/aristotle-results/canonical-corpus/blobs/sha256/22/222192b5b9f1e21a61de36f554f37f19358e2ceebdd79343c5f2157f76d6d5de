/-
# The closure picture: the table, its lcm, its ceiling, and `ζ`

`visualization/sporadic-zeta-closure.svg` expands the spectrum picture of
`RequestProject/SporadicSpectrumSvg.lean` with the two curves that close the table up:

* the **lcm** of the twenty-six sporadic orders, `N = |M| · 11 · 37 · 43 · 67`, whose Dirichlet
  mass dominates all twenty-six at every `s`;
* the **ceiling** `∏_{p ∈ sporadic primes} (1 - p^{-s})⁻¹`, the largest mass any number built
  from sporadic primes can have — with `ζ(s)` above it, unreachable, because `53` divides no
  sporadic order.

The left panel plots `log₁₀(mass - 1)` at `s = 1, …, 5`: the twenty-six groups in grey, the lcm
in blue, the ceiling in green and `ζ` in red. The right panel is the zoom at `s = 2`, where the
whole sporadic world lives in `[1.569, 1.6398]` and `ζ(2) = 1.64493…` sits above it.

Everything drawn is an exact rational number from `RequestProject/SporadicClosure.lean`; the
facts that the drawn window contains every plotted point, that the drawn vertical order is the
true one, and that the zoom axis contains everything it shows, are proved below.

`visualization/sporadic_zeta_closure.csv` carries the same numbers.
-/
import RequestProject.SporadicClosure
import RequestProject.SporadicSpectrumSvg

namespace SporadicClosureSvg

open Sporadic SporadicZeta SporadicSpectrum SporadicClosure SporadicSvg SporadicSpectrumSvg

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The data of the picture -/

/-- The lcm's mass at `s`, as a float. -/
def lcmF (s : ℕ) : Float := (lcmMassQ s : Float)

/-- The ceiling at `s`, as a float. -/
def ceilF (s : ℕ) : Float := (ceilingQ s : Float)

/-- **The drawn vertical order is the true one**: at every sampled `s`, each of the twenty-six
groups sits below the lcm, and the lcm below the ceiling. -/
theorem plot_order : ∀ G ∈ groups, ∀ s ∈ sValues,
    massQ G s ≤ lcmMassQ s ∧ lcmMassQ s ≤ ceilingQ s := by
  intro G hG s hs
  have h1 : 1 ≤ s := by fin_cases hs <;> norm_num
  exact ⟨massQ_le_lcmMassQ hG s, lcmMassQ_le_ceilingQ h1⟩

/-- **The window contains the two new curves too.** At each sampled `s` the excess masses of
the lcm and of the ceiling lie between `1/32` and `7`, the ends of the drawn vertical axis
(`curves_within_window` says the same for the twenty-six groups). -/
theorem new_curves_within_window : ∀ s ∈ sValues,
    (1 / 32 < lcmMassQ s - 1 ∧ lcmMassQ s - 1 < 7) ∧
      (1 / 32 < ceilingQ s - 1 ∧ ceilingQ s - 1 < 7) := by
  intro s hs
  fin_cases hs <;>
    refine ⟨⟨by norm_num [lcmMassQ, lcmFactors, Finset.sum_range_succ], by
      norm_num [lcmMassQ, lcmFactors, Finset.sum_range_succ]⟩,
      ⟨by norm_num [ceilingQ, lcmFactors], by norm_num [ceilingQ, lcmFactors]⟩⟩

/-- `ζ(2) = π²/6 < 1.645`. -/
theorem zetaR_two_lt : zetaR 2 < 1645 / 1000 := by
  rw [zetaR_two]
  nlinarith [Real.pi_lt_d6, Real.pi_pos]

/-- **The zoom axis of the right-hand panel contains everything it shows**: the twenty-six
masses at `s = 2`, the lcm, the ceiling and `ζ(2)` all lie in `[1.56, 1.65]`. -/
theorem zoom_axis_contains :
    (∀ G ∈ groups, 156 / 100 < massQ G 2 ∧ massQ G 2 < 165 / 100) ∧
      (156 / 100 < lcmMassQ 2 ∧ lcmMassQ 2 < 165 / 100) ∧
      (156 / 100 < ceilingQ 2 ∧ ceilingQ 2 < 165 / 100) ∧
      ((156 : ℝ) / 100 < zetaR 2 ∧ zetaR 2 < 165 / 100) := by
  refine ⟨fun G hG => ?_, ?_, ?_, ?_⟩
  · have h := zetaMassQ_mem_band G hG
    rw [massQ_two]
    constructor <;> [linarith [h.1]; linarith [h.2]]
  · have h := lcmMassQ_two_band
    constructor <;> [linarith [h.1]; linarith [h.2]]
  · have h := ceilingQ_two_band
    constructor <;> [linarith [h.1]; linarith [h.2]]
  · exact ⟨by linarith [zetaR_two_gt], by linarith [zetaR_two_lt]⟩

/-! ## Geometry of the left panel -/

private def plotLeft : Float := 210.0
private def plotRight : Float := 830.0
private def plotTop : Float := 210.0
private def plotBot : Float := 760.0

private def xOfSF (s : Float) : Float :=
  plotLeft + (s - 1.0) / 4.0 * (plotRight - plotLeft)

private def xOfS (s : ℕ) : Float := xOfSF (Float.ofNat s)

private def yOfV (v : Float) : Float :=
  plotBot - (v - yLo) / (yHi - yLo) * (plotBot - plotTop)

private def yOfMass (m : Float) : Float := yOfV (log10F (m - 1.0))

private def groupPoints (G : Group) : List (Float × Float) :=
  sValues.map fun s => (xOfS s, yOfMass (massF G s))

private def lcmPoints : List (Float × Float) :=
  sValues.map fun s => (xOfS s, yOfMass (lcmF s))

private def ceilPoints : List (Float × Float) :=
  sValues.map fun s => (xOfS s, yOfMass (ceilF s))

private def zetaPoints : List (Float × Float) :=
  zetaExcess.map fun se => (xOfS se.1, yOfV (log10F se.2))

private def yTicks : List Float := [-1.5, -1.0, -0.5, 0.0, 0.5, 0.9]

private def axisSvg : String :=
  String.intercalate "\n" (yTicks.map fun v =>
    lineTag plotLeft (yOfV v) plotRight (yOfV v) "#eef1f6" 1.0 "" ++ "\n" ++
    textTag (plotLeft - 14.0) (yOfV v + 4.0) 12 "#6b7280" "end" "500" (fmtFixed 1 v)) ++
  "\n" ++
  String.intercalate "\n" (sValues.map fun s =>
    lineTag (xOfS s) plotTop (xOfS s) (plotBot + 8.0) "#eef1f6" 1.0 "" ++ "\n" ++
    textTag (xOfS s) (plotBot + 30.0) 14 "#111827" "middle" "700" ("s = " ++ toString s))

/-- The two located crossing intervals, marked under the curves: `J1` overtakes `J3` somewhere
in `(1, 3/2)` and `M11` overtakes `J3` somewhere in `(2, 5/2)`. -/
private def crossingsSvg : String :=
  let bar (a b : Float) (label : String) (dy : Float) : String :=
    rectTag (xOfSF a) (plotBot + 44.0 + dy) (xOfSF b - xOfSF a) 9.0 "#7c3aed" "" 0.25 ++ "\n" ++
    lineTag (xOfSF a) (plotBot + 44.0 + dy) (xOfSF a) (plotBot + 53.0 + dy) "#7c3aed" 1.4 "" ++
      "\n" ++
    lineTag (xOfSF b) (plotBot + 44.0 + dy) (xOfSF b) (plotBot + 53.0 + dy) "#7c3aed" 1.4 "" ++
      "\n" ++
    textTag (xOfSF b + 10.0) (plotBot + 53.0 + dy) 12 "#7c3aed" "start" "700" label
  bar 1.0 1.5 "J1 overtakes J3 here" 0.0 ++ "\n" ++
  bar 2.0 2.5 "M11 overtakes J3 here" 20.0

private def groupCurvesSvg : String :=
  String.intercalate "\n" (groups.map fun G =>
    polylineTag (groupPoints G) "#c7cdd8" 1.2)

private def leftPanelSvg : String :=
  axisSvg ++ "\n" ++
  textTag (plotLeft - 14.0) (plotTop - 24.0) 12 "#6b7280" "end" "700" "log10(value - 1)" ++
    "\n" ++
  groupCurvesSvg ++ "\n" ++
  polylineTag ceilPoints "#15803d" 3.4 ++ "\n" ++
  polylineTag lcmPoints "#1d4ed8" 2.0 ++ "\n" ++
  polylineTag zetaPoints "#dc2626" 2.4 ++ "\n" ++
  String.intercalate "\n" (lcmPoints.map fun q => circleTag q.1 q.2 2.6 "#1d4ed8" "") ++ "\n" ++
  String.intercalate "\n" (zetaPoints.map fun q => circleTag q.1 q.2 2.8 "#dc2626" "") ++ "\n" ++
  textTag (xOfS 3) (yOfMass (ceilF 3) - 30.0) 13 "#15803d" "middle" "700"
    "ceiling: 18 untruncated Euler factors" ++ "\n" ++
  textTag (xOfS 3) (yOfMass (lcmF 3) + 34.0) 13 "#1d4ed8" "middle" "700"
    "lcm of all 26 orders" ++ "\n" ++
  textTag (xOfS 4 + 8.0) (yOfV (log10F 0.08232323371113819) - 12.0) 13 "#dc2626" "start" "700"
    "\u03b6(s) - 1" ++ "\n" ++
  textTag (xOfS 2) (plotTop - 4.0) 12 "#6b7280" "middle" "500"
    "26 grey curves: the sporadic groups" ++ "\n" ++
  textTag (xOfS 1 + 6.0) (plotTop - 44.0) 12 "#dc2626" "start" "700" "\u03b6(1) = \u221e" ++
    "\n" ++ crossingsSvg

/-! ## Geometry of the right panel: the zoom at `s = 2` -/

private def zoomLo : Float := 1.56
private def zoomHi : Float := 1.65
private def zoomLeft : Float := 1020.0
private def zoomRight : Float := 1300.0
private def zoomTop : Float := 230.0
private def zoomBot : Float := 760.0

private def yOfZoom (m : Float) : Float :=
  zoomBot - (m - zoomLo) / (zoomHi - zoomLo) * (zoomBot - zoomTop)

private def zoomTicks : List Float := [1.56, 1.58, 1.60, 1.62, 1.64]

private def zoomAxisSvg : String :=
  lineTag zoomLeft zoomTop zoomLeft zoomBot "#9ca3af" 1.2 "" ++ "\n" ++
  String.intercalate "\n" (zoomTicks.map fun v =>
    lineTag (zoomLeft - 6.0) (yOfZoom v) zoomRight (yOfZoom v) "#eef1f6" 1.0 "" ++ "\n" ++
    textTag (zoomLeft - 12.0) (yOfZoom v + 4.0) 12 "#6b7280" "end" "500" (fmtFixed 2 v))

private def groupTicksSvg : String :=
  String.intercalate "\n" (groups.map fun G =>
    lineTag zoomLeft (yOfZoom (massF G 2)) (zoomLeft + 34.0) (yOfZoom (massF G 2))
      "#9ca3af" 1.4 "")

/-- One level of the zoom panel: a horizontal line at the value `m`, and a two-line label
parked at the fixed height `labelY` in the right margin, joined to the line by a leader. -/
private def levelSvg (m : Float) (color label value : String) (labelY : Float) : String :=
  lineTag zoomLeft (yOfZoom m) zoomRight (yOfZoom m) color 2.2 "" ++ "\n" ++
  lineTag zoomRight (yOfZoom m) (zoomRight + 26.0) (labelY - 4.0) color 1.0 "3 3" ++ "\n" ++
  textTag (zoomRight + 32.0) labelY 12 color "start" "700" label ++ "\n" ++
  textTag (zoomRight + 32.0) (labelY + 15.0) 11 color "start" "500" value

private def zoomPanelSvg : String :=
  zoomAxisSvg ++ "\n" ++
  groupTicksSvg ++ "\n" ++
  textTag zoomLeft (zoomTop - 34.0) 14 "#111827" "start" "700" "the zoom at s = 2" ++ "\n" ++
  textTag zoomLeft (zoomTop - 14.0) 12 "#6b7280" "start" "500"
    "26 ticks: the sporadic masses \u2211_{d | |G|} d^(-2)" ++ "\n" ++
  levelSvg 1.6449340668482264 "#dc2626" "\u03b6(2) = \u03c0\u00b2/6" "1.644934" 246.0 ++ "\n" ++
  levelSvg (ceilF 2) "#15803d" "sporadic ceiling" (fmtFixed 6 (ceilF 2)) 292.0 ++ "\n" ++
  levelSvg (lcmF 2) "#1d4ed8" "lcm of the 26" (fmtFixed 6 (lcmF 2)) 338.0 ++ "\n" ++
  levelSvg (massF monster 2) "#b91c1c" "Monster" (fmtFixed 6 (massF monster 2)) 384.0 ++
    "\n" ++
  lineTag (zoomLeft + 60.0) (yOfZoom (ceilF 2)) (zoomLeft + 60.0)
    (yOfZoom 1.6449340668482264) "#dc2626" 1.2 "4 3" ++ "\n" ++
  textTag (zoomLeft + 68.0) ((yOfZoom (ceilF 2) + yOfZoom 1.6449340668482264) / 2.0 + 4.0) 12
    "#dc2626" "start" "700" "gap 0.0052" ++ "\n" ++
  textTag zoomLeft (zoomBot + 30.0) 12 "#111827" "start" "500"
    "lowest tick M11 1.569201, highest Monster 1.637236" ++ "\n" ++
  textTag zoomLeft (zoomBot + 50.0) 12 "#111827" "start" "500"
    "the gap: 53, 61, 73, \u2026 divide no sporadic order"

/-! ## The picture -/

/-- The closure picture: the twenty-six curves, their lcm, the sporadic ceiling, and `ζ`. -/
def sporadicClosureSvg : String :=
  let width : Float := 1520.0
  let height : Float := 920.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 52.0 22 "#111827" "start" "700"
    "Closing the table: the twenty-six sporadic groups, their lcm, their ceiling, and zeta" ++
    "\n" ++
  textTag 60.0 80.0 14 "#4b5563" "start" "400"
    ("the lcm of all twenty-six orders is |M| \u00b7 11 \u00b7 37 \u00b7 43 \u00b7 67 = 2^46 \u00b7 3^20 \u00b7 5^9 \u00b7 7^6" ++
      " \u00b7 11^3 \u00b7 13^3 \u00b7 17 \u00b7 19 \u00b7 23 \u00b7 29 \u00b7 31 \u00b7 37 \u00b7 41 \u00b7 43 \u00b7 47 \u00b7 59 \u00b7 67 \u00b7 71") ++ "\n" ++
  textTag 60.0 100.0 14 "#4b5563" "start" "400"
    ("its Dirichlet mass dominates every group at every s; above it the ceiling, the eighteen" ++
      " untruncated Euler factors, caps every number built from sporadic primes") ++ "\n" ++
  textTag 60.0 120.0 14 "#4b5563" "start" "400"
    ("the ceiling stays strictly below \u03b6: the prime 53 divides no sporadic order, and at" ++
      " s = 2 the sporadic world stops 0.0052 short of \u03b6(2) = 1.644934") ++ "\n" ++
  textTag 60.0 140.0 14 "#4b5563" "start" "400"
    ("at s = 2 the lcm is within 0.000045 of the ceiling: the twenty-six orders already" ++
      " exhaust nearly all the mass their primes can carry") ++ "\n" ++
  leftPanelSvg ++ "\n" ++
  zoomPanelSvg ++ "\n" ++
  textTag 60.0 (plotBot + 106.0) 13 "#4b5563" "start" "500"
    ("all values are exact rationals from RequestProject/SporadicClosure.lean; the drawn" ++
      " order group \u2264 lcm \u2264 ceiling is proved (plot_order), as is the fit of both panels") ++
    "\n" ++
  textTag 60.0 (plotBot + 128.0) 13 "#4b5563" "start" "500"
    ("the curves are continuous in s, so where two of them swap rank they really meet: the" ++
      " purple bars are the located crossings, J1/J3 inside (1, 1.5) and M11/J3 inside (2, 2.5)") ++
  "\n</svg>\n"

/-! ## The same numbers as a table -/

private def csvRow (s : ℕ) : String :=
  toString s ++ "," ++ fmtFixed 9 (massF mathieu11 s) ++ "," ++ fmtFixed 9 (massF monster s) ++
    "," ++ fmtFixed 9 (lcmF s) ++ "," ++ fmtFixed 9 (ceilF s)

/-- The extremes of the table, the lcm and the ceiling at `s = 1, …, 5`. -/
def sporadicClosureCsv : String :=
  "s,mass_M11,mass_Monster,mass_lcm,sporadic_ceiling\n" ++
    String.intercalate "\n" (sValues.map csvRow) ++ "\n"

end SporadicClosureSvg

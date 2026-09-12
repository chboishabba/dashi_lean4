/-
# The widened diagram: fifty primes

Two pictures drawn from the verified material of `RequestProject/ExtendedPrimes.lean`:

* `visualization/fibers-first-50-primes.svg` — the integers `1, …, 1024` on a 32 × 32 grid,
  each cell coloured by the prime `p` with `n = p^k` (`k ≥ 1`) for the **first fifty primes**
  `2, …, 229`; the twenty old colours are kept, so this picture strictly extends
  `visualization/fibers-first-20-primes.svg`. `PrimeFibers.card_first50Fibers_1024` proves
  that exactly `76` of the `1024` cells are coloured (against `46` for twenty primes), and
  `PrimeFibers.extCellColor_ne_neutral_iff_mem_first50Fibers` proves that the coloured cells
  are exactly the union of the fifty fibers.
* `visualization/zeta-euler-50-primes.svg` — the fifty Euler factors of `ζ` at `s = 2`, on a
  logarithmic axis (the excess `(1-p^{-2})⁻¹ - 1 = 1/(p²-1)` of each factor over `1`), with
  the fifteen primes of the Monster ringed, and below it the cumulative product
  `∏_{p ≤ P} (1-p^{-2})⁻¹` climbing towards `ζ(2) = π²/6`; the chain
  `∑_{d ∣ |M|} d^{-s} ≤ ∏_{p ∣ |M|} ≤ ∏_{p ≤ 229} ≤ ζ(s)` is proved in
  `Sporadic.monsterDivisorSum_le_extendedEulerProduct` and
  `Sporadic.extendedEulerProduct_le_zeta`.

Only floating-point coordinates and string manipulation live here.
-/
import RequestProject.ExtendedPrimes
import RequestProject.SporadicSvg

namespace ExtendedSvg

open PrimeFibers Sporadic SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## Picture 1: the 32 × 32 grid of the fifty fibers -/

/-- The numbers displayed in the wider grid. -/
def displayN : ℕ := 1024

/-- Columns of the grid. -/
def gridCols : ℕ := 32

private def cellW : Float := 27.0
private def marginX : Float := 30.0
private def gridTop : Float := 118.0

/-- Palette colours light enough to carry dark text. -/
def lightColors : List String :=
  ["#bfef45", "#fabed4", "#dcbeff", "#ffd8b1", "#aaffc3", "#ffe119", "#a9a9a9", "#42d4f4",
   "#00bfa0", "#cedb9c", "#e7cb94", "#9c9ede", "#b5cf6b", "#e7ba52", "#e7969c", "#de9ed6",
   "#bcbd22", "#17becf", "#f58231", "#3cb44b", "#2ca02c", "#8ca252", "#e377c2"]

/-- The colour of the numeral drawn inside a cell of the given background colour. -/
def extLabelColor (background : String) : String :=
  if background ∈ lightColors then "#1f2933" else "#ffffff"

/-- One cell of the wider grid. -/
private def cellSvg (n : ℕ) : String :=
  let i := n - 1
  let x := marginX + Float.ofNat (i % gridCols) * cellW
  let y := gridTop + Float.ofNat (i / gridCols) * cellW
  let c := extCellColor n
  let stroke := if c = neutralColor then "#e5e9f0" else "#ffffff"
  rectTag x y (cellW - 1.0) (cellW - 1.0) c stroke 1.0 ++
    (if c = neutralColor then ""
     else "\n" ++ textTag (x + cellW / 2.0 - 0.5) (y + cellW / 2.0 + 3.0) 9
            (extLabelColor c) "middle" "700" (toString n))

private def gridSvg : String :=
  String.intercalate "\n" ((List.range displayN).map (fun i => cellSvg (i + 1)))

private def legendEntry (x y : Float) (color label : String) : String :=
  rectTag x y 14.0 14.0 color "#ffffff" 1.0 ++ "\n" ++
    textTag (x + 20.0) (y + 11.5) 11 "#1f2933" "start" "500" label

private def legendSvg (y0 : Float) : String :=
  let entries :=
    extPrimeList.map (fun p => (extFiberColor p, toString p ++ "^k")) ++
      [(neutralColor, "other")]
  String.intercalate "\n"
    (entries.zipIdx.map (fun (e, i) =>
      legendEntry (marginX + Float.ofNat (i % 10) * 86.0)
        (y0 + Float.ofNat (i / 10) * 22.0) e.1 e.2))

private def svgWidth : Float := marginX * 2.0 + Float.ofNat gridCols * cellW

private def gridBottom : Float :=
  gridTop + Float.ofNat ((displayN + gridCols - 1) / gridCols) * cellW

private def docHeader (width height : Float) (title subtitle : String) : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++
    attr "width" (fmt width) ++ " " ++ attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag marginX 44.0 22 "#111827" "start" "700" title ++ "\n" ++
  textTag marginX 70.0 13 "#4b5563" "start" "400" subtitle

/-- The grid of `1, …, 1024` coloured by the fifty prime-power fibers. -/
def fiftyPrimeGridSvg : String :=
  let height := gridBottom + 160.0
  docHeader svgWidth height
      "Prime-power fibers of the first fifty primes"
      ("cell n is coloured by the prime p with n = p^k (k \u2265 1), for p \u2264 229;" ++
        " 76 of the 1024 cells are coloured (46 of them for p \u2264 71)") ++ "\n" ++
    textTag marginX 92.0 13 "#4b5563" "start" "400"
      ("fiber sizes: 2 \u21a6 10, 3 \u21a6 6, 5 \u21a6 4, 7 \u21a6 3, then 2 for 11 \u2264 p \u2264 31" ++
        " and 1 for 37 \u2264 p \u2264 229") ++ "\n" ++
    gridSvg ++ "\n" ++ legendSvg (gridBottom + 24.0) ++ "\n</svg>\n"

/-! ## Picture 2: the fifty Euler factors of zeta at `s = 2` -/

/-- The Euler factor `(1 - p^{-2})⁻¹` as a floating-point number. -/
def eulerF (p : ℕ) : Float :=
  let x := Float.ofNat p
  x * x / (x * x - 1.0)

/-- The excess of the Euler factor over `1`, namely `1/(p² - 1)`. -/
def eulerExcess (p : ℕ) : Float :=
  let x := Float.ofNat p
  1.0 / (x * x - 1.0)

/-- The cumulative products `1, f₂, f₂f₃, …` of the fifty Euler factors. -/
def cumProducts : List Float :=
  List.scanl (fun a p => a * eulerF p) 1.0 extPrimeList

/-- The full fifty-factor Euler product at `s = 2`, as a Float. -/
def extProduct : Float := (cumProducts.getLast? ).getD 1.0

/-- The Monster's fifteen-factor Euler product at `s = 2`, as a Float. -/
def monsterProduct : Float :=
  ([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71] : List ℕ).foldl
    (fun a p => a * eulerF p) 1.0

/-- `ζ(2) = π²/6`. -/
def zetaTwo : Float := 1.6449340668482264

private def panelLeft : Float := 96.0
private def panelRight : Float := 1010.0
private def topPanelTop : Float := 132.0
private def topPanelBot : Float := 400.0
private def botPanelTop : Float := 486.0
private def botPanelBot : Float := 700.0

/-- Horizontal position of the `i`-th prime (`i = 0, …, 49`). -/
private def xOf (i : ℕ) : Float :=
  panelLeft + (Float.ofNat i + 0.5) * (panelRight - panelLeft) / 50.0

/-- Vertical position in the top panel: `log₁₀` of the excess, from `10⁰` down to `10⁻⁵`. -/
private def yLog (v : Float) : Float :=
  let l := Float.log10 v
  topPanelBot + (l + 5.0) / 5.0 * (topPanelTop - topPanelBot)

/-- Vertical position in the bottom panel: the cumulative product, from `1.0` to `1.66`. -/
private def yCum (v : Float) : Float :=
  botPanelBot - (v - 1.0) / 0.66 * (botPanelBot - botPanelTop)

private def monsterPrimeList : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

private def topPanel : String :=
  let axes :=
    String.intercalate "\n"
      ((List.range 6).map (fun j =>
        let y := topPanelBot + Float.ofNat j / 5.0 * (topPanelTop - topPanelBot)
        lineTag panelLeft y panelRight y "#e5e9f0" 1.0 "" ++ "\n" ++
          textTag (panelLeft - 10.0) (y + 4.0) 11 "#6b7280" "end"
            "400" ("10^" ++ toString (j - 5 : Int))))
  let bars :=
    String.intercalate "\n"
      (extPrimeList.zipIdx.map (fun (p, i) =>
        let x := xOf i
        let v := eulerExcess p
        let y := yLog v
        let col := extFiberColor p
        let ring := if p ∈ monsterPrimeList then circleTag x y 6.5 "none" "#111827" else ""
        lineTag x topPanelBot x y col 3.0 "" ++ "\n" ++
          circleTag x y 3.6 col "#ffffff" ++
          (if ring = "" then "" else "\n" ++ ring) ++ "\n" ++
          textTag x (topPanelBot + 16.0) 9 "#374151" "middle"
            (if p ∈ monsterPrimeList then "700" else "400") (toString p)))
  axes ++ "\n" ++ bars ++ "\n" ++
    lineTag panelLeft topPanelBot panelRight topPanelBot "#9ca3af" 1.2 "" ++ "\n" ++
    textTag panelLeft (topPanelTop - 14.0) 13 "#111827" "start" "600"
      "excess of the Euler factor over 1 at s = 2:  (1 - p^-2)^-1 - 1 = 1/(p\u00b2-1)" ++ "\n" ++
    textTag panelRight (topPanelTop - 14.0) 11 "#111827" "end" "500"
      "ringed = one of the Monster's fifteen primes"

private def botPanel : String :=
  let pts :=
    (cumProducts.zipIdx.map (fun (c, i) =>
      (if i = 0 then panelLeft else xOf (i - 1), yCum c)))
  let dots :=
    String.intercalate "\n"
      (extPrimeList.zipIdx.map (fun (p, i) =>
        let c := (cumProducts.getD (i + 1) 1.0)
        circleTag (xOf i) (yCum c) 3.2 (extFiberColor p) "#ffffff"))
  let zetaLine :=
    lineTag panelLeft (yCum zetaTwo) panelRight (yCum zetaTwo) "#111827" 1.4 "5 4" ++ "\n" ++
      textTag (panelLeft + 6.0) (yCum zetaTwo - 7.0) 12 "#111827" "start" "700"
        ("\u03b6(2) = \u03c0\u00b2/6 = " ++ fmtFixed 6 zetaTwo)
  let monsterLine :=
    lineTag panelLeft (yCum monsterProduct) panelRight (yCum monsterProduct)
        "#7a1030" 1.2 "3 4" ++ "\n" ++
      textTag (panelLeft + 6.0) (yCum monsterProduct + 14.0) 12 "#7a1030" "start" "600"
        ("Monster's fifteen factors: " ++ fmtFixed 6 monsterProduct)
  let grid :=
    String.intercalate "\n"
      ((List.range 7).map (fun j =>
        let v := 1.0 + Float.ofNat j * 0.11
        let y := yCum v
        lineTag panelLeft y panelRight y "#eef1f6" 1.0 "" ++ "\n" ++
          textTag (panelLeft - 10.0) (y + 4.0) 11 "#6b7280" "end" "400" (fmtFixed 2 v)))
  grid ++ "\n" ++ zetaLine ++ "\n" ++ monsterLine ++ "\n" ++
    polylineTag pts "#1f3d99" 2.0 ++ "\n" ++ dots ++ "\n" ++
    lineTag panelLeft botPanelBot panelRight botPanelBot "#9ca3af" 1.2 "" ++ "\n" ++
    textTag panelLeft (botPanelTop - 14.0) 13 "#111827" "start" "600"
      "cumulative Euler product at s = 2:  \u220f_{p \u2264 P} (1 - p^-2)^-1, P running over the fifty primes" ++
    "\n" ++
    textTag panelRight (yCum extProduct - 10.0) 12 "#1f3d99" "end" "700"
      ("fifty factors: " ++ fmtFixed 6 extProduct)

/-- The two-panel picture of the fifty Euler factors of `ζ` at `s = 2`. -/
def zetaEulerFiftySvg : String :=
  docHeader 1060.0 740.0
      "Fifty Euler factors of \u03b6 at s = 2, and the Monster inside them"
      ("each prime p \u2264 229 contributes the factor (1 - p^-2)^-1;" ++
        " the product of all fifty is below \u03b6(2), and the Monster's fifteen are a sub-product") ++
    "\n" ++ textTag marginX 94.0 12 "#4b5563" "start" "400"
      ("proved: \u2211_{d | |M|} d^-s \u2264 \u220f_{p | |M|} (1-p^-s)^-1 \u2264 \u220f_{p \u2264 229} (1-p^-s)^-1 \u2264 \u03b6(s)" ++
        "  for every real s > 1") ++ "\n" ++
    topPanel ++ "\n" ++ botPanel ++ "\n</svg>\n"

/-! ## The table -/

/-- A CSV table of the fifty primes: fiber size in `1, …, 1024`, colour, Euler factor at
`s = 2`, running product, and whether the prime divides `|M|`. -/
def extendedPrimesCsv : String :=
  let header := "index,prime,fiber_size_1024,color,euler_factor_s2,cumulative_product,divides_monster"
  let rows :=
    extPrimeList.zipIdx.map (fun (p, i) =>
      String.intercalate ","
        [toString (i + 1), toString p, toString (Nat.log p 1024), extFiberColor p,
         fmtFixed 8 (eulerF p), fmtFixed 8 (cumProducts.getD (i + 1) 1.0),
         if p ∈ monsterPrimeList then "yes" else "no"])
  String.intercalate "\n" (header :: rows) ++ "\n"

end ExtendedSvg

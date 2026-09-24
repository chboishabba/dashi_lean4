/-
# The expanded diagram: all twenty-six sporadic groups measured against `ζ(2)`

`visualization/sporadic-zeta-ladder.svg` places the twenty-six sporadic simple groups on one
axis: the horizontal position of a group is the exact value of its Dirichlet mass

```
∑_{d ∣ |G|} d⁻²  =  ∏_{p^e ‖ |G|} (1 + p⁻² + ⋯ + p^{-2e}),
```

the truncated Euler product of `ζ` cut off at the exponents of that group's order. Three
vertical lines mark the ceilings: the Monster's value, the product of the *untruncated*
Euler factors at its fifteen supersingular primes, and `ζ(2) = π²/6`.

Everything drawn is the rational number `SporadicZeta.zetaMassQ`, whose relation to the
divisor sum is proved in `RequestProject/SporadicZeta.lean`
(`SporadicZeta.divisorSum_order_two`), and the axis really does contain the whole table
(`bars_within_axis` below).

`visualization/sporadic_zeta_masses.csv` carries the same numbers exactly, as fractions.
-/
import RequestProject.SporadicZeta
import RequestProject.SporadicSvg

namespace SporadicZetaSvg

open Sporadic SporadicZeta SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The data of the picture -/

/-- The value drawn for a group: its zeta mass `∑_{d ∣ |G|} d⁻²` as a floating-point number. -/
def massF (G : Group) : Float := (zetaMassQ G : Float)

/-- The rows of the picture: the twenty-six groups, in increasing order of zeta mass. -/
def rowsSorted : List Group :=
  List.insertionSort (fun a b => zetaMassQ a ≤ zetaMassQ b) groups

/-- The rows of the picture are exactly the twenty-six sporadic groups, reordered. -/
theorem rowsSorted_perm : rowsSorted.Perm groups :=
  List.perm_insertionSort _ _

theorem rowsSorted_length : rowsSorted.length = 26 :=
  rowsSorted_perm.length_eq.trans length_groups

/-- Left and right ends of the value axis. -/
def axisLo : Float := 1.55
def axisHi : Float := 1.65

/-- **The axis contains the whole table.** Every sporadic zeta mass lies strictly between the
two ends `1.55` and `1.65` of the drawn axis, so no bar is clipped. -/
theorem bars_within_axis : ∀ G ∈ groups,
    (155 : ℚ) / 100 < zetaMassQ G ∧ zetaMassQ G < (165 : ℚ) / 100 := by
  intro G hG
  obtain ⟨h1, h2⟩ := zetaMassQ_mem_band G hG
  constructor <;> linarith

/-- The untruncated Euler factor `(1 - p⁻²)⁻¹`, as a floating-point number. -/
def eulerF (p : ℕ) : Float :=
  let x := 1.0 / (Float.ofNat p * Float.ofNat p)
  1.0 / (1.0 - x)

/-- The product of the fifteen untruncated Euler factors at the Monster's primes: the ceiling
that the Monster's truncated product approaches from below. -/
def monsterEulerF : Float := (monsterPrimeList.map eulerF).foldl (· * ·) 1.0

/-- `ζ(2) = π²/6`. -/
def zetaTwoF : Float := 1.6449340668482264

/-- The exponent of `2` in the order of `G` (the group's rung on the ladder of 46). -/
def twoExp (G : Group) : ℕ := G.exponent 2

/-- How many primes divide `|G|`. -/
def primeCount (G : Group) : ℕ := G.factors.length

/-! ## Geometry -/

private def plotLeft : Float := 300.0
private def plotRight : Float := 1220.0
private def rowTop : Float := 236.0
private def rowH : Float := 33.0

private def xOf (v : Float) : Float :=
  plotLeft + (v - axisLo) / (axisHi - axisLo) * (plotRight - plotLeft)

private def yOf (i : ℕ) : Float := rowTop + Float.ofNat i * rowH

/-- The colour of a bar: warmer the higher the power of `2` in the order. -/
private def barOpacity (G : Group) : Float :=
  0.22 + 0.78 * Float.ofNat (twoExp G) / 46.0

private def tickValues : List Float := [1.55, 1.57, 1.59, 1.61, 1.63, 1.65]

private def gridLines : String :=
  String.intercalate "\n" (tickValues.map fun v =>
    lineTag (xOf v) (rowTop - 26.0) (xOf v) (yOf 26 + 6.0) "#e5e9f0" 1.0 "" ++ "\n" ++
    textTag (xOf v) (rowTop - 34.0) 12 "#6b7280" "middle" "500" (fmtFixed 2 v))

private def barRow (i : ℕ) (G : Group) : String :=
  let y := yOf i
  let v := massF G
  textTag (plotLeft - 176.0) (y + 21.0) 14 "#111827" "start" "700" G.name ++ "\n" ++
  textTag (plotLeft - 92.0) (y + 21.0) 12 "#6b7280" "start" "500"
    ("2^" ++ toString (twoExp G) ++ ", " ++ toString (primeCount G) ++ "p") ++ "\n" ++
  rectTag plotLeft (y + 5.0) (xOf v - plotLeft) (rowH - 12.0) "#2563eb" "#1e3a8a"
    (barOpacity G) ++ "\n" ++
  textTag (xOf v + 10.0) (y + 21.0) 12 "#111827" "start" "600" (fmtFixed 6 v) ++ "\n" ++
  textTag (plotRight + 130.0) (y + 21.0) 12 "#9333ea" "start" "500"
    (fmtFixed 6 (zetaTwoF - v))

private def markerLine (v : Float) (colour dash label : String) (dy : Float) : String :=
  lineTag (xOf v) (rowTop - 20.0) (xOf v) (yOf 26 + 10.0) colour 1.8 dash ++ "\n" ++
  textTag (xOf v) (yOf 26 + 10.0 + dy) 13 colour "middle" "700" label

/-- The ladder picture: the twenty-six sporadic groups by zeta mass, against `ζ(2)`. -/
def sporadicZetaLadderSvg : String :=
  let width : Float := plotRight + 260.0
  let height : Float := yOf 26 + 130.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 56.0 22 "#111827" "start" "700"
    "The twenty-six sporadic groups as truncated Euler products of the zeta function" ++ "\n" ++
  textTag 60.0 82.0 14 "#4b5563" "start" "400"
    ("each bar is the exact value of the divisor sum \u2211_{d | |G|} d^(-2)" ++
      " = \u220f_{p^e || |G|} (1 + p^(-2) + ... + p^(-2e)),") ++ "\n" ++
  textTag 60.0 102.0 14 "#4b5563" "start" "400"
    ("the Euler product of \u03b6 truncated at the exponents of |G|;" ++
      " rows are ordered by that value, the label gives the power of 2 and the" ++
      " number of primes") ++ "\n" ++
  textTag 60.0 122.0 14 "#4b5563" "start" "400"
    ("all twenty-six lie inside \u03b6(2) = \u03c0\u00b2/6 = 1.644934; the Monster is the largest," ++
      " at 1.637236, and still 0.007698 short (the purple column is the distance to" ++
      " \u03b6(2))") ++ "\n" ++
  textTag (plotRight + 130.0) (rowTop - 34.0) 12 "#9333ea" "start" "600" "\u03b6(2) - value" ++
    "\n" ++
  gridLines ++ "\n" ++
  String.intercalate "\n" (rowsSorted.zipIdx.map fun (G, i) => barRow i G) ++ "\n" ++
  markerLine monsterEulerF "#0f766e" "6 4"
    ("15 full Euler factors = " ++ fmtFixed 6 monsterEulerF) 26.0 ++ "\n" ++
  markerLine zetaTwoF "#dc2626" "" ("\u03b6(2) = " ++ fmtFixed 6 zetaTwoF) 48.0 ++ "\n" ++
  textTag 60.0 (yOf 26 + 92.0) 13 "#4b5563" "start" "500"
    ("the two losses have very different sizes: truncating the fifteen Euler factors at" ++
      " the Monster's own exponents costs only 0.000045, so the teal line all but touches" ++
      " the Monster's bar, while the primes |M| does not have (37 first) cost 0.007653") ++
  "\n</svg>\n"

/-! ## The same numbers as a table -/

private def csvRow (G : Group) : String :=
  let q := zetaMassQ G
  G.name ++ "," ++ factorString G ++ "," ++ toString (twoExp G) ++ "," ++
    toString (primeCount G) ++ "," ++ toString q.num ++ "," ++ toString q.den ++ "," ++
    fmtFixed 9 (massF G) ++ "," ++ fmtFixed 9 (zetaTwoF - massF G)

/-- The twenty-six zeta masses, exactly (as fractions) and numerically. -/
def sporadicZetaCsv : String :=
  "name,factorization,two_exponent,prime_count,mass_num,mass_den,mass,defect_to_zeta2\n" ++
    String.intercalate "\n" (rowsSorted.map csvRow) ++ "\n"

end SporadicZetaSvg

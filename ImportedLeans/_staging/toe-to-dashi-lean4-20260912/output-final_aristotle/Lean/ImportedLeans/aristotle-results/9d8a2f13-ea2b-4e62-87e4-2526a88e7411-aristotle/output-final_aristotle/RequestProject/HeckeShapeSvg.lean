/-
# Pictures of the twenty-six shapes in Hecke space

Two pictures and a table, drawn from the verified data of `RequestProject/HeckeShapeTable.lean`:

* `visualization/hecke-shape-efficiency.svg` — for each sporadic group, the visible Hecke mass of
  its shape (coloured by prime) against the number of Hecke coordinates it pays for, ranked by
  shape efficiency: the small groups are at the top, the Monster at the bottom
  (`shapeEfficiency_monster_min`), with a scatter of mass against dimension underneath;
* `visualization/monster-shape-primes.svg` — the Monster's own shape broken up prime by prime:
  the six small primes against the nine large ones, which contribute a single point each
  (`exponent_one_of_large`) and less than a third of the small primes' mass
  (`monster_large_lt_third_small`);
* `visualization/hecke_shapes.csv` — name, order digits, dimension, visible points, visible mass,
  shape efficiency, small/large split.

Only floating-point coordinates and string manipulation live here; every number drawn is the
`Float` image of the rational reference value `HeckeShapes.refAbs`, which
`HeckeShapes.visMass_close` proves to be within `10⁻⁷` of the true mass.
-/
import RequestProject.HeckeShapeTable
import RequestProject.SporadicSvg

namespace HeckeShapeSvg

open PrimeFibers Sporadic HeckeShapes
open SporadicSvg (fmt attr rectTag lineTag circleTag textTag polylineTag fmtFixed orderDigits
  factorString)

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The data of the pictures -/

/-- The visible mass contributed by one `(prime, exponent)` pair, as a `Float`. -/
def factorMass (pe : ℕ × ℕ) : Float :=
  ((visExponents pe).map fun k => (refAbs (pe.1 ^ k)).toFloat).foldl (· + ·) 0.0

/-- The visible Hecke mass of the shape of `G`, as a `Float`. -/
def massF (G : Group) : Float := (G.factors.map factorMass).foldl (· + ·) 0.0

/-- The shape efficiency of `G`, as a `Float`. -/
def effF (G : Group) : Float := massF G / Float.ofNat (dim G)

/-- The twenty-six groups ranked by shape efficiency, most efficient first. -/
def ranked : List Group :=
  (groups.mergeSort fun A B => decide (effF B ≤ effF A))

theorem ranked_length : ranked.length = 26 := by native_decide

/-- The three groups singled out by the ranking discussion. -/
def highlighted : List String := ["M11", "J2", "M24"]

def isHighlighted (G : Group) : Bool := highlighted.contains G.name

/-! ## Picture 1: mass against dimension, ranked by efficiency -/

private def rowTop : Float := 250.0
private def rowH : Float := 46.0
private def massLeft : Float := 250.0
private def massScale : Float := 38.0
private def dimLeft : Float := 1230.0
private def dimScale : Float := 5.6

private def massSegments (G : Group) : String :=
  String.intercalate "\n" ((G.factors.foldl (fun (acc : Float × List String) pe =>
      let w := factorMass pe * massScale
      let seg := rectTag (massLeft + acc.1) (rowTop - 26.0) w (rowH - 20.0)
        (fiberColor pe.1) "#ffffff" 0.92
      (acc.1 + w, acc.2 ++ [seg])) (0.0, [])).2)

private def dimSegments (G : Group) : String :=
  String.intercalate "\n" ((G.factors.foldl (fun (acc : Float × List String) pe =>
      let w := Float.ofNat pe.2 * dimScale
      let seg := rectTag (dimLeft + acc.1) (rowTop - 22.0) w (rowH - 28.0)
        (fiberColor pe.1) "#ffffff" 0.55
      (acc.1 + w, acc.2 ++ [seg])) (0.0, [])).2)

private def rowSvg (i : ℕ) (G : Group) : String :=
  let dy := Float.ofNat i * rowH
  let hl := isHighlighted G
  let mon := G.name == "M"
  "  <g transform=\"translate(0," ++ fmt dy ++ ")\">\n" ++
  (if hl || mon then
      rectTag 60.0 (rowTop - 32.0) 1860.0 (rowH - 8.0)
        (if mon then "#fee2e2" else "#e0f2fe") "" 1.0 ++ "\n"
    else "") ++
  textTag 230.0 (rowTop - 6.0) 15 "#111827" "end" (if hl || mon then "700" else "500")
    G.name ++ "\n" ++
  textTag 66.0 (rowTop - 6.0) 12 "#6b7280" "start" "400"
    ("10^" ++ toString (orderDigits G - 1)) ++ "\n" ++
  massSegments G ++ "\n" ++
  textTag (massLeft + massF G * massScale + 10.0) (rowTop - 6.0) 13 "#374151" "start" "600"
    (fmtFixed 2 (massF G)) ++ "\n" ++
  dimSegments G ++ "\n" ++
  textTag (dimLeft + Float.ofNat (dim G) * dimScale + 10.0) (rowTop - 6.0) 13 "#374151" "start"
    "600" (toString (dim G)) ++ "\n" ++
  textTag 1900.0 (rowTop - 6.0) 13 (if mon then "#b91c1c" else "#111827") "end"
    (if hl || mon then "700" else "500") (fmtFixed 3 (effF G)) ++ "\n" ++
  "  </g>"

private def legendSvg : String :=
  String.intercalate "\n" (([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 59, 67,
      71] : List ℕ).zipIdx.map fun (p, j) =>
    let x := 250.0 + Float.ofNat j * 92.0
    rectTag x 174.0 16.0 16.0 (fiberColor p) "#ffffff" 0.92 ++ "\n" ++
      textTag (x + 22.0) 187.0 13 "#374151" "start" "500" (toString p))

/-- Picture 1: the twenty-six shapes, ranked by shape efficiency. -/
def efficiencySvg : String :=
  let height : Float := rowTop + 26.0 * rowH + 150.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" "1960" ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 1960 " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 1960.0 height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 60.0 24 "#111827" "start" "700"
    "How much shape does each sporadic group buy in Hecke space?" ++ "\n" ++
  textTag 60.0 90.0 15 "#4b5563" "start" "400"
    ("left bar: visible Hecke mass of the group's shape, the sum of |tau(n)|/n^(11/2) over the" ++
      " prime powers p^k <= 256 with k <= v_p(|G|), coloured by prime") ++ "\n" ++
  textTag 60.0 114.0 15 "#4b5563" "start" "400"
    ("right bar: the number of Hecke coordinates the group pays for, dim G = sum of the" ++
      " exponents; far right: the efficiency, mass per coordinate") ++ "\n" ++
  textTag 60.0 138.0 15 "#4b5563" "start" "400"
    ("rows are ranked by efficiency: the Monster is last of all twenty-six" ++
      " (shapeEfficiency_monster_min), M11, J2 and M24 are near the top") ++ "\n" ++
  textTag 60.0 162.0 15 "#4b5563" "start" "400"
    "the left column is the number of decimal digits of |G|, as a power of ten" ++ "\n" ++
  legendSvg ++ "\n" ++
  textTag 250.0 (rowTop - 46.0) 14 "#111827" "start" "700" "visible Hecke mass" ++ "\n" ++
  textTag 1230.0 (rowTop - 46.0) 14 "#111827" "start" "700" "Hecke coordinates (dim)" ++ "\n" ++
  textTag 1900.0 (rowTop - 46.0) 14 "#111827" "end" "700" "mass / dim" ++ "\n" ++
  String.intercalate "\n" (ranked.zipIdx.map fun (G, i) => rowSvg i G) ++ "\n" ++
  textTag 60.0 (rowTop + 26.0 * rowH + 40.0) 14 "#4b5563" "start" "500"
    ("M11 (order 7920) already carries more than 23% of the Monster's visible mass with 8 of" ++
      " its 95 coordinates; J2 more than 37% with 13; M24 more than 45% with 17.") ++ "\n" ++
  textTag 60.0 (rowTop + 26.0 * rowH + 66.0) 14 "#4b5563" "start" "500"
    ("Together M11, J2 and M24 light up 16 of the Monster's 31 visible points and carry more" ++
      " than 48% of its visible mass.") ++
  "\n</svg>\n"

/-! ## Picture 2: the Monster's own shape, prime by prime -/

private def monsterFactors : List (ℕ × ℕ) := monster.factors

private def barLeft : Float := 160.0
private def barBottom : Float := 620.0
private def barScale : Float := 70.0
private def barW : Float := 76.0
private def barGap : Float := 22.0

private def primeBar (j : ℕ) (pe : ℕ × ℕ) : String :=
  let x := barLeft + Float.ofNat j * (barW + barGap)
  let h := factorMass pe * barScale
  rectTag x (barBottom - h) barW h (fiberColor pe.1) "#ffffff" 0.92 ++ "\n" ++
  textTag (x + barW / 2.0) (barBottom - h - 12.0) 14 "#111827" "middle" "700"
    (fmtFixed 2 (factorMass pe)) ++ "\n" ++
  textTag (x + barW / 2.0) (barBottom + 24.0) 16 (fiberColor pe.1) "middle" "700"
    (toString pe.1) ++ "\n" ++
  textTag (x + barW / 2.0) (barBottom + 46.0) 13 "#4b5563" "middle" "500"
    ("^" ++ toString pe.2) ++ "\n" ++
  textTag (x + barW / 2.0) (barBottom + 68.0) 12 "#6b7280" "middle" "400"
    (toString (visExponents pe).length ++ " pt" ++
      (if (visExponents pe).length == 1 then "" else "s"))

/-- Picture 2: the Monster's shape prime by prime, small primes against large. -/
def monsterPrimesSvg : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" "1700" ++ " " ++
    attr "height" "820" ++ " " ++ attr "viewBox" "0 0 1700 820" ++ ">\n" ++
  rectTag 0.0 0.0 1700.0 820.0 "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 60.0 24 "#111827" "start" "700"
    "The Monster's shape, prime by prime" ++ "\n" ++
  textTag 60.0 92.0 15 "#4b5563" "start" "400"
    ("each bar is the visible Hecke mass the prime contributes to the shape of |M| =" ++
      " 2^46 . 3^20 . 5^9 . 7^6 . 11^2 . 13^3 . 17 . 19 . 23 . 29 . 31 . 41 . 47 . 59 . 71") ++
    "\n" ++
  textTag 60.0 116.0 15 "#4b5563" "start" "400"
    ("under each prime: its exponent in |M|, and how many of its powers are inside the" ++
      " plotted window n <= 256") ++ "\n" ++
  rectTag 140.0 150.0 590.0 34.0 "#eef2ff" "" 1.0 ++ "\n" ++
  textTag 152.0 173.0 15 "#3730a3" "start" "700"
    "six small primes: 86 of the 95 coordinates" ++ "\n" ++
  rectTag 760.0 150.0 880.0 34.0 "#fef2f2" "" 1.0 ++ "\n" ++
  textTag 772.0 173.0 15 "#b91c1c" "start" "700"
    "nine large primes: exponent one each, 9 coordinates, one plotted point each" ++ "\n" ++
  lineTag barLeft barBottom 1640.0 barBottom "#9aa4b2" 1.2 "" ++ "\n" ++
  lineTag 742.0 220.0 742.0 (barBottom + 80.0) "#9aa4b2" 1.2 "6 4" ++ "\n" ++
  String.intercalate "\n" (monsterFactors.zipIdx.map fun (pe, j) => primeBar j pe) ++ "\n" ++
  textTag 60.0 700.0 15 "#111827" "start" "700"
    "Beyond the window: the full Hecke mass of the shape" ++ "\n" ++
  textTag 60.0 726.0 14 "#4b5563" "start" "400"
    ("consecutive points of a fiber can never both be small (|y_k| + |y_(k+1)| >= 0.7), so the" ++
      " six small primes carry mass at least 29.4 over all 86 of their coordinates,") ++ "\n" ++
  textTag 60.0 750.0 14 "#4b5563" "start" "400"
    ("while the nine large primes carry less than 7.98 in total: three times less" ++
      " (monster_large_lt_third_small), under 22% of the whole.") ++
  "\n</svg>\n"

/-! ## The table -/

/-- `visualization/hecke_shapes.csv`. -/
def shapesCsv : String :=
  "name,order_digits,dim,small_dim,large_dim,visible_points,visible_mass,shape_efficiency\n" ++
  String.intercalate "\n" (ranked.map fun G =>
    G.name ++ "," ++ toString (orderDigits G) ++ "," ++ toString (dim G) ++ "," ++
      toString (smallDim G) ++ "," ++ toString (largeDim G) ++ "," ++
      toString (visDim G) ++ "," ++ fmtFixed 6 (massF G) ++ "," ++ fmtFixed 6 (effF G)) ++ "\n"

end HeckeShapeSvg

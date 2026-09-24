/-
# The expanded diagram: the twenty-six sporadic groups, their prime exponents, and zeta

Three pictures, all drawn from the verified table `Sporadic.groups`:

* `visualization/sporadic-prime-grid.svg` — the 26 × 18 grid of the sporadic groups against the
  eighteen primes that divide their orders, each cell carrying the exponent of that prime in
  that group's order, in that prime's fiber colour;
* `visualization/sporadic-two-exponents.svg` — the fiber of `2` expanded to its forty-six
  exponents `2^1, …, 2^46`, with each sporadic group placed at its own power of `2` (the
  Monster at `2^46`);
* `visualization/monster-zeta-euler.svg` — the fifteen Euler factors of `ζ` at the primes of
  the Monster, and the cumulative product of those factors compared with `ζ(2) = π²/6`.

Only floating-point coordinates and string manipulation live here; the exponents drawn are
the entries of `Sporadic.groups`, which `Sporadic.exponent_eq_factorization` proves to be the
`p`-adic valuations of the group orders.
-/
import RequestProject.MonsterZeta
import RequestProject.FiberColors

namespace SporadicSvg

open PrimeFibers Sporadic

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The data of the picture -/

/-- The eighteen primes dividing sporadic group orders, in increasing order. -/
def primeCols : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 59, 67, 71]

/-- The columns of the grid are exactly the primes that occur. -/
theorem primeCols_toFinset : primeCols.toFinset = sporadicPrimes := by decide

theorem primeCols_length : primeCols.length = 18 := rfl

/-- Every column of the grid gets a genuine fiber colour (none is the neutral colour). -/
theorem fiberColor_primeCols : ∀ p ∈ primeCols, fiberColor p ≠ neutralColor := by decide

/-- The rows of the grid: the twenty-six sporadic groups. -/
def rows : List Group := groups

theorem rows_length : rows.length = 26 := rfl

/-- The number drawn in the cell of group `G` and prime `p`: the exponent of `p` in `|G|`,
which is its `p`-adic valuation. -/
def cellExponent (G : Group) (p : ℕ) : ℕ := G.exponent p

theorem cellExponent_eq_factorization {G : Group} (hG : G ∈ groups) (p : ℕ) :
    cellExponent G p = G.order.factorization p :=
  (exponent_eq_factorization hG p).symm

/-- The largest exponent anywhere in the grid is the Monster's `46` for the prime `2`. -/
theorem cellExponent_le_46 : ∀ G ∈ rows, ∀ p ∈ primeCols, cellExponent G p ≤ 46 := by decide

theorem cellExponent_monster_two : cellExponent monster 2 = 46 := by decide

/-! ## Formatting helpers -/

def fmt (x : Float) : String := toString x

def attr (k v : String) : String := k ++ "=\"" ++ v ++ "\""

def rectTag (x y w h : Float) (fill stroke : String) (opacity : Float) : String :=
  "  <rect " ++ attr "x" (fmt x) ++ " " ++ attr "y" (fmt y) ++ " " ++
    attr "width" (fmt w) ++ " " ++ attr "height" (fmt h) ++ " " ++ attr "fill" fill ++ " " ++
    attr "fill-opacity" (fmt opacity) ++
    (if stroke = "" then "" else " " ++ attr "stroke" stroke ++ " " ++
      attr "stroke-width" "0.8") ++ "/>"

def lineTag (x1 y1 x2 y2 : Float) (stroke : String) (width : Float)
    (dash : String) : String :=
  "  <line " ++ attr "x1" (fmt x1) ++ " " ++ attr "y1" (fmt y1) ++ " " ++
    attr "x2" (fmt x2) ++ " " ++ attr "y2" (fmt y2) ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt width) ++
    (if dash = "" then "" else " " ++ attr "stroke-dasharray" dash) ++ "/>"

def circleTag (cx cy r : Float) (fill stroke : String) : String :=
  "  <circle " ++ attr "cx" (fmt cx) ++ " " ++ attr "cy" (fmt cy) ++ " " ++
    attr "r" (fmt r) ++ " " ++ attr "fill" fill ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" "1.2" ++ "/>"

/-- Positioned just after an `&`, does this begin a well-formed XML character
reference (`#8804;`, `#x22;` or `amp;`)? -/
private def startsCharRef : List Char → Bool :=
  let rec go : List Char → Nat → Bool
    | ';' :: _, n => n > 0
    | c :: rest, n => if n < 12 && (c.isAlphanum || c == '#') then go rest (n + 1) else false
    | [], _ => false
  fun cs => go cs 0

/-- Escape the characters that are not allowed raw in XML character data, so that
text bodies containing `<`, `>` or a bare `&` (e.g. `n <= 256`) still produce
well-formed SVG. Existing character references such as `&#8804;` are left intact. -/
def xmlEscape (s : String) : String :=
  let rec go : List Char → String
    | [] => ""
    | '<' :: cs => "&lt;" ++ go cs
    | '>' :: cs => "&gt;" ++ go cs
    | '&' :: cs => (if startsCharRef cs then "&" else "&amp;") ++ go cs
    | c :: cs => c.toString ++ go cs
  go s.toList

def textTag (x y : Float) (size : ℕ) (fill anchor weight body : String) : String :=
  "  <text " ++ attr "x" (fmt x) ++ " " ++ attr "y" (fmt y) ++ " " ++
    attr "font-family" "ui-monospace, SFMono-Regular, Menlo, monospace" ++ " " ++
    attr "font-size" (toString size) ++ " " ++ attr "font-weight" weight ++ " " ++
    attr "fill" fill ++ " " ++ attr "text-anchor" anchor ++ ">" ++ xmlEscape body ++ "</text>"

def polylineTag (pts : List (Float × Float)) (stroke : String) (width : Float) : String :=
  "  <polyline " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++
    " " ++ attr "fill" "none" ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt width) ++ "/>"

def padLeft (n : ℕ) (c : Char) (s : String) : String :=
  if s.length < n then String.ofList (List.replicate (n - s.length) c) ++ s else s

/-- `x` rounded to `places` decimals, as a fixed-point string. -/
def fmtFixed (places : ℕ) (x : Float) : String :=
  let neg := x < 0.0
  let scaled := (x.abs * (10.0 : Float) ^ Float.ofNat places + 0.5).floor
  let digits := padLeft (places + 1) '0' (toString scaled.toUInt64.toNat)
  let cs := digits.toList
  let intPart := String.ofList (cs.take (cs.length - places))
  let frac := String.ofList (cs.drop (cs.length - places))
  (if neg then "-" else "") ++ intPart ++ "." ++ frac

/-- The number of decimal digits of the order of `G`. -/
def orderDigits (G : Group) : ℕ := (toString G.order).length

/-- The factorization of `|G|` as a printable string, e.g. `2^46·3^20·…`. -/
def factorString (G : Group) : String :=
  String.intercalate "\u00b7" (G.factors.map fun pe =>
    toString pe.1 ++ (if pe.2 = 1 then "" else "^" ++ toString pe.2))

/-! ## Picture 1: the 26 × 18 grid -/

private def gridLeft : Float := 220.0
private def gridTop : Float := 150.0
private def cellW : Float := 62.0
private def cellH : Float := 34.0

private def gridCell (i j : ℕ) (G : Group) (p : ℕ) : String :=
  let e := cellExponent G p
  let x := gridLeft + Float.ofNat j * cellW
  let y := gridTop + Float.ofNat i * cellH
  if e = 0 then
    rectTag x y (cellW - 2.0) (cellH - 2.0) "#f5f7fa" "#e7ebf1" 1.0
  else
    let op := 0.18 + 0.82 * Float.ofNat e / 46.0
    rectTag x y (cellW - 2.0) (cellH - 2.0) (fiberColor p) "#c9d1dc" op ++ "\n" ++
      textTag (x + (cellW - 2.0) / 2.0) (y + 22.0) 13
        (if e ≥ 12 then "#ffffff" else "#111827") "middle" "700" (toString e)

private def gridRow (i : ℕ) (G : Group) : String :=
  textTag (gridLeft - 14.0) (gridTop + Float.ofNat i * cellH + 22.0) 13 "#111827" "end" "700"
    G.name ++ "\n" ++
  String.intercalate "\n" (primeCols.zipIdx.map fun (p, j) => gridCell i j G p) ++ "\n" ++
  textTag (gridLeft + 18.0 * cellW + 16.0) (gridTop + Float.ofNat i * cellH + 22.0) 12
    "#4b5563" "start" "500" ("|G| ~ 10^" ++ toString (orderDigits G - 1))

private def gridHeader : String :=
  String.intercalate "\n" (primeCols.zipIdx.map fun (p, j) =>
    textTag (gridLeft + Float.ofNat j * cellW + (cellW - 2.0) / 2.0) (gridTop - 14.0) 14
      (fiberColor p) "middle" "700" (toString p))

/-- The grid of the twenty-six sporadic groups against the eighteen primes. -/
def sporadicGridSvg : String :=
  let width : Float := gridLeft + 18.0 * cellW + 210.0
  let height : Float := gridTop + 26.0 * cellH + 120.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 56.0 22 "#111827" "start" "700"
    "The twenty-six sporadic simple groups and the eighteen primes dividing their orders" ++
    "\n" ++
  textTag 60.0 82.0 14 "#4b5563" "start" "400"
    ("each cell is the exponent of that prime in that group's order (its p-adic valuation);" ++
      " colours are the prime-fiber colours") ++ "\n" ++
  textTag 60.0 104.0 14 "#4b5563" "start" "400"
    ("the Monster row is 2^46 \u00b7 3^20 \u00b7 5^9 \u00b7 7^6 \u00b7 11^2 \u00b7 13^3 \u00b7 17 \u00b7 19 \u00b7 23 \u00b7 29" ++
      " \u00b7 31 \u00b7 41 \u00b7 47 \u00b7 59 \u00b7 71; the columns 37, 43, 67 occur only in the pariahs Ly and J4") ++
    "\n" ++
  gridHeader ++ "\n" ++
  String.intercalate "\n" (rows.zipIdx.map fun (G, i) => gridRow i G) ++ "\n" ++
  textTag 60.0 (gridTop + 26.0 * cellH + 46.0) 13 "#4b5563" "start" "500"
    ("53 and 61 are the only primes below 72 that divide no sporadic group.") ++
  "\n</svg>\n"

/-! ## Picture 2: the fiber of `2`, expanded to its forty-six exponents -/

private def axLeft : Float := 110.0
private def axRight : Float := 1580.0
private def axY : Float := 250.0

private def xOfK (k : ℕ) : Float :=
  axLeft + Float.ofNat k * (axRight - axLeft) / 47.0

/-- The groups whose order has `2`-exponent exactly `k`. -/
def groupsWithTwoExponent (k : ℕ) : List Group :=
  groups.filter fun G => G.exponent 2 = k

/-- Every sporadic group appears at exactly one of the forty-six positions. -/
theorem groupsWithTwoExponent_cover :
    ((List.range 47).map fun k => (groupsWithTwoExponent k).length).sum = 26 := by decide

private def tickSvg (k : ℕ) : String :=
  let x := xOfK k
  let gs := groupsWithTwoExponent k
  lineTag x (axY - 10.0) x (axY + 10.0) "#9aa4b2" 1.0 "" ++ "\n" ++
  circleTag x axY (if gs.isEmpty then 3.0 else 6.5) (fiberColor 2)
    (if gs.isEmpty then "#ffffff" else "#111827") ++ "\n" ++
  textTag x (axY + 30.0) 11 "#6b7280" "middle" "500" (toString k) ++
  (if gs.isEmpty then "" else
    "\n" ++ String.intercalate "\n" (gs.zipIdx.map fun (G, i) =>
      textTag x (axY - 22.0 - Float.ofNat i * 15.0) 12 "#111827" "middle" "700" G.name))

/-- The fiber of `2`, from `2^1` to `2^46`, with the sporadic groups placed on it. -/
def twoFiberSvg : String :=
  let width : Float := 1660.0
  let height : Float := 430.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 52.0 22 "#111827" "start" "700"
    "The fiber of 2, expanded to its forty-six exponents 2^1, \u2026, 2^46" ++ "\n" ++
  textTag 60.0 78.0 14 "#4b5563" "start" "400"
    ("each sporadic group sits at the exact power of 2 dividing its order;" ++
      " the Monster is at 2^46, the Baby Monster at 2^41") ++ "\n" ++
  lineTag axLeft axY axRight axY (fiberColor 2) 2.0 "" ++ "\n" ++
  String.intercalate "\n" ((List.range 47).drop 1 |>.map tickSvg) ++ "\n" ++
  textTag ((axLeft + axRight) / 2.0) (axY + 66.0) 13 "#4b5563" "middle" "500"
    "k   (the fiber point is n = 2^k)" ++
  "\n</svg>\n"

/-! ## Picture 3: the Monster's factors against the Euler factors of zeta -/

/-- The Euler factor `(1 - p^{-s})⁻¹` of `ζ`, in floating point. -/
def eulerFloat (p : ℕ) (s : Float) : Float :=
  1.0 / (1.0 - 1.0 / (Float.ofNat p) ^ s)

/-- The primes of the Monster with their exponents, in floating point order. -/
def monsterFactorList : List (ℕ × ℕ) := monster.factors

theorem monsterFactorList_length : monsterFactorList.length = 15 := rfl

/-- The base-10 logarithm of the truncation defect
`p^{-(e+1)s} (1 - p^{-s})⁻¹` of the Monster's local factor at `p`. -/
def defectLog10 (p e : ℕ) (s : Float) : Float :=
  (Float.ofNat (e + 1)) * s * (- Float.log (Float.ofNat p) / Float.log 10.0) +
    Float.log (eulerFloat p s) / Float.log 10.0

private def zetaTwo : Float := 1.6449340668482264

private def bLeft : Float := 130.0
private def bRight : Float := 1520.0
private def bBase : Float := 560.0
private def bScale : Float := 900.0

private def cumProducts : List Float :=
  (monsterFactorList.foldl (fun acc pe => (acc.1 * eulerFloat pe.1 2.0,
      acc.2 ++ [acc.1 * eulerFloat pe.1 2.0])) ((1.0 : Float), ([] : List Float))).2

private def slot : Float := (bRight - bLeft) / 15.0

private def barSvg (i : ℕ) (pe : ℕ × ℕ) : String :=
  let v := eulerFloat pe.1 2.0
  let x := bLeft + Float.ofNat i * slot + slot * 0.16
  let w := slot * 0.68
  let h := (v - 1.0) * bScale
  let y := bBase - h
  rectTag x y w h (fiberColor pe.1) "#111827" 0.85 ++ "\n" ++
  textTag (x + w / 2.0) (y - 24.0) 12 "#111827" "middle" "700" (fmtFixed 4 v) ++ "\n" ++
  textTag (x + w / 2.0) (y - 10.0) 10 "#6b7280" "middle" "500"
    ("defect 10^" ++ fmtFixed 1 (defectLog10 pe.1 pe.2 2.0)) ++ "\n" ++
  textTag (x + w / 2.0) (bBase + 20.0) 13 "#374151" "middle" "700" (toString pe.1) ++ "\n" ++
  textTag (x + w / 2.0) (bBase + 38.0) 12 (fiberColor pe.1) "middle" "700"
    ("^" ++ toString pe.2)

private def cLeft : Float := 130.0
private def cRight : Float := 1520.0
private def cBase : Float := 1020.0
private def cScale : Float := 520.0

private def cumSvg : String :=
  let pts := cumProducts.zipIdx.map fun (v, i) =>
    (cLeft + Float.ofNat i * (cRight - cLeft) / 14.0, cBase - (v - 1.0) * cScale)
  polylineTag pts "#111827" 2.0 ++ "\n" ++
  String.intercalate "\n" (cumProducts.zipIdx.map fun (v, i) =>
    let x := cLeft + Float.ofNat i * (cRight - cLeft) / 14.0
    circleTag x (cBase - (v - 1.0) * cScale) 5.0 (fiberColor (monsterFactorList[i]!).1)
      "#ffffff" ++ "\n" ++
    textTag x (cBase - (v - 1.0) * cScale - 14.0) 11 "#374151" "middle" "600" (fmtFixed 4 v) ++
    "\n" ++
    textTag x (cBase + 20.0) 12 "#4b5563" "middle" "600" (toString (monsterFactorList[i]!).1)) ++
  "\n" ++
  lineTag cLeft (cBase - (zetaTwo - 1.0) * cScale) cRight (cBase - (zetaTwo - 1.0) * cScale)
    "#e6194b" 1.6 "6 5" ++ "\n" ++
  textTag cRight (cBase - (zetaTwo - 1.0) * cScale - 10.0) 13 "#e6194b" "end" "700"
    ("\u03b6(2) = \u03c0\u00b2/6 = " ++ fmtFixed 4 zetaTwo)

/-- The Monster's local factors against the Euler factors of `ζ`, at `s = 2`. -/
def monsterZetaSvg : String :=
  let width : Float := 1620.0
  let height : Float := 1120.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 52.0 22 "#111827" "start" "700"
    "The factors of the Monster against the Euler factors of \u03b6, at s = 2" ++ "\n" ++
  textTag 60.0 78.0 14 "#4b5563" "start" "400"
    ("top: the Euler factor (1 - p^-s)^-1 of \u03b6 at each of the fifteen primes of |M|," ++
      " with the exponent that prime carries in |M| and the size of the truncation defect") ++
    "\n" ++
  textTag 60.0 100.0 14 "#4b5563" "start" "400"
    ("bottom: the cumulative product of those fifteen factors, which stays below \u03b6(2)") ++
    "\n" ++
  lineTag bLeft bBase bRight bBase "#9aa4b2" 1.4 "" ++ "\n" ++
  String.intercalate "\n" (monsterFactorList.zipIdx.map fun (pe, i) => barSvg i pe) ++ "\n" ++
  textTag bLeft 150.0 14 "#111827" "start" "600"
    ("(1 - p\u207b\u02e2)\u207b\u00b9 - 1   (bar height), with the Monster exponent below each prime") ++
    "\n" ++
  textTag cLeft 700.0 14 "#111827" "start" "600"
    "cumulative product of the fifteen Euler factors, versus \u03b6(2)" ++ "\n" ++
  cumSvg ++
  "\n</svg>\n"

/-! ## The table, as CSV -/

/-- The sporadic groups with their orders and factorizations. -/
def sporadicCsv : String :=
  "group,order,factorization,exponent_of_2,digits\n" ++
  String.intercalate "\n" (groups.map fun G =>
    String.intercalate "," [G.name, toString G.order, "\"" ++ factorString G ++ "\"",
      toString (G.exponent 2), toString (orderDigits G)]) ++ "\n"

end SporadicSvg

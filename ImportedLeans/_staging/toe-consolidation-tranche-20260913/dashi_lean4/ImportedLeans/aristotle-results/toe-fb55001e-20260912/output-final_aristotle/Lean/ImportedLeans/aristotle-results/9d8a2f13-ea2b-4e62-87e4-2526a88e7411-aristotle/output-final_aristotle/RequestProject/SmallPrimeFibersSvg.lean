/-
# The diagram with the fibers of `5`, `7`, `11` and `13` added

`visualization/sporadic-small-prime-fibers.svg` extends
`visualization/sporadic-two-exponents.svg` from the single fiber of `2` to the six small
primes of the Monster, `2, 3, 5, 7, 11, 13`, in three panels:

* **A** — the six fibers on a common *exponent* axis `k = 0, …, 46`: the Monster's exponents
  `46, 20, 9, 6, 2, 3` (and `11^3` in `J4`), with every sporadic group placed at the exact
  power of that prime dividing its order;
* **B** — the same six fibers on the *height* axis `z = k·log p` used by the spiral pictures,
  with the stack `log smallPart = 92.508` inside `log |M| = 124.126`;
* **C** — the six primes against `ζ` at `s = 2`: each truncated Monster factor next to the
  Euler factor `(1 - p^{-2})⁻¹` of `ζ`, and the cumulative product climbing to
  `715715/442368 = 1.617918`, against `ζ(2) = π²/6 = 1.644934`.

The numbers drawn are the entries of the verified table `Sporadic.groups`; the exponents are
`p`-adic valuations (`Sporadic.exponent_eq_factorization`), the row maxima are proved in
`RequestProject/SmallPrimeFibers.lean`, and the value of the six-factor product at `s = 2`
is `Sporadic.smallEulerProduct_two`.
-/
import RequestProject.SmallPrimeFibers
import RequestProject.SporadicSvg

namespace SmallFiberSvg

open PrimeFibers Sporadic SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The data of the picture -/

/-- The six small primes with the largest exponent each carries in a sporadic group. -/
def smallCols : List (ℕ × ℕ) := [(2, 46), (3, 20), (5, 9), (7, 6), (11, 3), (13, 3)]

/-- The four primes added at this step. -/
def newCols : List ℕ := [5, 7, 11, 13]

/-- The columns of the picture are the six small primes. -/
theorem smallCols_primes : (smallCols.map Prod.fst).toFinset = smallPrimes := by decide

/-- The row lengths really are the maximal exponents over the twenty-six groups. -/
theorem smallCols_max : ∀ pe ∈ smallCols, ∀ G ∈ groups, G.exponent pe.1 ≤ pe.2 := by decide

/-- Each row length is attained by some sporadic group. -/
theorem smallCols_attained : ∀ pe ∈ smallCols, ∃ G ∈ groups, G.exponent pe.1 = pe.2 := by decide

/-- The Monster's own exponents of the six small primes. -/
def monsterExp (p : ℕ) : ℕ := monster.exponent p

theorem monsterExp_values :
    smallCols.map (fun pe => monsterExp pe.1) = [46, 20, 9, 6, 2, 3] := by decide

/-- The sporadic groups whose order has `p`-exponent exactly `k`. -/
def groupsAt (p k : ℕ) : List Group := groups.filter fun G => G.exponent p = k

/-- Every group is placed exactly once in every row (the `k = 0` slot holding the groups
whose order that prime does not divide). -/
theorem groupsAt_cover : ∀ pe ∈ smallCols,
    ((List.range (pe.2 + 1)).map fun k => (groupsAt pe.1 k).length).sum = 26 := by decide

/-- The number of groups placed at a positive exponent of `p`. -/
def rowPlaced (p e : ℕ) : ℕ := (((List.range (e + 1)).drop 1).map fun k => (groupsAt p k).length).sum

theorem rowPlaced_values :
    smallCols.map (fun pe => rowPlaced pe.1 pe.2) = [26, 26, 26, 23, 21, 9] := by decide

/-! ## Panel A: the six fibers on the exponent axis -/

private def aLeft : Float := 230.0
private def aRight : Float := 1700.0
private def aTop : Float := 240.0
private def rowGap : Float := 132.0

/-- Each row is drawn on its own scale, so that its `e + 1` exponents fill the width; the
true common scale is panel B. -/
private def xOfK (e k : ℕ) : Float :=
  aLeft + Float.ofNat k * (aRight - aLeft) / Float.ofNat e

private def rowY (i : ℕ) : Float := aTop + Float.ofNat i * rowGap

private def tickA (i : ℕ) (p e k : ℕ) : String :=
  let x := xOfK e k
  let y := rowY i
  let gs := groupsAt p k
  let n := gs.length
  let r := if n = 0 then 3.0 else
    (if 4.5 + 1.2 * Float.ofNat n > 17.0 then 17.0 else 4.5 + 1.2 * Float.ofNat n)
  let stagger := if k % 2 = 1 then 16.0 else 0.0
  if k = 0 then
    -- the slot `k = 0` is not part of the fiber: it collects the groups `p` does not divide
    circleTag x y 4.0 "#ffffff" "#9aa4b2" ++ "\n" ++
    textTag x (y + 30.0) 11 "#9aa4b2" "middle" "500" "0" ++ "\n" ++
    textTag x (y - 22.0) 10 "#9aa4b2" "middle" "500"
      (toString n ++ " with no " ++ toString p)
  else
    lineTag x (y - 8.0) x (y + 8.0) "#9aa4b2" 1.0 "" ++ "\n" ++
    circleTag x y r (fiberColor p) (if n = 0 then "#ffffff" else "#111827") ++ "\n" ++
    textTag x (y + 30.0) 11 "#6b7280" "middle" "500" (toString k) ++
    (if n = 0 then "" else
      if n ≤ 3 then
        "\n" ++ String.intercalate "\n" (gs.zipIdx.map fun (G, j) =>
          textTag x (y - 22.0 - stagger - Float.ofNat j * 14.0) 11 "#111827" "middle" "700"
            G.name)
      else
        "\n" ++ textTag x (y - 22.0 - stagger) 11 "#111827" "middle" "700"
          (toString n ++ " groups"))

private def rowA (i : ℕ) (pe : ℕ × ℕ) : String :=
  let y := rowY i
  let p := pe.1
  let e := pe.2
  lineTag aLeft y aRight y (fiberColor p) 2.2 "" ++ "\n" ++
  textTag (aLeft - 26.0) (y + 5.0) 15 (fiberColor p) "end" "700"
    ("p = " ++ toString p) ++ "\n" ++
  textTag (aLeft - 26.0) (y + 24.0) 11 "#6b7280" "end" "500"
    ("|M| : " ++ toString p ++ "^" ++ toString (monsterExp p)) ++ "\n" ++
  textTag (aRight + 16.0) (y + 5.0) 12 "#4b5563" "start" "600"
    ("max " ++ toString p ++ "^" ++ toString e ++
      (if e = monsterExp p then " (M)" else " (J4)")) ++ "\n" ++
  String.intercalate "\n" ((List.range (e + 1)).map fun k => tickA i p e k)

/-! ## Panel B: the same fibers on the height axis `z = k log p` -/

private def bLeft : Float := 230.0
private def bRight : Float := 1560.0
private def bTop : Float := 1080.0
private def bGap : Float := 74.0

private def logF (p : ℕ) : Float := Float.log (Float.ofNat p)

private def zMax : Float := 33.0

private def xOfZ (z : Float) : Float := bLeft + z * (bRight - bLeft) / zMax

private def rowB (i : ℕ) (pe : ℕ × ℕ) : String :=
  let y := bTop + Float.ofNat i * bGap
  let p := pe.1
  let e := pe.2
  let zTop := Float.ofNat e * logF p
  lineTag bLeft y (xOfZ zTop) y (fiberColor p) 2.0 "" ++ "\n" ++
  textTag (bLeft - 24.0) (y + 5.0) 14 (fiberColor p) "end" "700" ("p = " ++ toString p) ++
  "\n" ++
  String.intercalate "\n" ((List.range (e + 1)).drop 1 |>.map fun k =>
    circleTag (xOfZ (Float.ofNat k * logF p)) y 3.4 (fiberColor p) "#ffffff") ++ "\n" ++
  textTag (xOfZ zTop + 12.0) (y + 5.0) 12 "#374151" "start" "600"
    (toString p ++ "^" ++ toString e ++ (if e = monsterExp p then "" else " (J4)") ++
      " : z = " ++ fmtFixed 2 zTop)

/-- The heights of the six Monster fibers, and the height left over for the nine remaining
primes. -/
private def stackSegments : List (ℕ × Float) :=
  [(2, 46.0 * logF 2), (3, 20.0 * logF 3), (5, 9.0 * logF 5), (7, 6.0 * logF 7),
   (11, 2.0 * logF 11), (13, 3.0 * logF 13)]

private def smallHeight : Float := (stackSegments.map Prod.snd).foldl (· + ·) 0.0

private def monsterHeight : Float :=
  smallHeight + logF 17 + logF 19 + logF 23 + logF 29 + logF 31 + logF 41 + logF 47 +
    logF 59 + logF 71

private def stackY : Float := bTop + 6.0 * bGap + 56.0

private def stackSvg : String :=
  let x0 := bLeft
  let w := (bRight - bLeft) / monsterHeight
  let seg := (stackSegments.foldl (fun acc pe =>
      let x := acc.1
      let out := acc.2 ++ [(pe.1, x, pe.2)]
      (x + pe.2 * w, out)) ((x0, ([] : List (ℕ × Float × Float))))).2
  String.intercalate "\n" (seg.map fun (p, x, h) =>
    rectTag x stackY (h * w) 40.0 (fiberColor p) "#ffffff" 0.9 ++ "\n" ++
    textTag (x + h * w / 2.0) (stackY + 25.0) 12 "#ffffff" "middle" "700" (toString p) ++ "\n" ++
    textTag (x + h * w / 2.0) (stackY + 56.0) 11 "#4b5563" "middle" "500" (fmtFixed 2 h)) ++
  "\n" ++
  rectTag (x0 + smallHeight * w) stackY ((monsterHeight - smallHeight) * w) 40.0
    "#9aa4b2" "#ffffff" 0.55 ++ "\n" ++
  textTag (x0 + (smallHeight + monsterHeight) * w / 2.0) (stackY + 25.0) 12 "#111827" "middle"
    "700" "17 \u2026 71" ++ "\n" ++
  textTag (x0 + (smallHeight + monsterHeight) * w / 2.0) (stackY + 56.0) 11 "#4b5563" "middle"
    "500" (fmtFixed 2 (monsterHeight - smallHeight)) ++ "\n" ++
  textTag x0 (stackY - 12.0) 13 "#111827" "start" "600"
    ("log |M| = " ++ fmtFixed 3 monsterHeight ++ ", of which the six small primes carry " ++
      fmtFixed 3 smallHeight ++ " (" ++
      fmtFixed 1 (100.0 * smallHeight / monsterHeight) ++ "%)")

/-! ## Panel C: the six primes against the Euler factors of `ζ` at `s = 2` -/

/-- The Euler factor `(1 - p^{-2})⁻¹` of `ζ`, in floating point. -/
private def euler2 (p : ℕ) : Float := 1.0 / (1.0 - 1.0 / (Float.ofNat p) ^ 2.0)

/-- The Monster's local factor at `p`: the Euler factor truncated at the exponent `e`. -/
private def trunc2 (p e : ℕ) : Float :=
  (1.0 - (1.0 / (Float.ofNat p) ^ 2.0) ^ (Float.ofNat (e + 1))) /
    (1.0 - 1.0 / (Float.ofNat p) ^ 2.0)

private def zetaTwoF : Float := 1.6449340668482264

private def cLeft : Float := 240.0
private def cRight : Float := 900.0
private def cBase : Float := 2180.0
private def cScale : Float := 1050.0

private def barC (i : ℕ) (pe : ℕ × ℕ) : String :=
  let p := pe.1
  let e := monsterExp p
  let slot := (cRight - cLeft) / 6.0
  let x := cLeft + Float.ofNat i * slot
  let w := slot * 0.30
  let hE := (euler2 p - 1.0) * cScale
  let hT := (trunc2 p e - 1.0) * cScale
  rectTag (x + slot * 0.10) (cBase - hE) w hE (fiberColor p) "#111827" 0.35 ++ "\n" ++
  rectTag (x + slot * 0.46) (cBase - hT) w hT (fiberColor p) "#111827" 0.95 ++ "\n" ++
  textTag (x + slot * 0.5) (cBase - hE - 28.0) 11 "#111827" "middle" "700"
    (fmtFixed 6 (euler2 p)) ++ "\n" ++
  textTag (x + slot * 0.5) (cBase - hE - 14.0) 10 "#6b7280" "middle" "500"
    ("defect 10^" ++ fmtFixed 1 (defectLog10 p e 2.0)) ++ "\n" ++
  textTag (x + slot * 0.5) (cBase + 20.0) 14 (fiberColor p) "middle" "700" (toString p) ++ "\n" ++
  textTag (x + slot * 0.5) (cBase + 38.0) 11 "#4b5563" "middle" "500"
    ("exponent " ++ toString e)

private def dLeft : Float := 1060.0
private def dRight : Float := 1680.0
private def dBase : Float := 2180.0
private def dScale : Float := 900.0

/-- The cumulative product is plotted from the base value `1.30`. -/
private def dFloor : Float := 1.30

private def cumList : List (ℕ × Float) :=
  (smallCols.foldl (fun acc pe =>
      let v := acc.1 * euler2 pe.1
      (v, acc.2 ++ [(pe.1, v)])) ((1.0 : Float), ([] : List (ℕ × Float)))).2

private def cumSvgC : String :=
  let pts := cumList.zipIdx.map fun (pv, i) =>
    (dLeft + Float.ofNat i * (dRight - dLeft) / 5.0, dBase - (pv.2 - dFloor) * dScale)
  polylineTag pts "#111827" 2.0 ++ "\n" ++
  String.intercalate "\n" (cumList.zipIdx.map fun (pv, i) =>
    let x := dLeft + Float.ofNat i * (dRight - dLeft) / 5.0
    let y := dBase - (pv.2 - dFloor) * dScale
    circleTag x y 5.0 (fiberColor pv.1) "#ffffff" ++ "\n" ++
    textTag x (y - 14.0) 11 "#374151" "middle" "600" (fmtFixed 5 pv.2) ++ "\n" ++
    textTag x (dBase + 20.0) 12 (fiberColor pv.1) "middle" "700" (toString pv.1)) ++ "\n" ++
  lineTag dLeft (dBase - (zetaTwoF - dFloor) * dScale) dRight
    (dBase - (zetaTwoF - dFloor) * dScale) "#e6194b" 1.6 "6 5" ++ "\n" ++
  textTag dRight (dBase - (zetaTwoF - dFloor) * dScale - 10.0) 13 "#e6194b" "end" "700"
    ("\u03b6(2) = \u03c0\u00b2/6 = " ++ fmtFixed 6 zetaTwoF)

/-! ## The whole picture -/

/-- The six small fibers `2, 3, 5, 7, 11, 13` of the sporadic groups, on the exponent axis,
on the height axis, and against `ζ`. -/
def smallFibersSvg : String :=
  let width : Float := 1800.0
  let height : Float := 2300.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 56.0 24 "#111827" "start" "700"
    "The fibers of 2 and 3 with 5, 7, 11 and 13 added: the small primes of the Monster" ++
    "\n" ++
  textTag 60.0 84.0 14 "#4b5563" "start" "400"
    ("|M| = 2^46 \u00b7 3^20 \u00b7 5^9 \u00b7 7^6 \u00b7 11^2 \u00b7 13^3 \u00b7 17 \u00b7 19 \u00b7 23 \u00b7 29 \u00b7 31" ++
      " \u00b7 41 \u00b7 47 \u00b7 59 \u00b7 71; the six small primes carry 86 of its 95 prime-power exponents") ++
    "\n" ++
  textTag 60.0 108.0 14 "#4b5563" "start" "400"
    ("A: every sporadic group placed at the exact power of each prime dividing its order;" ++
      " each row runs to the largest exponent of that prime occurring in a sporadic group," ++
      " on its own scale (the true common scale is B)") ++
    "\n" ++
  textTag 60.0 130.0 14 "#4b5563" "start" "400"
    ("the row of 11 is the exception: its maximum 11^3 belongs to the pariah J4," ++
      " not to the Monster, which carries only 11^2") ++ "\n" ++
  textTag 60.0 172.0 16 "#111827" "start" "700" "A   the six fibers on the exponent axis k" ++
    "\n" ++
  String.intercalate "\n" (smallCols.zipIdx.map fun (pe, i) => rowA i pe) ++ "\n" ++
  textTag ((aLeft + aRight) / 2.0) (rowY 5 + 62.0) 13 "#4b5563" "middle" "500"
    "k   (the fiber point is n = p^k; a dot grows with the number of groups sitting on it)" ++
    "\n" ++
  textTag 60.0 (bTop - 46.0) 16 "#111827" "start" "700"
    "B   the same six fibers on the height axis z = k log p, and the height stack of |M|" ++
    "\n" ++
  String.intercalate "\n" (smallCols.zipIdx.map fun (pe, i) => rowB i pe) ++ "\n" ++
  stackSvg ++ "\n" ++
  textTag 60.0 1730.0 16 "#111827" "start" "700"
    "C   the six primes against \u03b6 at s = 2" ++ "\n" ++
  textTag cLeft 1764.0 13 "#4b5563" "start" "500"
    ("pale bar: Euler factor (1 - p\u207b\u00b2)\u207b\u00b9 of \u03b6;  solid bar: the Monster's factor," ++
      " truncated at its exponent") ++ "\n" ++
  lineTag cLeft cBase cRight cBase "#9aa4b2" 1.4 "" ++ "\n" ++
  String.intercalate "\n" (smallCols.zipIdx.map fun (pe, i) => barC i pe) ++ "\n" ++
  textTag dLeft 1764.0 13 "#4b5563" "start" "500"
    "cumulative product of the six Euler factors, against \u03b6(2)" ++ "\n" ++
  lineTag dLeft dBase dRight dBase "#9aa4b2" 1.4 "" ++ "\n" ++
  cumSvgC ++ "\n" ++
  textTag 60.0 (cBase + 82.0) 13 "#111827" "start" "500"
    ("the six factors multiply to exactly 715715/442368 = 1.617918, which is 98.36% of" ++
      " \u03b6(2) = 1.644934; the four new primes 5, 7, 11, 13 contribute 715715/663552 = 1.078612") ++
  "\n</svg>\n"

/-! ## The table, as CSV -/

/-- Prime, Monster exponent, largest sporadic exponent, top height, Euler factor at `s = 2`
and the running product. -/
def smallFibersCsv : String :=
  "prime,monster_exponent,max_sporadic_exponent,groups_placed,top_height,euler_factor_2," ++
    "monster_factor_2,cumulative_product\n" ++
  String.intercalate "\n" (smallCols.zipIdx.map fun (pe, i) =>
    String.intercalate "," [toString pe.1, toString (monsterExp pe.1), toString pe.2,
      toString (rowPlaced pe.1 pe.2),
      fmtFixed 5 (Float.ofNat (monsterExp pe.1) * logF pe.1),
      fmtFixed 6 (euler2 pe.1), fmtFixed 6 (trunc2 pe.1 (monsterExp pe.1)),
      fmtFixed 6 (cumList[i]!).2]) ++ "\n"

end SmallFiberSvg

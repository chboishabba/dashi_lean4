/-
# The picture: every exponent on the zeta graph, on the triple-logarithmic scale

`visualization/zeta-exponent-scale.svg` is drawn here.  It has four panels, all built from
the verified table `Sporadic.groups` and the Euler factors of `ζ`:

1. **the fifteen exponents of `|M|` on the zeta Euler-factor graph** — the curve
   `x ↦ (1 - x^{-2})⁻¹` with the fifteen supersingular primes marked on it, each dot carrying
   the exponent that prime has in `|M|` (`46, 20, 9, 6, 2, 3, 1, …, 1`) and the truncated
   Monster factor `∑_{j ≤ e} p^{-2j}` shown as a hollow dot below it;
2. **the zeta graph in `s`** — `ζ(s)`, the fifteen-factor Euler product `P(s)` and the
   Monster's divisor sum `D(s) = ∑_{d ∣ |M|} d^{-s}`, which `Sporadic.monsterDivisorSum_le_zeta`
   proves to satisfy `D ≤ P ≤ ζ`;
3. **the triple-logarithmic axis** `log log log`, on which all twenty-six sporadic groups and
   all fifteen prime powers `p^{e_p}` of `|M|` fit between `0` and `1.6`, the Monster at
   `1.5730` (proved to lie in `(1.57, 1.58)`) and its largest prime power `2^46` at `1.2419`
   (proved to lie in `(1.24, 1.25)`);
4. **the ordinary `log₁₀` axis** for contrast, where the same twenty-six points are squeezed
   against the two ends.

Only floating-point geometry and string manipulation live in this file; the numbers plotted
are the exponents of `Sporadic.groups`, proved to be `p`-adic valuations in
`Sporadic.exponent_eq_factorization`, and the bounds quoted in the picture are proved in
`RequestProject/ZetaExponentScale.lean`.
-/
import RequestProject.ZetaExponentScale
import RequestProject.SporadicSvg

namespace ZetaExponentSvg

open PrimeFibers Sporadic SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## The numbers plotted -/

/-- `ζ(s)` in floating point, by Euler–Maclaurin summation. -/
def zetaF (s : Float) : Float :=
  let N : ℕ := 24
  let head := ((List.range N).drop 1).foldl (fun acc n => acc + (Float.ofNat n) ^ (-s)) 0.0
  let Nf := Float.ofNat N
  head + Nf ^ (-s) / 2.0 + Nf ^ (1.0 - s) / (s - 1.0) + s * Nf ^ (-s - 1.0) / 12.0

/-- The Euler factor of `ζ` at `p`, truncated at the exponent `e`: `∑_{j ≤ e} p^{-js}`. -/
def truncFloat (p e : ℕ) (s : Float) : Float :=
  ((List.range (e + 1)).map fun j =>
    ((Float.ofNat p) ^ (-s)) ^ (Float.ofNat j)).foldl (· + ·) 0.0

/-- The fifteen-factor Euler product of `ζ` over the primes of `|M|`. -/
def monsterEulerF (s : Float) : Float :=
  (monster.factors.map fun pe => eulerFloat pe.1 s).foldl (· * ·) 1.0

/-- The Monster's divisor sum `∑_{d ∣ |M|} d^{-s}`, as the product of the truncated factors. -/
def monsterTruncF (s : Float) : Float :=
  (monster.factors.map fun pe => truncFloat pe.1 pe.2 s).foldl (· * ·) 1.0

/-- `log |G|`, computed from the exponents: `∑_p e_p log p`. -/
def logOrderF (G : Group) : Float :=
  (G.factors.map fun pe => Float.ofNat pe.2 * Float.log (Float.ofNat pe.1)).foldl (· + ·) 0.0

/-- The second and third logarithms of a number whose logarithm is `L`. -/
def lllOfLog (L : Float) : Float := Float.log (Float.log L)

/-- `log log log |G|`. -/
def lllGroup (G : Group) : Float := lllOfLog (logOrderF G)

/-- `log log log (p^e)`. -/
def lllPow (p e : ℕ) : Float := lllOfLog (Float.ofNat e * Float.log (Float.ofNat p))

/-- `log₁₀ |G|`. -/
def log10Group (G : Group) : Float := logOrderF G / Float.log 10.0

/-- The twenty-six groups listed in increasing order of `|G|` (hence, the scale being
faithful, in increasing order of `log log log |G|`). -/
def sortedNames : List String :=
  ["M11", "M12", "J1", "M22", "J2", "M23", "HS", "J3", "M24", "McL", "He", "Ru", "Suz",
   "ON", "Co3", "Co2", "Fi22", "HN", "Ly", "Th", "Fi23", "Co1", "J4", "Fi24'", "B", "M"]

/-- The twenty-six groups in the order in which they are drawn on the axis. -/
def sortedGroups : List Group :=
  sortedNames.filterMap fun n => groups.find? fun G => G.name == n

theorem sortedGroups_length : sortedGroups.length = 26 := by decide

/-- Every group drawn comes from the table. -/
theorem sortedGroups_subset : ∀ G ∈ sortedGroups, G ∈ groups := by decide

/-- No group is left out. -/
theorem sortedGroups_complete : ∀ G ∈ groups, G ∈ sortedGroups := by decide

/-- The list really is increasing in the order of the group. -/
theorem sortedGroups_chain : sortedGroups.Pairwise (fun A B => A.order < B.order) := by decide

/-- The last entry is the Monster, the first is `M11`. -/
theorem sortedGroups_last : sortedGroups.getLast? = some monster := by decide

theorem sortedGroups_head : sortedGroups.head? = some m11 := by decide

/-- Left to right on the triple-logarithmic axis is exactly increasing group order: the
picture's ordering is the ordering of the `|G|`. -/
theorem lll_sortedGroups_strictMono :
    ∀ A ∈ sortedGroups, ∀ B ∈ sortedGroups, A.order < B.order →
      lll (A.order : ℝ) < lll (B.order : ℝ) := by
  intro A hA B _ hAB
  have h7920 : 7920 ≤ A.order := (order_mem_Icc A (sortedGroups_subset A hA)).1
  refine lll_lt_lll ?_ (by exact_mod_cast hAB)
  have : (7920 : ℝ) ≤ (A.order : ℝ) := by exact_mod_cast h7920
  linarith [exp_one_lt_three]

/-- The fifteen dots of the first panel are the prime powers of `|M|`, and the number written
on each of them is the `p`-adic valuation of `|M|`. -/
theorem plotted_exponents_eq_factorization :
    ∀ pe ∈ monster.factors, monsterOrder.factorization pe.1 = pe.2 := by
  intro pe hpe
  rw [monsterOrder, exponent_eq_factorization monster_mem]
  revert pe hpe
  decide

/-! ## Geometry -/

private def W : Float := 1780.0
private def H : Float := 1860.0

/-! ### Panel 1: the exponents on the zeta Euler-factor graph -/

private def p1Left : Float := 190.0
private def p1Right : Float := 1640.0
private def p1Top : Float := 250.0
private def p1Bot : Float := 580.0

private def p1LogLo : Float := Float.log 1.85
private def p1LogHi : Float := Float.log 92.0

private def xOfPrimeF (x : Float) : Float :=
  p1Left + (Float.log x - p1LogLo) / (p1LogHi - p1LogLo) * (p1Right - p1Left)

/-- The vertical scale of panel 1: `log₁₀` of the excess of the local factor over `1`, which
spreads all fifteen primes out. -/
private def yOfFactor (v : Float) : Float :=
  let l := Float.log (v - 1.0) / Float.log 10.0
  p1Bot - (l + 4.2) / 3.85 * (p1Bot - p1Top)

private def zetaLocal (x : Float) : Float := 1.0 / (1.0 - x ^ (-2.0))

private def p1Curve : String :=
  let pts := (List.range 241).map fun i =>
    let t := Float.ofNat i / 240.0
    let x := Float.exp (Float.log 2.0 + t * (Float.log 90.0 - Float.log 2.0))
    (xOfPrimeF x, yOfFactor (zetaLocal x))
  polylineTag pts "#111827" 2.2

private def p1Dot (i : ℕ) (pe : ℕ × ℕ) : String :=
  let p := pe.1
  let e := pe.2
  let d := Float.ofNat (i % 3) * 36.0
  let x := xOfPrimeF (Float.ofNat p)
  let vz := eulerFloat p 2.0
  let yz := yOfFactor vz
  lineTag x p1Bot x yz "#e7ebf1" 1.0 "3 4" ++ "\n" ++
  circleTag x yz 7.0 (fiberColor p) "#111827" ++ "\n" ++
  textTag x (yz - 16.0) 20 (fiberColor p) "middle" "700" (toString e) ++ "\n" ++
  textTag x (p1Bot + 24.0 + d) 14 (fiberColor p) "middle" "700"
    (toString p ++ "^" ++ toString e) ++ "\n" ++
  textTag x (p1Bot + 40.0 + d) 10 "#9aa4b2" "middle" "400"
    ("defect 10^" ++ fmtFixed 1 (defectLog10 p e 2.0))

private def p1Grid : String :=
  String.intercalate "\n" ([(0.4 : Float), 1.0, 2.0, 3.0, 4.0].map fun k =>
    let y := p1Bot - (4.2 - k) / 3.85 * (p1Bot - p1Top)
    lineTag p1Left y p1Right y "#e7ebf1" 1.0 "" ++ "\n" ++
    textTag (p1Left - 12.0) (y + 4.0) 11 "#6b7280" "end" "500"
      ("10^-" ++ fmtFixed 1 k))

private def panel1 : String :=
  textTag 60.0 172.0 17 "#111827" "start" "700"
    "1.  the fifteen exponents of |M|, marked on the Euler-factor graph of \u03b6 at s = 2" ++
    "\n" ++
  textTag 60.0 196.0 13 "#4b5563" "start" "400"
    ("the curve is the zeta factor (1 - x\u207b\u00b2)\u207b\u00b9 - 1;  the big number over each dot is the" ++
     " exponent e of that prime in |M|, and below it the defect (1 - p\u207b\u00b2)\u207b\u00b9 - \u2211_{j \u2264 e} p\u207b\u00b2\u02b2" ++
     " left over by truncating there") ++ "\n" ++
  p1Grid ++ "\n" ++
  lineTag p1Left p1Bot p1Right p1Bot "#9aa4b2" 1.4 "" ++ "\n" ++
  p1Curve ++ "\n" ++
  String.intercalate "\n" (monster.factors.zipIdx.map fun (pe, i) => p1Dot i pe) ++ "\n" ++
  textTag p1Right (p1Top - 8.0) 12 "#4b5563" "end" "500"
    "vertical axis: (local factor of \u03b6 at s = 2) - 1,  logarithmic" ++ "\n" ++
  textTag (p1Left - 12.0) (p1Bot + 24.0) 12 "#4b5563" "end" "500" "p^e in |M|"

/-! ### Panel 2: the zeta graph in `s` -/

private def p2Left : Float := 170.0
private def p2Right : Float := 1640.0
private def p2Top : Float := 800.0
private def p2Bot : Float := 1120.0
private def sLo : Float := 1.25
private def sHi : Float := 6.0

private def xOfS (s : Float) : Float :=
  p2Left + (s - sLo) / (sHi - sLo) * (p2Right - p2Left)

private def yOfVal (v : Float) : Float :=
  p2Bot - (v - 0.9) / 5.6 * (p2Bot - p2Top)

private def curveOf (f : Float → Float) (stroke : String) (width : Float) : String :=
  polylineTag ((List.range 195).map fun i =>
    let s := sLo + Float.ofNat i * (sHi - sLo) / 194.0
    (xOfS s, yOfVal (f s))) stroke width

private def p2Grid : String :=
  String.intercalate "\n" ([(1.0 : Float), 2.0, 3.0, 4.0, 5.0, 6.0].map fun v =>
    lineTag p2Left (yOfVal v) p2Right (yOfVal v) "#e7ebf1" 1.0 "" ++ "\n" ++
    textTag (p2Left - 12.0) (yOfVal v + 4.0) 12 "#6b7280" "end" "500" (fmtFixed 1 v)) ++
  "\n" ++
  String.intercalate "\n" ([(1.5 : Float), 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0].map
    fun s =>
      lineTag (xOfS s) p2Bot (xOfS s) (p2Bot + 7.0) "#9aa4b2" 1.0 "" ++ "\n" ++
      textTag (xOfS s) (p2Bot + 22.0) 12 "#6b7280" "middle" "500" (fmtFixed 1 s))

private def p2Marks : String :=
  let s := 2.0
  let x := xOfS s
  lineTag x (yOfVal (monsterTruncF s)) x (yOfVal (zetaF s)) "#111827" 1.2 "4 4" ++ "\n" ++
  circleTag x (yOfVal (zetaF s)) 5.0 "#111827" "#ffffff" ++ "\n" ++
  circleTag x (yOfVal (monsterEulerF s)) 5.0 "#3b5bdb" "#ffffff" ++ "\n" ++
  circleTag x (yOfVal (monsterTruncF s)) 5.0 "#e6194b" "#ffffff" ++ "\n" ++
  textTag (x + 14.0) (yOfVal (zetaF s) - 30.0) 12 "#111827" "start" "600"
    ("\u03b6(2) = \u03c0\u00b2/6 = " ++ fmtFixed 6 (zetaF s)) ++ "\n" ++
  textTag (x + 14.0) (yOfVal (zetaF s) - 14.0) 12 "#3b5bdb" "start" "600"
    ("P(2) = " ++ fmtFixed 6 (monsterEulerF 2.0)) ++ "\n" ++
  textTag (x + 14.0) (yOfVal (zetaF s) + 2.0) 12 "#e6194b" "start" "600"
    ("D(2) = " ++ fmtFixed 6 (monsterTruncF 2.0))

private def panel2 : String :=
  textTag 60.0 730.0 17 "#111827" "start" "700"
    "2.  the zeta graph:  D(s) \u2264 P(s) \u2264 \u03b6(s)   for s &gt; 1" ++ "\n" ++
  textTag 60.0 754.0 13 "#4b5563" "start" "400"
    ("\u03b6(s) = \u2211 n\u207b\u02e2  (black);  P(s) = \u220f_{p \u2223 |M|} (1 - p\u207b\u02e2)\u207b\u00b9, the fifteen zeta factors (blue);" ++
     "  D(s) = \u2211_{d \u2223 |M|} d\u207b\u02e2, the same factors truncated at the exponents 46, 20, 9, 6, 2, 3, 1, \u2026 (red)") ++
    "\n" ++
  p2Grid ++ "\n" ++
  lineTag p2Left p2Bot p2Right p2Bot "#9aa4b2" 1.4 "" ++ "\n" ++
  curveOf zetaF "#111827" 2.4 ++ "\n" ++
  curveOf monsterEulerF "#3b5bdb" 2.0 ++ "\n" ++
  curveOf monsterTruncF "#e6194b" 1.8 ++ "\n" ++
  p2Marks ++ "\n" ++
  textTag ((p2Left + p2Right) / 2.0) (p2Bot + 44.0) 13 "#4b5563" "middle" "500" "s" ++ "\n" ++
  textTag p2Right (p2Top + 18.0) 12 "#4b5563" "end" "500"
    ("P and D are indistinguishable at this scale: keeping 46 powers of 2, 20 of 3, \u2026 loses" ++
     " almost nothing")

/-! ### Panel 3: the triple-logarithmic axis -/

private def p3Left : Float := 190.0
private def p3Right : Float := 1660.0
private def p3Y : Float := 1400.0
private def lllHi : Float := 1.65

private def xOfLll (v : Float) : Float := p3Left + v / lllHi * (p3Right - p3Left)

private def p3Ticks : String :=
  String.intercalate "\n" ((List.range 17).map fun i =>
    let v := Float.ofNat i / 10.0
    lineTag (xOfLll v) (p3Y - 8.0) (xOfLll v) (p3Y + 8.0) "#9aa4b2" 1.0 "" ++ "\n" ++
    textTag (xOfLll v) (p3Y + 24.0) 11 "#6b7280" "middle" "500" (fmtFixed 1 v))

private def p3PowerMark (i : ℕ) (pe : ℕ × ℕ) : String :=
  let v := lllPow pe.1 pe.2
  let x := xOfLll v
  let y := p3Y - 34.0 - Float.ofNat (i % 4) * 30.0
  lineTag x (p3Y - 6.0) x (y + 6.0) (fiberColor pe.1) 1.0 "3 3" ++ "\n" ++
  circleTag x (p3Y) 5.5 (fiberColor pe.1) "#ffffff" ++ "\n" ++
  textTag x (y - 2.0) 13 (fiberColor pe.1) "middle" "700"
    (toString pe.1 ++ "^" ++ toString pe.2) ++ "\n" ++
  textTag x (y + 12.0) 10 "#9aa4b2" "middle" "400" (fmtFixed 3 v)

private def p3GroupMark (i : ℕ) (G : Group) : String :=
  let v := lllGroup G
  let x := xOfLll v
  let y := p3Y + 44.0 + Float.ofNat (i % 5) * 25.0
  let isM := G.name == "M"
  lineTag x (p3Y + 6.0) x (y - 10.0) (if isM then "#e6194b" else "#c9d1dc") 1.0 "" ++ "\n" ++
  circleTag x p3Y (if isM then 7.0 else 4.0) (if isM then "#e6194b" else "#374151")
    "#ffffff" ++ "\n" ++
  textTag x y 12 (if isM then "#e6194b" else "#374151") "middle" (if isM then "700" else "600")
    G.name ++ "\n" ++
  textTag x (y + 12.0) 9 "#9aa4b2" "middle" "400" (fmtFixed 3 v)

private def panel3 : String :=
  textTag 60.0 1200.0 17 "#111827" "start" "700"
    "3.  the triple-logarithmic axis  log log log \u2014 the only scale on which the Monster fits" ++
    "\n" ++
  textTag 60.0 1224.0 13 "#4b5563" "start" "400"
    ("above the axis: the fifteen prime powers p^e of |M|, each labelled with its exponent;" ++
     "  below the axis: all twenty-six sporadic groups") ++ "\n" ++
  textTag 60.0 1246.0 13 "#4b5563" "start" "400"
    ("proved:  1.57 &lt; log log log |M| &lt; 1.58,   1.24 &lt; log log log 2\u2074\u2076 &lt; 1.25,  " ++
     " 0.72 &lt; log log log |M11| &lt; 0.79 \u2014 the whole family lives in a window of width 0.8") ++
    "\n" ++
  lineTag p3Left p3Y p3Right p3Y "#111827" 2.0 "" ++ "\n" ++
  p3Ticks ++ "\n" ++
  String.intercalate "\n" (monster.factors.zipIdx.map fun (pe, i) => p3PowerMark i pe) ++
    "\n" ++
  String.intercalate "\n" (sortedGroups.zipIdx.map fun (G, i) => p3GroupMark i G) ++ "\n" ++
  textTag (xOfLll (lllGroup monster)) (p3Y - 150.0) 13 "#e6194b" "middle" "700"
    ("|M| = 8.08 \u00b7 10\u2075\u00b3   \u21a6   " ++ fmtFixed 4 (lllGroup monster)) ++ "\n" ++
  lineTag (xOfLll (lllGroup monster)) (p3Y - 142.0) (xOfLll (lllGroup monster)) (p3Y - 8.0)
    "#e6194b" 1.2 "5 4" ++ "\n" ++
  textTag p3Right (p3Y - 14.0) 12 "#4b5563" "end" "500" "axis: log log log"

/-! ### Panel 4: the ordinary `log₁₀` axis, for contrast -/

private def p4Left : Float := 190.0
private def p4Right : Float := 1660.0
private def p4Y : Float := 1740.0

private def xOfLog10 (v : Float) : Float := p4Left + v / 56.0 * (p4Right - p4Left)

private def panel4 : String :=
  textTag 60.0 1630.0 17 "#111827" "start" "700"
    "4.  the ordinary log\u2081\u2080 axis, for contrast" ++ "\n" ++
  textTag 60.0 1654.0 13 "#4b5563" "start" "400"
    ("the same twenty-six groups: the number of digits of |G| runs from 4 to 54, and the" ++
     " prime powers of |M| (grey) all collapse into the first quarter") ++ "\n" ++
  lineTag p4Left p4Y p4Right p4Y "#111827" 1.6 "" ++ "\n" ++
  String.intercalate "\n" ((List.range 12).map fun i =>
    let v := Float.ofNat i * 5.0
    lineTag (xOfLog10 v) (p4Y - 6.0) (xOfLog10 v) (p4Y + 6.0) "#9aa4b2" 1.0 "" ++ "\n" ++
    textTag (xOfLog10 v) (p4Y + 22.0) 11 "#6b7280" "middle" "500"
      ("10^" ++ toString (i * 5))) ++ "\n" ++
  String.intercalate "\n" (monster.factors.map fun pe =>
    circleTag (xOfLog10 (Float.ofNat pe.2 * Float.log (Float.ofNat pe.1) / Float.log 10.0))
      (p4Y - 22.0) 4.0 "#c9d1dc" "#9aa4b2") ++ "\n" ++
  String.intercalate "\n" (sortedGroups.zipIdx.map fun (G, i) =>
    let x := xOfLog10 (log10Group G)
    let isM := G.name == "M"
    circleTag x p4Y (if isM then 7.0 else 4.0) (if isM then "#e6194b" else "#374151")
      "#ffffff" ++ "\n" ++
    (if isM || G.name == "M11" || G.name == "B" || G.name == "Fi24'" then
      textTag x (p4Y + 40.0 + Float.ofNat (i % 3) * 20.0) 12
        (if isM then "#e6194b" else "#374151") "middle" (if isM then "700" else "600") G.name
     else "")) ++
  "\n" ++
  textTag p4Right (p4Y - 24.0) 12 "#6b7280" "end" "500" "grey dots: the prime powers p^e of |M|"

/-! ## The picture -/

/-- The four-panel picture: every exponent of the Monster shown on the zeta graph, and the
triple-logarithmic scale that makes the Monster visible. -/
def zetaExponentSvg : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt W) ++ " " ++
    attr "height" (fmt H) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt W ++ " " ++ fmt H) ++ ">\n" ++
  rectTag 0.0 0.0 W H "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 58.0 24 "#111827" "start" "700"
    ("Every exponent of the Monster, on the zeta graph \u2014 and on the log log log scale") ++
    "\n" ++
  textTag 60.0 88.0 14 "#4b5563" "start" "400"
    ("|M| = 2\u2074\u2076 \u00b7 3\u00b2\u2070 \u00b7 5\u2079 \u00b7 7\u2076 \u00b7 11\u00b2 \u00b7 13\u00b3 \u00b7 17 \u00b7 19 \u00b7 23 \u00b7 29 \u00b7 31 \u00b7 41 \u00b7 47 \u00b7 59 \u00b7 71" ++
     " = 808017424794512875886459904961710757005754368000000000") ++ "\n" ++
  textTag 60.0 112.0 14 "#4b5563" "start" "400"
    ("log |M| = 46 log 2 + 20 log 3 + 9 log 5 + 6 log 7 + 2 log 11 + 3 log 13 + log 17 + \u2026 + log 71 = " ++
     fmtFixed 4 (logOrderF monster) ++
     ",   log log |M| = " ++ fmtFixed 4 (Float.log (logOrderF monster)) ++
     ",   log log log |M| = " ++ fmtFixed 4 (lllGroup monster)) ++ "\n" ++
  panel1 ++ "\n" ++
  panel2 ++ "\n" ++
  panel3 ++ "\n" ++
  panel4 ++
  "\n</svg>\n"

/-! ## The table, as CSV -/

/-- The twenty-six groups on the three logarithmic levels. -/
def lllCsv : String :=
  "group,digits,exponent_of_2,log,loglog,logloglog,log10\n" ++
  String.intercalate "\n" (sortedGroups.map fun G =>
    String.intercalate ","
      [G.name, toString (orderDigits G), toString (G.exponent 2),
        fmtFixed 4 (logOrderF G), fmtFixed 4 (Float.log (logOrderF G)),
        fmtFixed 4 (lllGroup G), fmtFixed 4 (log10Group G)]) ++ "\n" ++
  "\n" ++
  "prime_power,exponent,log,loglog,logloglog\n" ++
  String.intercalate "\n" (monster.factors.map fun pe =>
    String.intercalate ","
      [toString pe.1 ++ "^" ++ toString pe.2, toString pe.2,
        fmtFixed 4 (Float.ofNat pe.2 * Float.log (Float.ofNat pe.1)),
        fmtFixed 4 (Float.log (Float.ofNat pe.2 * Float.log (Float.ofNat pe.1))),
        fmtFixed 4 (lllPow pe.1 pe.2)]) ++ "\n"

end ZetaExponentSvg

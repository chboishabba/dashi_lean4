/-
# The picture: ζ as moonshine

`visualization/zeta-moonshine.svg` is drawn here.  It has three panels:

1. **the dictionary** between monstrous moonshine (the Monster `M` and `J = j - 744`) and the
   ζ-moonshine of `RequestProject/ZetaMoonshine.lean` (the cyclic group `ZMod 24` and `ζ`),
   line by line, with the name of the proved statement behind each line;
2. **the isotypic decomposition of `ζ(2)`** — one bar for each of the twenty-four
   irreducible representations `ρ_a` of the moonshine group, of height
   `∑_{n ≡ a (24)} n^{-2}`; the bars add up to `ζ(2) = π²/6`
   (`ZetaMoonshine.riemannZeta_eq_sum_isotypic`, truncated here at `n ≤ 4096`), and the four
   classes `2, 4, 8, 16` that carry the whole prime-power fiber of `2`
   (`ZetaMoonshine.two_pow_mod24_mem`) are marked in the fiber colour of `2`, the class of the
   Monster's `2^46` among them;
3. **the twenty-four McKay–Thompson series at `s = 2`** in the complex plane:
   `T_j(2) = ∑_n e^{2πijn/24} n^{-2} = ∑_a e^{2πija/24} · (a-th isotypic value)`
   (`ZetaMoonshine.mtSeries_eq_sum_isotypic`), with `T_0(2) = ζ(2)` far to the right.

Only floating-point geometry and string manipulation live in this file; every mathematical
claim written in the picture is proved in `RequestProject/ZetaMoonshine.lean`.
-/
import RequestProject.ZetaMoonshine
import RequestProject.SporadicSvg

namespace ZetaMoonshineSvg

open SporadicSvg

set_option autoImplicit false
set_option maxRecDepth 40000

/-! ## What the picture claims, proved -/

/-- The powers of `2` occupy only four of the twenty-four residue classes drawn in panel 2.
This is the `Nat`-level form of `ZetaMoonshine.two_pow_mod24_mem`, which is what the
rendering code below tests. -/
theorem two_pow_mod24_nat (k : ℕ) (hk : 1 ≤ k) :
    2 ^ k % 24 = 2 ∨ 2 ^ k % 24 = 4 ∨ 2 ^ k % 24 = 8 ∨ 2 ^ k % 24 = 16 := by
  induction k with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with h | h
    · interval_cases n
      · norm_num
    · have hstep : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
      have := ih h
      omega

/-! ## The numbers plotted -/

/-- The truncation level of every series drawn. -/
def K : ℕ := 4096

/-- The modulus, i.e. the order of the moonshine group. -/
def N : ℕ := 24

/-- `∑_{n ≤ K, n ≡ a (24)} n^{-s}`: the `a`-isotypic component of the ζ-moonshine module,
truncated at `K`. -/
def isoF (a : ℕ) (s : Float) : Float :=
  ((List.range K).drop 1).foldl
    (fun acc n => if n % N == a then acc + (Float.ofNat n) ^ (-s) else acc) 0.0

/-- The twenty-four isotypic values at `s = 2`. -/
def isoVals : List Float := (List.range N).map fun a => isoF a 2.0

/-- Their sum, which is the truncated `ζ(2)`. -/
def isoTotal : Float := isoVals.foldl (· + ·) 0.0

def twoPi : Float := 6.283185307179586

/-- `T_j(2) = ∑_a e^{2πija/24} · isoF a 2`, the `j`-th McKay–Thompson series at `s = 2`,
assembled from the isotypic components exactly as in
`ZetaMoonshine.mtSeries_eq_sum_isotypic`. -/
def mtF (j : ℕ) : Float × Float :=
  (List.range N).foldl
    (fun acc a =>
      let ang := twoPi * Float.ofNat (j * a % N) / Float.ofNat N
      let v := isoF a 2.0
      (acc.1 + v * Float.cos ang, acc.2 + v * Float.sin ang))
    (0.0, 0.0)

/-- The residue classes carrying the prime-power fiber of `2`. -/
def twoFiberResidues : List ℕ := [2, 4, 8, 16]

/-- The colour of the fiber of `2` in the rest of the project. -/
def twoColor : String := PrimeFibers.fiberColor 2

/-! ## Geometry -/

private def W : Float := 1760.0
private def H : Float := 1560.0

/-! ### Panel 1: the dictionary -/

private def tabTop : Float := 185.0
private def tabRow : Float := 32.0
private def colL : Float := 70.0
private def colM : Float := 430.0
private def colR : Float := 1080.0

private def rows : List (String × String × String) :=
  [("group",
      "the Monster M,  |M| = 8.08 \u00b7 10\u2075\u00b3",
      "the cyclic group Z/24,  order 24"),
   ("graded module",
      "V\u266e = \u2295 V\u2099,  dim V\u2099 = c(n)",
      "V = \u2295_{n \u2265 1} V\u2099,  dim V\u2099 = 1"),
   ("grading variable",
      "q\u207f,  q = e\u00b2\u03c0\u2071\u1d57",
      "n\u207b\u02e2  (Dirichlet series in place of q-expansions)"),
   ("moonshine function",
      "J(\u03c4) = j(\u03c4) - 744 = \u2211 c(n) q\u207f",
      "\u03b6(s) = \u2211 n\u207b\u02e2"),
   ("McKay\u2013Thompson series",
      "T_g(\u03c4) = \u2211 tr(g | V\u2099) q\u207f",
      "T_j(s) = \u2211 tr(j | V\u2099) n\u207b\u02e2 = \u2211 e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 n\u207b\u02e2      [mtSeries]"),
   ("the identity element",
      "T\u2081 = J  (the moonshine function itself)",
      "T\u2080 = \u03b6      [mtSeries_zero_eq_riemannZeta]"),
   ("how many series",
      "194 conjugacy classes, 172 distinct T_g",
      "24 elements, 24 distinct T_j      [gradedTrace_injective]"),
   ("graded pieces",
      "c(1) = 196884 = 1 + 196883  (sums of irrep dims)",
      "V\u2099 = \u03c1_{n mod 24},  dim V\u2099 = 1      [gradedTrace_eq_irrep]"),
   ("multiplicities",
      "mult of an irrep in V\u2099: non-negative integers",
      "mult(\u03c1_a, V\u2099) = 1 if n \u2261 a (24), else 0      [mult_eq_ite]"),
   ("positivity",
      "every c(n) a non-negative combination of dims",
      "\u2211_a mult(\u03c1_a, V\u2099) = dim V\u2099 = 1      [sum_mult]"),
   ("isotypic decomposition",
      "V\u266e = \u2295 (isotypic pieces for M)",
      "\u03b6(s) = \u2211_{a mod 24} \u2211_{n \u2261 a} n\u207b\u02e2      [riemannZeta_eq_sum_isotypic]"),
   ("character twists",
      "hauptmoduln of the groups \u0393\u2080(N)+e",
      "Dirichlet L-functions L(s, \u03c7)      [sum_dirichlet_smul_isotypic]"),
   ("recovering the pieces",
      "Thompson series determine the module",
      "\u2211_{n \u2261 a} n\u207b\u02e2 = \u03c6(24)\u207b\u00b9 \u2211_\u03c7 \u03c7(a\u207b\u00b9) L(s, \u03c7)      [isotypic_eq_sum_LSeries]"),
   ("self-similarity",
      "replication formulas for the T_g",
      "\u2211_{24 | n} n\u207b\u02e2 = 24\u207b\u02e2 \u03b6(s)      [isotypic_zero_eq]"),
   ("the group of order 2",
      "smaller moonshine groups have their own T_g",
      "T\u2081(s) = \u2211 (-1)\u207f n\u207b\u02e2 = (2\u00b9\u207b\u02e2 - 1) \u03b6(s), the Dirichlet eta      [mtSeries_one_two]"),
   ("the prime 2",
      "2\u2074\u2076 is the largest prime power of |M|",
      "2\u2074\u2076 lies in the isotypic component a = 16      [mult_monster_two_pow]")]

private def tableRow (i : ℕ) (r : String × String × String) : String :=
  let y := tabTop + Float.ofNat i * tabRow
  (if i % 2 == 1 then rectTag (colL - 14.0) (y - 20.0) 1640.0 28.0 "#f4f6fa" "" 1.0 ++ "\n"
   else "") ++
  textTag colL y 13 "#6b7280" "start" "600" r.1 ++ "\n" ++
  textTag colM y 13 "#1f2937" "start" "400" r.2.1 ++ "\n" ++
  textTag colR y 13 "#7f1d3f" "start" "400" r.2.2

private def panel1 : String :=
  textTag 60.0 156.0 17 "#111827" "start" "700"
    "1.  the dictionary:  monstrous moonshine  \u2194  \u03b6-moonshine" ++ "\n" ++
  textTag colM (tabTop - 26.0) 14 "#111827" "start" "700" "Monster M  /  j-invariant" ++ "\n" ++
  textTag colR (tabTop - 26.0) 14 "#7f1d3f" "start" "700"
    "Z/24  /  \u03b6  (this project, all statements proved)" ++ "\n" ++
  String.intercalate "\n" (rows.zipIdx.map fun (r, i) => tableRow i r)

/-! ### Panel 2: the isotypic decomposition of ζ(2) -/

private def p2Left : Float := 130.0
private def p2Right : Float := 1660.0
private def p2Bot : Float := 1090.0
private def p2Top : Float := 800.0

private def barW : Float := 44.0

private def yOfVal (v : Float) : Float :=
  p2Bot - (v / 1.05) * (p2Bot - p2Top)

private def bar (a : ℕ) : String :=
  let v := isoF a 2.0
  let x := p2Left + Float.ofNat a * ((p2Right - p2Left) / Float.ofNat N) + 8.0
  let isTwo := twoFiberResidues.contains a
  let col := if isTwo then twoColor else "#3b5bdb"
  let h := if v > 1.05 then p2Bot - p2Top else p2Bot - yOfVal v
  let y := p2Bot - h
  rectTag x y barW h col "" (if isTwo then 0.95 else 0.75) ++ "\n" ++
  textTag (x + barW / 2.0) (y - 8.0) 12 col "middle" "700" (fmtFixed 4 v) ++ "\n" ++
  textTag (x + barW / 2.0) (p2Bot + 20.0) 14 "#111827" "middle" "700" (toString a) ++
  (if isTwo then "\n" ++ textTag (x + barW / 2.0) (p2Bot + 38.0) 11 twoColor "middle" "600"
      (if a == 16 then "2\u2074\u2076" else "2\u1d4f") else "")

private def panel2 : String :=
  textTag 60.0 700.0 17 "#111827" "start" "700"
    "2.  \u03b6(2) split into the twenty-four isotypic components of the moonshine module" ++ "\n" ++
  textTag 60.0 724.0 13 "#4b5563" "start" "400"
    ("bar a = \u2211_{n \u2264 4096, n \u2261 a (mod 24)} n\u207b\u00b2 ;  the twenty-four bars add up to " ++
     fmtFixed 6 isoTotal ++ ", the truncation of \u03b6(2) = \u03c0\u00b2/6 = 1.644934;  the class a = 1 " ++
     "carries the term n = 1") ++ "\n" ++
  textTag 60.0 746.0 13 "#4b5563" "start" "400"
    ("the four red classes 2, 4, 8, 16 are exactly the ones met by the prime-power fiber " ++
     "of 2, and the Monster's 2\u2074\u2076 lies in the class a = 16") ++ "\n" ++
  lineTag p2Left p2Bot p2Right p2Bot "#9aa4b2" 1.4 "" ++ "\n" ++
  String.intercalate "\n" ((List.range N).map bar) ++ "\n" ++
  textTag (p2Left - 10.0) (yOfVal 1.0) 12 "#6b7280" "end" "500" "1.0" ++ "\n" ++
  lineTag p2Left (yOfVal 1.0) p2Right (yOfVal 1.0) "#e7ebf1" 1.0 "4 5" ++ "\n" ++
  textTag (p2Left - 10.0) (p2Bot + 20.0) 12 "#4b5563" "end" "600" "a ="

/-! ### Panel 3: the McKay–Thompson series in the complex plane -/

private def p3Cx : Float := 700.0
private def p3Cy : Float := 1368.0
private def p3Scale : Float := 150.0

private def xOfRe (u : Float) : Float := p3Cx + u * p3Scale
private def yOfIm (v : Float) : Float := p3Cy - v * p3Scale

private def mtDot (j : ℕ) : String :=
  let z := mtF j
  let x := xOfRe z.1
  let y := yOfIm z.2
  circleTag x y 6.0 (if j == 0 then "#111827" else "#3b5bdb") "#ffffff" ++ "\n" ++
  textTag (x + 10.0) (y - 8.0) 12 (if j == 0 then "#111827" else "#4b5563") "start" "600"
    ("T" ++ toString j)

private def panel3 : String :=
  textTag 60.0 1170.0 17 "#111827" "start" "700"
    "3.  the twenty-four McKay\u2013Thompson series at s = 2, in the complex plane" ++ "\n" ++
  textTag 60.0 1194.0 13 "#4b5563" "start" "400"
    ("T_j(2) = \u2211_n e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 n\u207b\u00b2, assembled from the bars of panel 2 by " ++
     "T_j = \u2211_a e\u00b2\u03c0\u2071\u02b2\u1d43\u141f\u00b2\u2074 \u00b7 (bar a);  the identity gives T\u2080(2) = \u03b6(2) = " ++
     fmtFixed 6 isoTotal) ++ "\n" ++
  lineTag (xOfRe (-0.6)) p3Cy (xOfRe 1.9) p3Cy "#cbd5e1" 1.2 "" ++ "\n" ++
  lineTag p3Cx (yOfIm (-0.75)) p3Cx (yOfIm 0.75) "#cbd5e1" 1.2 "" ++ "\n" ++
  textTag (xOfRe 1.9) (p3Cy + 18.0) 12 "#6b7280" "end" "500" "Re" ++ "\n" ++
  textTag (p3Cx + 8.0) (yOfIm 0.75) 12 "#6b7280" "start" "500" "Im" ++ "\n" ++
  circleTag (xOfRe 0.0) (yOfIm 0.0) 3.0 "#9aa4b2" "#9aa4b2" ++ "\n" ++
  String.intercalate "\n" ((List.range N).map mtDot)

/-! ## The picture -/

/-- The three-panel picture: ζ read as the moonshine function of the cyclic group of
order 24. -/
def zetaMoonshineSvg : String :=
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt W) ++ " " ++
    attr "height" (fmt H) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt W ++ " " ++ fmt H) ++ ">\n" ++
  rectTag 0.0 0.0 W H "#ffffff" "" 1.0 ++ "\n" ++
  textTag 60.0 58.0 24 "#111827" "start" "700"
    "If \u03b6 were moonshine:  the zeta function as the graded dimension of a module" ++ "\n" ++
  textTag 60.0 88.0 14 "#4b5563" "start" "400"
    ("monstrous moonshine makes j - 744 the graded dimension of a module for the Monster;  " ++
     "here \u03b6(s) = \u2211 n\u207b\u02e2 is the graded dimension of the module with dim V\u2099 = 1 for every n,") ++
    "\n" ++
  textTag 60.0 110.0 14 "#4b5563" "start" "400"
    ("acted on by the cyclic group Z/24 through j \u00b7 v = e\u00b2\u03c0\u2071\u02b2\u207f\u141f\u00b2\u2074 v on V\u2099;  its " ++
     "McKay\u2013Thompson series are the twisted series T_j, and its character twists are the " ++
     "Dirichlet L-functions") ++ "\n" ++
  panel1 ++ "\n" ++
  panel2 ++ "\n" ++
  panel3 ++
  "\n</svg>\n"

/-! ## The table, as CSV -/

/-- The isotypic components of `ζ(2)` and the McKay–Thompson values at `s = 2`. -/
def zetaMoonshineCsv : String :=
  "residue_a,isotypic_partial_sum_at_s2,in_fiber_of_2\n" ++
  String.intercalate "\n" ((List.range N).map fun a =>
    String.intercalate ","
      [toString a, fmtFixed 6 (isoF a 2.0),
        if twoFiberResidues.contains a then "yes" else "no"]) ++ "\n" ++
  "total," ++ fmtFixed 6 isoTotal ++ ",\n\n" ++
  "group_element_j,Re T_j(2),Im T_j(2)\n" ++
  String.intercalate "\n" ((List.range N).map fun j =>
    let z := mtF j
    String.intercalate "," [toString j, fmtFixed 6 z.1, fmtFixed 6 z.2]) ++ "\n"

end ZetaMoonshineSvg

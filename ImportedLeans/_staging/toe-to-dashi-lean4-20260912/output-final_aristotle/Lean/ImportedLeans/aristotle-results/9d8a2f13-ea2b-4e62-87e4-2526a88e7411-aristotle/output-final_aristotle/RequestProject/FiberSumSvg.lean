/-
# Rendering the fiber sums

Two panels, drawn from the same data that is evaluated exactly in
`RequestProject/FiberSumsMulti.lean`, `RequestProject/FiberSumsSingle.lean` and
`RequestProject/FiberSumTable.lean`:

* a bar chart of the absolute fiber sums `∑_k |τ(p^k)|/p^{11k/2}` for the first twenty primes,
  each bar in that fiber's colour and annotated with its value and its number of terms;
* the profiles `|τ(p^k)|/p^{11k/2}` plotted against `n = p^k ≤ 256`, with the multi-power fibers
  joined up and the area under them filled.

Only the floating-point coordinates and the string manipulation live here; the numbers
themselves are the ones proved correct (to six decimal places) in the files above.  The picture
is written to `visualization/fiber-abs-sums.svg` by `scripts/GenerateSvg.lean`, which also
writes the table `visualization/prime_fiber_sums.csv`.
-/
import RequestProject.FiberSumTable

namespace FiberSums

open PrimeFibers RamanujanTau

/-! ## The data, in floating point -/

/-- The Deligne-normalised coefficient `τ(n)/n^{11/2}`, in floating point. -/
def normFloat (n : ℕ) : Float := Float.ofInt (tau n) / (Float.ofNat n) ^ (5.5 : Float)

/-- Its absolute value `|τ(n)|/n^{11/2}`. -/
def absNormFloat (n : ℕ) : Float := (normFloat n).abs

/-- The powers `p, p², …` of `p` that are `≤ 256`. -/
def fiberPowers (p : ℕ) : List ℕ :=
  (List.range 9).filterMap fun k => if 1 ≤ k && p ^ k ≤ 256 then some (p ^ k) else none

/-- The picture is faithful: the points plotted for `p` are exactly the prime-power fiber of
`p` inside the displayed range. -/
theorem fiberPowers_toFinset {p : ℕ} (hp : 2 ≤ p) :
    (fiberPowers p).toFinset = primePowerFiber p 256 := by
  ext n
  simp only [List.mem_toFinset, fiberPowers, List.mem_filterMap, List.mem_range,
    mem_primePowerFiber]
  constructor
  · rintro ⟨k, -, hk2⟩
    by_cases h : 1 ≤ k && p ^ k ≤ 256
    · rw [if_pos h] at hk2
      simp only [Option.some.injEq] at hk2
      subst hk2
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨⟨Nat.pow_pos (by omega), h.2⟩, k, h.1, rfl⟩
    · rw [if_neg h] at hk2
      exact absurd hk2 (by simp)
  · rintro ⟨⟨-, hle⟩, k, hk, rfl⟩
    have hk9 : k < 9 := by
      by_contra hc
      have h1 : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp _
      have h2 : 2 ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    exact ⟨k, hk9, by rw [if_pos (by simp [hle]; omega)]⟩

/-- The signed fiber sum, in floating point. -/
def signedSumFloat (p : ℕ) : Float :=
  ((fiberPowers p).map normFloat).foldl (· + ·) 0.0

/-- The absolute fiber sum, in floating point. -/
def absSumFloat (p : ℕ) : Float :=
  ((fiberPowers p).map absNormFloat).foldl (· + ·) 0.0

/-! ## Formatting -/

private def padLeft (n : ℕ) (c : Char) (s : String) : String :=
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

private def fmt (x : Float) : String := toString x

/-! ## SVG helpers -/

private def attr (k v : String) : String := k ++ "=\"" ++ v ++ "\""

private def rectTag (x y w h : Float) (fill stroke : String) : String :=
  "  <rect " ++ attr "x" (fmt x) ++ " " ++ attr "y" (fmt y) ++ " " ++
    attr "width" (fmt w) ++ " " ++ attr "height" (fmt h) ++ " " ++ attr "fill" fill ++
    (if stroke = "" then "" else " " ++ attr "stroke" stroke ++ " " ++
      attr "stroke-width" "1") ++ "/>"

private def lineTag (x1 y1 x2 y2 : Float) (stroke : String) (width : Float)
    (dash : String) : String :=
  "  <line " ++ attr "x1" (fmt x1) ++ " " ++ attr "y1" (fmt y1) ++ " " ++
    attr "x2" (fmt x2) ++ " " ++ attr "y2" (fmt y2) ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt width) ++
    (if dash = "" then "" else " " ++ attr "stroke-dasharray" dash) ++ "/>"

private def circleTag (cx cy r : Float) (fill stroke : String) : String :=
  "  <circle " ++ attr "cx" (fmt cx) ++ " " ++ attr "cy" (fmt cy) ++ " " ++
    attr "r" (fmt r) ++ " " ++ attr "fill" fill ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" "1.2" ++ "/>"

private def textTag (x y : Float) (size : ℕ) (fill anchor weight body : String) : String :=
  "  <text " ++ attr "x" (fmt x) ++ " " ++ attr "y" (fmt y) ++ " " ++
    attr "font-family" "ui-monospace, SFMono-Regular, Menlo, monospace" ++ " " ++
    attr "font-size" (toString size) ++ " " ++ attr "font-weight" weight ++ " " ++
    attr "fill" fill ++ " " ++ attr "text-anchor" anchor ++ ">" ++ body ++ "</text>"

private def polylineTag (pts : List (Float × Float)) (stroke : String) (width : Float) : String :=
  "  <polyline " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++
    " " ++ attr "fill" "none" ++ " " ++ attr "stroke" stroke ++ " " ++
    attr "stroke-width" (fmt width) ++ "/>"

private def polygonTag (pts : List (Float × Float)) (fill : String) : String :=
  "  <polygon " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++
    " " ++ attr "fill" fill ++ " " ++ attr "opacity" "0.25" ++ "/>"

/-! ## Panel 1: the bar chart of absolute fiber sums -/

private def barLeft : Float := 110.0
private def barRight : Float := 1540.0
private def barBase : Float := 500.0
private def barTop : Float := 130.0
/-- Vertical pixels per unit of absolute fiber sum (the largest is `≈ 5.39`). -/
private def barScale : Float := 62.0

private def barSlot : Float := (barRight - barLeft) / 20.0

private def barSvg (i : ℕ) (p : ℕ) : String :=
  let v := absSumFloat p
  let x := barLeft + Float.ofNat i * barSlot + barSlot * 0.18
  let w := barSlot * 0.64
  let h := v * barScale
  let y := barBase - h
  let cnt := (fiberPowers p).length
  rectTag x y w h (fiberColor p) "#111827" ++ "\n" ++
    textTag (x + w / 2.0) (y - 22.0) 12 "#111827" "middle" "700" (fmtFixed 2 v) ++ "\n" ++
    textTag (x + w / 2.0) (y - 8.0) 10 "#6b7280" "middle" "500"
      ("(" ++ toString cnt ++ (if cnt = 1 then " term)" else " terms)")) ++ "\n" ++
    textTag (x + w / 2.0) (barBase + 18.0) 12 "#374151" "middle" "700" ("p=" ++ toString p)

private def barGridSvg : String :=
  String.intercalate "\n" ([(1.0 : Float), 2.0, 3.0, 4.0, 5.0].map fun v =>
    lineTag barLeft (barBase - v * barScale) barRight (barBase - v * barScale) "#e7ebf1" 1.0
      "4 4" ++ "\n" ++
      textTag (barLeft - 12.0) (barBase - v * barScale + 4.0) 12 "#8a94a6" "end" "400"
        (fmtFixed 1 v))

private def panel1Svg : String :=
  barGridSvg ++ "\n" ++
    lineTag barLeft barBase barRight barBase "#9aa4b2" 1.4 "" ++ "\n" ++
    String.intercalate "\n" ((primeList.zipIdx).map fun (p, i) => barSvg i p) ++ "\n" ++
    textTag barLeft (barTop - 24.0) 14 "#111827" "start" "600"
      "\u2211\u2096 |\u03c4(p\u1d4f)| / p^(11k/2)   (absolute mass of each prime fiber, n \u2264 256)"

/-! ## Panel 2: the fiber profiles -/

private def profLeft : Float := 110.0
private def profRight : Float := 1540.0
private def profBase : Float := 1010.0
private def profTop : Float := 640.0
/-- Vertical pixels per unit of `|τ(n)|/n^{11/2}` (all values are `< 2`). -/
private def profScale : Float := 165.0

private def xOfN (n : ℕ) : Float :=
  profLeft + Float.ofNat n * (profRight - profLeft) / 260.0

private def yOfVal (v : Float) : Float := profBase - v * profScale

private def profGridSvg : String :=
  String.intercalate "\n" ([(0.5 : Float), 1.0, 1.5, 2.0].map fun v =>
    lineTag profLeft (yOfVal v) profRight (yOfVal v) "#e7ebf1" 1.0 "4 4" ++ "\n" ++
      textTag (profLeft - 12.0) (yOfVal v + 4.0) 12 "#8a94a6" "end" "400" (fmtFixed 1 v)) ++
    "\n" ++
    String.intercalate "\n" ([0, 32, 64, 96, 128, 160, 192, 224, 256].map fun n =>
      lineTag (xOfN n) profTop (xOfN n) profBase "#f1f4f8" 1.0 "" ++ "\n" ++
        textTag (xOfN n) (profBase + 20.0) 12 "#8a94a6" "middle" "400" (toString n)) ++ "\n" ++
    lineTag profLeft profBase profRight profBase "#9aa4b2" 1.4 ""

private def fiberProfileSvg (p : ℕ) : String :=
  let ns := fiberPowers p
  let pts := ns.map fun n => (xOfN n, yOfVal (absNormFloat n))
  let c := fiberColor p
  match ns with
  | [] => ""
  | [n] =>
      lineTag (xOfN n) profBase (xOfN n) (yOfVal (absNormFloat n)) c 1.6 "" ++ "\n" ++
        circleTag (xOfN n) (yOfVal (absNormFloat n)) 4.0 c "#ffffff" ++ "\n" ++
        textTag (xOfN n) (yOfVal (absNormFloat n) - 10.0) 10 "#374151" "middle" "600"
          (toString n)
  | _ =>
      let area := (xOfN ns.head!, profBase) :: pts ++ [(xOfN ns.getLast!, profBase)]
      polygonTag area c ++ "\n" ++ polylineTag pts c 2.0 ++ "\n" ++
        String.intercalate "\n" (ns.map fun n =>
          circleTag (xOfN n) (yOfVal (absNormFloat n)) 4.5 c "#ffffff" ++ "\n" ++
            textTag (xOfN n) (yOfVal (absNormFloat n) - 10.0) 10 "#374151" "middle" "600"
              (toString n))

private def panel2Svg : String :=
  profGridSvg ++ "\n" ++
    String.intercalate "\n" (primeList.map fiberProfileSvg) ++ "\n" ++
    textTag profLeft (profTop - 24.0) 14 "#111827" "start" "600"
      "|\u03c4(p\u1d4f)| / p^(11k/2)   plotted at n = p\u1d4f \u2264 256, with the area under each multi-power fiber filled" ++
    "\n" ++
    textTag ((profLeft + profRight) / 2.0) (profBase + 44.0) 13 "#4b5563" "middle" "500"
      "n = p^k"

/-! ## The document -/

private def legendEntry (x y : Float) (color label : String) : String :=
  circleTag (x + 7.0) (y + 7.0) 5.0 color "#ffffff" ++ "\n" ++
    textTag (x + 20.0) (y + 12.0) 12 "#374151" "start" "500" label

private def legendSvg : String :=
  String.intercalate "\n"
    ((primeList.zipIdx).map fun (p, i) =>
      legendEntry (profLeft + Float.ofNat (i % 7) * 200.0)
        (profBase + 66.0 + Float.ofNat (i / 7) * 26.0) (fiberColor p)
        ("p=" ++ toString p ++ "  (" ++ toString (fiberPowers p).length ++
          (if (fiberPowers p).length = 1 then " term)" else " terms)")))

/-- The two-panel picture of the fiber sums. -/
def fiberSumsSvg : String :=
  let width : Float := 1620.0
  let height : Float := 1160.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" ++ "\n" ++
  textTag 110.0 52.0 22 "#111827" "start" "700"
    "Absolute mass of the Deligne-normalised coefficients of \u0394 = \u03b7\u00b2\u2074 along each prime fiber" ++
    "\n" ++
  textTag 110.0 78.0 14 "#4b5563" "start" "400"
    ("fibers of the first twenty primes, n = p^k \u2264 256; the values are the ones proved to six" ++
      " decimal places in RequestProject/FiberSums*.lean") ++ "\n" ++
  panel1Svg ++ "\n" ++ panel2Svg ++ "\n" ++ legendSvg ++ "\n</svg>\n"

/-! ## The table, as CSV -/

/-- The summary table: prime, number of powers, the powers, signed sum, absolute sum. -/
def fiberSumsCsv : String :=
  "prime,power_count,powers_n,signed_sum_deligne,absolute_sum_deligne\n" ++
  String.intercalate "\n" (primeList.map fun p =>
    let ns := fiberPowers p
    String.intercalate "," [toString p, toString ns.length,
      "\"" ++ String.intercalate " " (ns.map toString) ++ "\"",
      fmtFixed 6 (signedSumFloat p), fmtFixed 6 (absSumFloat p)]) ++ "\n"

end FiberSums

/-
# Plotting the zeta function of the modular form

Renders `visualization/modular-zeta.svg`, a three-panel picture of the Dirichlet series
(the "zeta function") of the modular discriminant `Δ = η²⁴ = ∑ τ(n) qⁿ`, in the
Deligne-normalised form

```
L(Δ, s) = ∑_{n ≥ 1} (τ(n)/n^{11/2}) n^{-s},
```

drawn against the Riemann zeta function:

1. **the two zeta functions in `s`** — the partial sums `ζ_N(s) = ∑_{n ≤ N} n^{-s}` and
   `L_N(Δ, s) = ∑_{n ≤ N} (τ(n)/n^{11/2}) n^{-s}` for `N = 256`, together with the Deligne
   envelope `ζ_N(s)²` and the proved band `|L_N(Δ,s) - 1| ≤ ζ_N(s)² - 1` shaded around `1`
   (`ModularZeta.abs_deltaLPartial_sub_one_le`);
2. **the local factors at `s = 2`** — for each of the first twenty primes, the *quadratic*
   modular local factor `(1 - y_p p^{-s} + p^{-2s})⁻¹` (in that prime's fiber colour) against
   zeta's *linear* factor `(1 - p^{-s})⁻¹`, with the proved envelopes `(1 - p^{-s})⁻²` and
   `(1 + p^{-s})⁻²` (`ModularZeta.modularLocalFactor_le_eulerFactor_sq`,
   `ModularZeta.eulerFactor_sq_inv_le_modularLocalFactor`);
3. **the two series accumulating at `s = 2`** — the running partial sums
   `∑_{n ≤ m} n^{-2} → ζ(2) = π²/6` and `∑_{n ≤ m} (τ(n)/n^{11/2}) n^{-2} → L(Δ, 2)`, with the
   prime powers marked in their fiber colours, and the total of the Deligne envelope
   `∑ d(n) n^{-2}` recorded (`ModularZeta.abs_deltaLPartial_le_divisorPartial`).

Only floating-point coordinates and string manipulation live here; the mathematics of the
picture is in `RequestProject/ModularZeta.lean`.  A companion table is written to
`visualization/modular_zeta.csv`.
-/
import RequestProject.ModularZeta
import RequestProject.SporadicSvg
import RequestProject.ModularSvg

namespace ModularZetaSvg

open PrimeFibers RamanujanTau SporadicSvg

set_option autoImplicit false

/-! ## The plotted data (floating point) -/

/-- The displayed range `n ≤ 256`. -/
def plotN : ℕ := 256

/-- The Deligne-normalised coefficients `τ(n)/n^{11/2}`, precomputed. -/
def normTauArr : Array Float :=
  (Array.range (plotN + 1)).map fun n => if n = 0 then 0.0 else ModularGraph.plotValue n

def normTauF (n : ℕ) : Float := normTauArr[n]!

/-- The partial sum `ζ_N(s) = ∑_{n ≤ N} n^{-s}`. -/
def zetaPF (s : Float) : Float :=
  (List.range plotN).foldl (fun a i => a + (Float.ofNat (i + 1)) ^ (-s)) 0.0

/-- The partial sum `L_N(Δ, s) = ∑_{n ≤ N} (τ(n)/n^{11/2}) n^{-s}`. -/
def deltaLF (s : Float) : Float :=
  (List.range plotN).foldl (fun a i => a + normTauF (i + 1) * (Float.ofNat (i + 1)) ^ (-s)) 0.0

/-- The number of divisors of `n`. -/
def divisorCount (n : ℕ) : ℕ := n.divisors.card

/-- The reciprocal of the modular local factor at `p`: `1 - y_p p^{-s} + p^{-2s}`. -/
def modularLocalInvF (p : ℕ) (s : Float) : Float :=
  let x := (Float.ofNat p) ^ (-s)
  1.0 - normTauF p * x + x * x

/-- The modular local factor `(1 - y_p p^{-s} + p^{-2s})⁻¹`. -/
def modularLocalF (p : ℕ) (s : Float) : Float := 1.0 / modularLocalInvF p s

/-- Zeta's local factor `(1 - p^{-s})⁻¹`. -/
def eulerF (p : ℕ) (s : Float) : Float := 1.0 / (1.0 - (Float.ofNat p) ^ (-s))

/-- The proved upper envelope `(1 - p^{-s})⁻²`. -/
def eulerSqF (p : ℕ) (s : Float) : Float := eulerF p s * eulerF p s

/-- The proved lower envelope `(1 + p^{-s})⁻²`. -/
def eulerLowF (p : ℕ) (s : Float) : Float :=
  let y := 1.0 / (1.0 + (Float.ofNat p) ^ (-s))
  y * y

/-! ## Geometry -/

private def polygonTag (pts : List (Float × Float)) (fill : String) (opacity : Float) : String :=
  "  <polygon " ++
    attr "points" (String.intercalate " " (pts.map fun q => fmt q.1 ++ "," ++ fmt q.2)) ++ " " ++
    attr "fill" fill ++ " " ++ attr "fill-opacity" (fmt opacity) ++ "/>"

/-! ### Panel 1: the two zeta functions -/

private def p1Left : Float := 140.0
private def p1Right : Float := 1500.0
private def p1Top : Float := 150.0
private def p1Bottom : Float := 640.0
private def sMin : Float := 1.5
private def sMax : Float := 6.0
private def vMax : Float := 7.0

private def xOfS (s : Float) : Float :=
  p1Left + (s - sMin) * (p1Right - p1Left) / (sMax - sMin)

private def yOfV (v : Float) : Float :=
  let w := if v > vMax then vMax else if v < 0.0 then 0.0 else v
  p1Bottom - w * (p1Bottom - p1Top) / vMax

private def samples : List Float :=
  (List.range 91).map fun i => sMin + (sMax - sMin) * Float.ofNat i / 90.0

private def curve (f : Float → Float) : List (Float × Float) :=
  samples.map fun s => (xOfS s, yOfV (f s))

private def panel1 : String :=
  let zeta := curve zetaPF
  let dl := curve deltaLF
  let env := curve (fun s => zetaPF s * zetaPF s)
  let bandUp := samples.map fun s => (xOfS s, yOfV (zetaPF s * zetaPF s))
  let bandDown := (samples.map fun s => (xOfS s, yOfV (2.0 - zetaPF s * zetaPF s))).reverse
  let gridLines := String.intercalate "\n" ((List.range 8).map fun i =>
    let v := Float.ofNat i
    lineTag p1Left (yOfV v) p1Right (yOfV v) "#e7ebf1" 1.0 "" ++ "\n" ++
      textTag (p1Left - 12.0) (yOfV v + 5.0) 14 "#6b7280" "end" "400" (toString i))
  let sTicks := String.intercalate "\n" ([1.5, 2.0, 2.5, 3.0, 3.5, 4.0, 4.5, 5.0, 5.5, 6.0].map
    fun s =>
      lineTag (xOfS s) p1Bottom (xOfS s) (p1Bottom + 7.0) "#9aa5b1" 1.2 "" ++ "\n" ++
        textTag (xOfS s) (p1Bottom + 26.0) 14 "#374151" "middle" "400" (fmtFixed 1 s))
  let marks :=
    let s2 := 2.0
    circleTag (xOfS s2) (yOfV (zetaPF s2)) 5.0 "#1f4fd8" "#ffffff" ++ "\n" ++
    circleTag (xOfS s2) (yOfV (deltaLF s2)) 5.0 "#c81e4a" "#ffffff" ++ "\n" ++
    textTag (xOfS s2 + 14.0) (yOfV (zetaPF s2) - 10.0) 15 "#1f4fd8" "start" "700"
      ("&#950;(2) &#8776; " ++ fmtFixed 4 (zetaPF 2.0)) ++ "\n" ++
    textTag (xOfS s2 + 14.0) (yOfV (deltaLF s2) + 22.0) 15 "#c81e4a" "start" "700"
      ("L(&#916;, 2) &#8776; " ++ fmtFixed 4 (deltaLF 2.0))
  String.intercalate "\n"
    [ textTag p1Left (p1Top - 78.0) 26 "#111827" "start" "700"
        "1. the zeta function of the modular form &#916; against the Riemann zeta function"
    , textTag p1Left (p1Top - 50.0) 16 "#4b5563" "start" "400"
        ("L(&#916;, s) = &#8721; (&#964;(n)/n^(11/2)) n^(-s)   versus   " ++
          "&#950;(s) = &#8721; n^(-s)   (partial sums, n &#8804; 256)")
    , rectTag p1Left p1Top (p1Right - p1Left) (p1Bottom - p1Top) "#ffffff" "#d1d5db" 1.0
    , gridLines
    , polygonTag (bandUp ++ bandDown) "#c81e4a" 0.08
    , lineTag p1Left (yOfV 1.0) p1Right (yOfV 1.0) "#6b7280" 1.2 "5 4"
    , textTag (p1Right - 6.0) (yOfV 1.0 - 8.0) 13 "#6b7280" "end" "400" "1"
    , polylineTag env "#9aa5b1" 2.0
    , polylineTag zeta "#1f4fd8" 3.0
    , polylineTag dl "#c81e4a" 3.4
    , sTicks
    , marks
    , textTag ((p1Left + p1Right) / 2.0) (p1Bottom + 52.0) 16 "#374151" "middle" "400" "s"
    , textTag (xOfS 5.2) (yOfV 1.55) 14 "#9aa5b1" "start" "700" "&#950;(s)&#178;  (Deligne envelope)"
    , textTag (xOfS 5.2) (yOfV 1.02 - 6.0) 14 "#c81e4a" "start" "700"
        "shaded: proved band |L - 1| &#8804; &#950;&#8342;(s)&#178; - 1" ]

/-! ### Panel 2: the local factors at `s = 2` -/

private def p2Left : Float := 140.0
private def p2Right : Float := 1500.0
private def p2Top : Float := 800.0
private def p2Bottom : Float := 1120.0
private def v2Min : Float := 0.6
private def v2Max : Float := 1.85

private def yOfV2 (v : Float) : Float :=
  let w := if v > v2Max then v2Max else if v < v2Min then v2Min else v
  p2Bottom - (w - v2Min) * (p2Bottom - p2Top) / (v2Max - v2Min)

private def xOfIdx (i : ℕ) : Float :=
  p2Left + 34.0 + Float.ofNat i * (p2Right - p2Left - 68.0) / 19.0

private def primeColumn (i : ℕ) (p : ℕ) : String :=
  let x := xOfIdx i
  let ylow := yOfV2 (eulerLowF p 2.0)
  let yhigh := yOfV2 (eulerSqF p 2.0)
  let ymod := yOfV2 (modularLocalF p 2.0)
  let yeul := yOfV2 (eulerF p 2.0)
  String.intercalate "\n"
    [ lineTag x ylow x yhigh "#cbd5e1" 8.0 ""
    , lineTag (x - 9.0) yeul (x + 9.0) yeul "#1f4fd8" 3.0 ""
    , circleTag x ymod 6.0 (fiberColor p) "#ffffff"
    , textTag x (p2Bottom + 24.0) 14 "#374151" "middle" "700" (toString p)
    , textTag x (ymod - 14.0) 11 "#374151" "middle" "400" (fmtFixed 3 (modularLocalF p 2.0)) ]

private def panel2 : String :=
  let gridLines := String.intercalate "\n" ([0.6, 0.8, 1.0, 1.2, 1.4, 1.6, 1.8].map fun v =>
    lineTag p2Left (yOfV2 v) p2Right (yOfV2 v) "#e7ebf1" 1.0 "" ++ "\n" ++
      textTag (p2Left - 12.0) (yOfV2 v + 5.0) 14 "#6b7280" "end" "400" (fmtFixed 1 v))
  String.intercalate "\n"
    ([ textTag p2Left (p2Top - 74.0) 26 "#111827" "start" "700"
         "2. the local factors at s = 2: quadratic for &#916;, linear for &#950;"
     , textTag p2Left (p2Top - 46.0) 16 "#4b5563" "start" "400"
         ("dot: (1 - y&#8346; p^(-s) + p^(-2s))^(-1) in the fiber colour; " ++
           "bar: (1 - p^(-s))^(-1); grey band: the proved envelopes " ++
           "(1 + p^(-s))^(-2) &#8804; &#8226; &#8804; (1 - p^(-s))^(-2)")
     , rectTag p2Left p2Top (p2Right - p2Left) (p2Bottom - p2Top) "#ffffff" "#d1d5db" 1.0
     , gridLines
     , lineTag p2Left (yOfV2 1.0) p2Right (yOfV2 1.0) "#6b7280" 1.2 "5 4" ] ++
     (primeList.zipIdx.map fun (p, i) => primeColumn i p) ++
     [ textTag ((p2Left + p2Right) / 2.0) (p2Bottom + 50.0) 16 "#374151" "middle" "400" "prime p" ])

/-! ### Panel 3: the two zeta series accumulating at `s = 2` -/

private def p3Left : Float := 140.0
private def p3Right : Float := 1500.0
private def p3Top : Float := 1270.0
private def p3Bottom : Float := 1560.0
private def v3Min : Float := 0.80
private def v3Max : Float := 1.75

private def xOfN (n : ℕ) : Float :=
  p3Left + Float.ofNat (n - 1) * (p3Right - p3Left) / Float.ofNat (plotN - 1)

private def yOfV3 (v : Float) : Float :=
  let w := if v > v3Max then v3Max else if v < v3Min then v3Min else v
  p3Bottom - (w - v3Min) * (p3Bottom - p3Top) / (v3Max - v3Min)

/-- The running partial sums of a series over `n = 1, …, 256`. -/
private def runningSums (f : ℕ → Float) : Array Float :=
  (Array.range plotN).foldl (fun acc i => acc.push (acc.back?.getD 0.0 + f (i + 1))) #[]

/-- The running partial sums `∑_{n ≤ m} n^{-2}`, converging to `ζ(2) = π²/6`. -/
private def zetaRunning : Array Float :=
  runningSums fun n => 1.0 / (Float.ofNat n * Float.ofNat n)

/-- The running partial sums `∑_{n ≤ m} (τ(n)/n^{11/2}) n^{-2}` of the modular zeta. -/
private def deltaRunning : Array Float :=
  runningSums fun n => normTauF n / (Float.ofNat n * Float.ofNat n)

/-- The running partial sums of the Deligne envelope `∑_{n ≤ m} d(n) n^{-2}`. -/
private def divisorRunning : Array Float :=
  runningSums fun n => Float.ofNat (divisorCount n) / (Float.ofNat n * Float.ofNat n)

private def runCurve (a : Array Float) : List (Float × Float) :=
  (List.range plotN).map fun i => (xOfN (i + 1), yOfV3 (a[i]!))

/-- The prime powers, marked on the modular curve in their fiber colour. -/
private def fiberMarks : String :=
  String.intercalate "\n" (((List.range plotN).filter fun i => cellColor (i + 1) != neutralColor).map
    fun i =>
      let n := i + 1
      circleTag (xOfN n) (yOfV3 (deltaRunning[i]!)) 4.0 (cellColor n) "#ffffff")

private def panel3 : String :=
  let zLimit := zetaRunning[plotN - 1]!
  let dLimit := deltaRunning[plotN - 1]!
  let gridLines := String.intercalate "\n" ([0.8, 1.0, 1.2, 1.4, 1.6].map fun v =>
    lineTag p3Left (yOfV3 v) p3Right (yOfV3 v) "#e7ebf1" 1.0 "" ++ "\n" ++
      textTag (p3Left - 12.0) (yOfV3 v + 5.0) 14 "#6b7280" "end" "400" (fmtFixed 1 v))
  let nTicks := String.intercalate "\n" ([1, 32, 64, 96, 128, 160, 192, 224, 256].map fun n =>
    lineTag (xOfN n) p3Bottom (xOfN n) (p3Bottom + 7.0) "#9aa5b1" 1.2 "" ++ "\n" ++
      textTag (xOfN n) (p3Bottom + 26.0) 14 "#374151" "middle" "400" (toString n))
  String.intercalate "\n"
    [ textTag p3Left (p3Top - 74.0) 26 "#111827" "start" "700"
        "3. the two series accumulating at s = 2, term by term"
    , textTag p3Left (p3Top - 46.0) 16 "#4b5563" "start" "400"
        ("running partial sums over n &#8804; 256; dots mark the prime powers, " ++
          "each in its fiber colour")
    , rectTag p3Left p3Top (p3Right - p3Left) (p3Bottom - p3Top) "#ffffff" "#d1d5db" 1.0
    , gridLines
    , polylineTag (runCurve zetaRunning) "#1f4fd8" 3.0
    , polylineTag (runCurve deltaRunning) "#c81e4a" 3.0
    , fiberMarks
    , lineTag p3Left (yOfV3 zLimit) p3Right (yOfV3 zLimit) "#1f4fd8" 1.0 "5 4"
    , lineTag p3Left (yOfV3 dLimit) p3Right (yOfV3 dLimit) "#c81e4a" 1.0 "5 4"
    , textTag (p3Right - 10.0) (yOfV3 zLimit - 10.0) 15 "#1f4fd8" "end" "700"
        ("&#950;&#8342;(2) = " ++ fmtFixed 6 zLimit ++ "   (&#960;&#178;/6 = 1.644934)")
    , textTag (p3Right - 10.0) (yOfV3 dLimit + 24.0) 15 "#c81e4a" "end" "700"
        ("L&#8342;(&#916;, 2) = " ++ fmtFixed 6 dLimit)
    , textTag (p3Left + 12.0) (yOfV3 1.05) 14 "#111827" "start" "400"
        ("the divisor series &#8721; d(n) n^(-2) reaches " ++
          fmtFixed 4 (divisorRunning[plotN - 1]!) ++ ", the proved envelope")
    , nTicks
    , textTag ((p3Left + p3Right) / 2.0) (p3Bottom + 52.0) 16 "#374151" "middle" "400" "n"
    ]


/-! ## The whole picture -/

def modularZetaSvg : String :=
  String.intercalate "\n"
    [ "<svg xmlns=\"http://www.w3.org/2000/svg\" width=\"1600\" height=\"1660\" " ++
        "viewBox=\"0 0 1600 1660\">"
    , rectTag 0.0 0.0 1600.0 1660.0 "#ffffff" "" 1.0
    , textTag 60.0 54.0 32 "#111827" "start" "700"
        "Plotting the modular form's zeta function  L(&#916;, s) = &#8721; &#964;(n) n^(-s-11/2)"
    , panel1
    , panel2
    , panel3
    , "</svg>" ]

/-! ## The companion table -/

private def csvRow (s : Float) : String :=
  String.intercalate ","
    [ fmtFixed 2 s, fmtFixed 6 (zetaPF s), fmtFixed 6 (deltaLF s)
    , fmtFixed 6 (zetaPF s * zetaPF s), fmtFixed 6 ((deltaLF s - 1.0).abs)
    , fmtFixed 6 (zetaPF s * zetaPF s - 1.0) ]

private def csvLocalRow (p : ℕ) : String :=
  String.intercalate ","
    [ toString p, fmtFixed 6 (normTauF p), fmtFixed 6 (modularLocalF p 2.0)
    , fmtFixed 6 (eulerF p 2.0), fmtFixed 6 (eulerSqF p 2.0), fmtFixed 6 (eulerLowF p 2.0) ]

/-- `visualization/modular_zeta.csv`: the two Dirichlet series in `s`, and the local factors at
`s = 2` for the first twenty primes. -/
def modularZetaCsv : String :=
  String.intercalate "\n"
    ([ "# partial sums over n <= 256"
     , "s,zeta_N,L_Delta_N,zeta_N_squared,|L-1|,bound_zeta_N_squared_minus_1" ] ++
     ([1.25, 1.5, 1.75, 2.0, 2.25, 2.5, 3.0, 3.5, 4.0, 5.0, 6.0].map csvRow) ++
     [ "", "# local factors at s = 2"
     , "p,y_p=tau(p)/p^(11/2),modular_local_factor,zeta_local_factor,upper_envelope,lower_envelope"
     ] ++ primeList.map csvLocalRow) ++ "\n"

end ModularZetaSvg

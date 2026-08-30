/-
# Separating the spiral and combining it again — the picture

Renders `visualization/monster-spiral.svg`, the next zoom of
`visualization/moonshine-trajectories-zoom.svg`.  Everything is drawn at the point
`s = 1/2 + iρ₁` of the critical line, `ρ₁ = 14.134725` being the first zero of `ζ`.

* **A** — the Monster's divisor sum `∑_{d ∣ |M|} d^{-s}` *separated* into the fifteen factor
  spirals `∑_{j ≤ e_p} (p^j)^{-s}` (`MonsterSpiral.divisorSumC_eq_prod`), one small multiple per
  supersingular prime, in that prime's fiber colour.  Each is an equiangular polygon: its steps
  shrink by the constant ratio `p^{-1/2}` and it turns by the constant angle `t log p`
  (`MonsterSpiral.norm_factorTerm`, `MonsterSpiral.factorTerm_succ`).
* **B** — *combining* them: the running product `F_2, F_2F_3, …` of the fifteen factors, from
  `1` to `∑_{d ∣ |M|} d^{-s} = 0.0896 + 0.0418i`.
* **C** — the factor spiral of `2` on its own, all forty-seven vertices `2^0, …, 2^46`: the
  forty-six exponents of `2` in `|M|` as forty-six steps of one equiangular spiral.
* **D** — the turning budget: `t·e_p·log p` for each of the fifteen primes, adding up to
  `t·log|M| = 1754.49` rad `= 279.24` turns, exactly the turning of the zeta spiral truncated at
  `N = |M|` (`MonsterSpiral.monster_turning_eq_zeta_turning`).
* **E** — the other separation: the zeta polygon `∑_{n ≤ 500} n^{-s}` split into its twenty-four
  threads `n ≡ a (mod 24)` (left, each drawn from the origin) and the twenty-four thread vectors
  added head to tail back into it (right) — `MonsterSpiral.sum_thread`,
  `MonsterSpiral.thread_eq_fourier`.

Only floating-point geometry and string manipulation live here; the statements written on the
picture are proved in `RequestProject/MonsterSpiral.lean`.
-/
import RequestProject.MonsterSpiral
import RequestProject.MoonshineZoomSvg

namespace MonsterSpiralSvg

open PrimeFibers Sporadic SporadicSvg MoonshineSvg

set_option autoImplicit false
set_option maxRecDepth 400000

/-! ## The point of the critical line at which everything is drawn -/

/-- The ordinate of the first zero of `ζ`. -/
def rho1 : Float := 14.134725

/-- The abscissa: the critical line. -/
def sig0 : Float := 0.5

/-- The truncation used for the zeta polygon in panel E. -/
def eK : Nat := 500

/-! ## The complex arithmetic of the picture -/

/-- The step `n^{-s}` at `s = σ + it`. -/
def termN (n : Nat) (sig t : Float) : C :=
  let ln := Float.log (Float.ofNat n)
  cscale (Float.exp (-(sig * ln))) (cexpi (-(t * ln)))

/-- The step `(p^j)^{-s}` of the factor spiral of `p`. -/
def facTerm (p j : Nat) (sig t : Float) : C :=
  let lp := Float.log (Float.ofNat p)
  cscale (Float.exp (-(sig * Float.ofNat j * lp))) (cexpi (-(t * Float.ofNat j * lp)))

/-- The vertices `∑_{j ≤ k} (p^j)^{-s}`, `k = 0, …, e`, of the factor spiral of `p`. -/
def facVerts (p e : Nat) (sig t : Float) : List C :=
  (((List.range (e + 1)).map fun j => facTerm p j sig t).scanl cadd (0.0, 0.0)).drop 1

/-- The value `∑_{j ≤ e} (p^j)^{-s}` of the factor spiral. -/
def facValue (p e : Nat) (sig t : Float) : C := (facVerts p e sig t).getLastD (0.0, 0.0)

/-- The Euler factor `(1 - p^{-s})^{-1}` of `\u03b6` at `p`: the point the factor spiral winds into. -/
def eulerLimit (p : Nat) (sig t : Float) : C := cdiv cone (csub cone (facTerm p 1 sig t))

/-- The continuous logarithmic spiral `u \u21a6 L(1 - (p^{-s})^u)` through the vertices of the
factor spiral of `p`: at `u = 0, 1, \u2026, e+1` it passes through the origin and the `e+1`
vertices, and it winds into the Euler factor `L`. -/
def logSpiralPts (p e : Nat) (sig t : Float) : List C :=
  let L := eulerLimit p sig t
  let uMax := Nat.min (e + 1) 16
  let steps := 80 * uMax
  let lp := Float.log (Float.ofNat p)
  (List.range (steps + 1)).map fun k =>
    let u := Float.ofNat uMax * Float.ofNat k / Float.ofNat steps
    let xu := cscale (Float.exp (-(u * sig * lp))) (cexpi (-(u * t * lp)))
    csub L (cmul L xu)

/-- The fifteen `(prime, exponent)` pairs of `|M|`. -/
def mFactors : List (Nat × Nat) := monsterFactorList

/-- The running products `1, F_2, F_2F_3, …` of the fifteen factor spirals. -/
def runningProducts (sig t : Float) : List C :=
  (mFactors.map fun pe => facValue pe.1 pe.2 sig t).scanl cmul cone

/-- The indices `n ≤ K` with `n ≡ a (mod 24)`. -/
def threadIdx (a K : Nat) : List Nat :=
  ((List.range (K + 1)).drop 1).filter fun n => n % 24 == a

/-- The vertices of the `a`-th thread of the zeta polygon. -/
def threadVerts (a K : Nat) (sig t : Float) : List C :=
  (((threadIdx a K).map fun n => termN n sig t).scanl cadd (0.0, 0.0)).drop 1

/-- The value of the `a`-th thread. -/
def threadValue (a K : Nat) (sig t : Float) : C := (threadVerts a K sig t).getLastD (0.0, 0.0)

/-- The twenty-four thread vectors added head to tail: the recombination of `sum_thread`. -/
def threadChain (K : Nat) (sig t : Float) : List C :=
  (((List.range 24).map fun a => threadValue a K sig t).scanl cadd (0.0, 0.0))

/-- The turning `t·e·log p` contributed by the factor spiral of `p`. -/
def facTurning (p e : Nat) (t : Float) : Float :=
  t * Float.ofNat e * Float.log (Float.ofNat p)

/-- `t·log|M|`, the total turning. -/
def totalTurning (t : Float) : Float :=
  (mFactors.map fun pe => facTurning pe.1 pe.2 t).foldl (· + ·) 0.0

def twoPiF : Float := 6.283185307179586

/-! ## Clipping -/

/-- A clip rectangle definition. -/
def clipDef (id : String) (x y w h : Float) : String :=
  "  <clipPath " ++ attr "id" id ++ ">\n" ++ rectTag x y w h "#ffffff" "" 1.0 ++ "\n  </clipPath>"

/-- Wrap a fragment in a clip group. -/
def clipped (id body : String) : String :=
  "  <g " ++ attr "clip-path" ("url(#" ++ id ++ ")") ++ ">\n" ++ body ++ "\n  </g>"

/-! ## Small multiples: the fifteen factor spirals -/

private def aX0 : Float := 62.0
private def aY0 : Float := 212.0
private def aBox : Float := 300.0
private def aGap : Float := 36.0

private def cellOX (i : Nat) : Float := aX0 + Float.ofNat (i % 5) * (aBox + aGap)
private def cellOY (i : Nat) : Float := aY0 + Float.ofNat (i / 5) * (aBox + 74.0)

/-- A square window of radius `r` about `(cre, cim)` inside the box at `(ox, oy)`. -/
private def mapBox (ox oy box cre cim r : Float) (z : C) : Float × Float :=
  (ox + box / 2.0 + box * (z.1 - cre) / (2.0 * r),
   oy + box / 2.0 - box * (z.2 - cim) / (2.0 * r))

private def spiralCell (i : Nat) (pe : Nat × Nat) : String :=
  let p := pe.1
  let e := pe.2
  let ox := cellOX i
  let oy := cellOY i
  let r : Float := 1.12
  let mp := mapBox ox oy aBox 0.5 0.0 r
  let vs := facVerts p e sig0 rho1
  let val := facValue p e sig0 rho1
  let col := fiberColor p
  let turnStep := rho1 * Float.log (Float.ofNat p)
  String.intercalate "\n"
    ([rectTag ox oy aBox aBox "#ffffff" "#cbd5e1" 1.0,
      lineTag ox ((mp (0.0, 0.0)).2) (ox + aBox) ((mp (0.0, 0.0)).2) "#e2e8f0" 0.9 "",
      lineTag ((mp (0.0, 0.0)).1) oy ((mp (0.0, 0.0)).1) (oy + aBox) "#e2e8f0" 0.9 "",
      circleTag ((mp (0.0, 0.0)).1) ((mp (0.0, 0.0)).2) (aBox / (2.0 * r)) "none" "#f1f5f9",
      clipped ("acell" ++ toString i) (polylineTag ((logSpiralPts p e sig0 rho1).map mp) "#cbd5e1" 1.0),
      polylineTag ((( (0.0, 0.0) :: vs).map mp)) col 1.7] ++
     (vs.map fun z =>
        circleTag ((mp z).1) ((mp z).2) (if e ≤ 6 then 3.0 else 1.6) col "#ffffff") ++
     [circleTag ((mp (eulerLimit p sig0 rho1)).1) ((mp (eulerLimit p sig0 rho1)).2) 7.0
        "none" "#0f172a",
      circleTag ((mp val).1) ((mp val).2) 5.0 "#0f172a" "#ffffff",
      textTag (ox + 12.0) (oy + 26.0) 17 col "start" "700"
        (toString p ++ (if e == 1 then "" else "^" ++ toString e)),
      textTag (ox + aBox - 12.0) (oy + 24.0) 12 "#475569" "end" "500"
        (toString (e + 1) ++ " vertices"),
      textTag (ox + 12.0) (oy + aBox + 18.0) 12 "#334155" "start" "500"
        ("|F| = " ++ fmtFixed 4 (cabs val) ++ "   arg = " ++ fmtFixed 4 (carg val)),
      textTag (ox + 12.0) (oy + aBox + 34.0) 12 "#64748b" "start" "400"
        ("turn/step = " ++ fmtFixed 3 turnStep ++ " rad;  total " ++
          fmtFixed 2 (facTurning p e rho1) ++ " rad"),
      textTag (ox + 12.0) (oy + aBox + 50.0) 12 "#64748b" "start" "400"
        ("ring = \u03b6 Euler factor (1-p^(-s))^(-1);  miss = " ++
          fmtFixed 6 (cabs (csub val (eulerLimit p sig0 rho1))))])

private def panelA : String :=
  String.intercalate "\n"
    ([textTag aX0 (aY0 - 46.0) 18 "#0f172a" "start" "700"
        "A.  Separated: the fifteen factor spirals of |M| at s = 1/2 + i\u03c1\u2081",
      textTag aX0 (aY0 - 24.0) 13 "#475569" "start" "400"
        ("\u2211_{d | |M|} d^(-s) = \u220f_p \u2211_{j \u2264 e_p} (p^j)^(-s)" ++
          "   (MonsterSpiral.divisorSumC_eq_prod);  each polygon turns by the same angle" ++
          " t\u00b7log p at every vertex, winding into \u03b6's Euler factor at p (grey curve, ring)")] ++
     (mFactors.zipIdx.map fun (pe, i) => spiralCell i pe))

/-! ## Panel B: combining the fifteen -/

private def bOX : Float := 62.0
private def bOY : Float := 1420.0
private def bBox : Float := 640.0

private def bMap : C → Float × Float := mapBox bOX bOY bBox 0.55 0.045 0.60

private def panelB : String :=
  let pts := runningProducts sig0 rho1
  let fin := pts.getLastD (0.0, 0.0)
  String.intercalate "\n"
    ([textTag bOX (bOY - 66.0) 18 "#0f172a" "start" "700"
        "B.  Combined: the running product of the fifteen factors",
      textTag bOX (bOY - 44.0) 13 "#475569" "start" "400"
        "from 1 through F\u2082, F\u2082F\u2083, \u2026 to the Monster's divisor sum at s = 1/2 + i\u03c1\u2081",
      rectTag bOX bOY bBox bBox "#ffffff" "#cbd5e1" 1.0,
      lineTag bOX ((bMap (0.0, 0.0)).2) (bOX + bBox) ((bMap (0.0, 0.0)).2) "#e2e8f0" 1.0 "",
      lineTag ((bMap (0.0, 0.0)).1) bOY ((bMap (0.0, 0.0)).1) (bOY + bBox) "#e2e8f0" 1.0 "",
      polylineTag (pts.map bMap) "#0f172a" 1.6] ++
     (pts.zipIdx.map fun (z, i) =>
        let col := if i == 0 then "#0f172a" else fiberColor ((mFactors.getD (i - 1) (2, 1)).1)
        circleTag ((bMap z).1) ((bMap z).2) 5.0 col "#ffffff") ++
     (pts.zipIdx.map fun (z, i) =>
        let lab := if i == 0 then "1" else toString (mFactors.getD (i - 1) (2, 1)).1
        textTag ((bMap z).1 + 9.0) ((bMap z).2 - 8.0) 12
          (if i == 0 then "#0f172a" else fiberColor ((mFactors.getD (i - 1) (2, 1)).1))
          "start" "700" lab) ++
     [textTag (bOX + 14.0) (bOY + bBox - 58.0) 13 "#0f172a" "start" "700"
        ("\u2211_{d | |M|} d^(-s) = " ++ fmtFixed 6 fin.1 ++
          (if fin.2 < 0.0 then " - " ++ fmtFixed 6 (-fin.2) else " + " ++ fmtFixed 6 fin.2) ++ "i"),
      textTag (bOX + 14.0) (bOY + bBox - 38.0) 13 "#334155" "start" "500"
        ("|\u2211| = " ++ fmtFixed 6 (cabs fin) ++ " = \u220f_p |F_p|   (norm_divisorSumC)"),
      textTag (bOX + 14.0) (bOY + bBox - 18.0) 13 "#334155" "start" "500"
        "the sum has 424 488 960 terms, the fifteen polygons 110 vertices"])

/-! ## Panel C: the forty-six exponents of two -/

private def cOX : Float := 762.0
private def cOY : Float := 1420.0
private def cBox : Float := 640.0

private def cMap : C → Float × Float := mapBox cOX cOY cBox 0.675 0.09 0.43

private def panelC : String :=
  let vs := facVerts 2 46 sig0 rho1
  let col := fiberColor 2
  String.intercalate "\n"
    ([textTag cOX (cOY - 66.0) 18 "#0f172a" "start" "700"
        "C.  The forty-six exponents of 2, drawn as forty-six steps",
      textTag cOX (cOY - 44.0) 13 "#475569" "start" "400"
        ("the factor spiral 2^0 + 2^(-s) + \u2026 + (2^46)^(-s): step lengths 2^(-j/2)," ++
          " constant turning t\u00b7log 2 = 9.7974 rad = 3.5143 rad (mod 2\u03c0)"),
      textTag cOX (cOY - 24.0) 13 "#475569" "start" "400"
        ("the grey logarithmic spiral L(1-(2^(-s))^u) carries the vertices into" ++
          " \u03b6's Euler factor"),
      rectTag cOX cOY cBox cBox "#ffffff" "#cbd5e1" 1.0,
      lineTag cOX ((cMap (0.0, 0.0)).2) (cOX + cBox) ((cMap (0.0, 0.0)).2) "#e2e8f0" 1.0 "",
      lineTag ((cMap (0.0, 0.0)).1) cOY ((cMap (0.0, 0.0)).1) (cOY + cBox) "#e2e8f0" 1.0 "",
      clipped "ccell" (polylineTag ((logSpiralPts 2 46 sig0 rho1).map cMap) "#cbd5e1" 1.2),
      polylineTag (vs.map cMap) col 1.8] ++
     (vs.zipIdx.map fun (z, j) =>
        circleTag ((cMap z).1) ((cMap z).2) (if j ≤ 10 then 4.2 else 2.4) col "#ffffff") ++
     (((vs.zipIdx).filter fun (_, j) => j ≤ 8).map fun (z, j) =>
        textTag ((cMap z).1 + 10.0) ((cMap z).2 - 9.0) 12 "#0f172a" "start" "700"
          ("2^" ++ toString j)) ++
     [circleTag ((cMap (eulerLimit 2 sig0 rho1)).1) ((cMap (eulerLimit 2 sig0 rho1)).2) 8.0
        "none" "#0f172a",
      textTag ((cMap (eulerLimit 2 sig0 rho1)).1 + 12.0) ((cMap (eulerLimit 2 sig0 rho1)).2 + 4.0)
        12 "#0f172a" "start" "700" "(1-2^(-s))^(-1)",
      circleTag ((cMap (facValue 2 46 sig0 rho1)).1) ((cMap (facValue 2 46 sig0 rho1)).2) 5.5
        "#0f172a" "#ffffff",
      textTag (cOX + 14.0) (cOY + cBox - 40.0) 13 "#0f172a" "start" "700"
        ("F\u2082 = " ++ fmtFixed 6 (facValue 2 46 sig0 rho1).1 ++ " + " ++
          fmtFixed 6 (facValue 2 46 sig0 rho1).2 ++ "i,  |F\u2082| = " ++
          fmtFixed 6 (cabs (facValue 2 46 sig0 rho1))),
      textTag (cOX + 14.0) (cOY + cBox - 20.0) 13 "#334155" "start" "500"
        ("total turning 46\u00b7t\u00b7log 2 = " ++ fmtFixed 2 (facTurning 2 46 rho1) ++
          " rad = " ++ fmtFixed 2 (facTurning 2 46 rho1 / twoPiF) ++ " turns")])

/-! ## Panel D: the turning budget -/

private def dOX : Float := 240.0
private def dOY : Float := 2170.0
private def dW : Float := 1240.0
private def dRow : Float := 22.0

private def dBar (i : Nat) (pe : Nat × Nat) : String :=
  let y := dOY + Float.ofNat i * dRow
  let turn := facTurning pe.1 pe.2 rho1
  let w := dW * turn / 460.0
  String.intercalate "\n"
    [textTag (dOX - 14.0) (y + 13.0) 13 (fiberColor pe.1) "end" "700"
       (toString pe.1 ++ (if pe.2 == 1 then "" else "^" ++ toString pe.2)),
     rectTag dOX y w 15.0 (fiberColor pe.1) "" 0.9,
     textTag (dOX + w + 10.0) (y + 13.0) 12 "#334155" "start" "500"
       (fmtFixed 2 turn ++ " rad  =  " ++ fmtFixed 2 (turn / twoPiF) ++ " turns")]

private def panelD : String :=
  String.intercalate "\n"
    ([textTag 62.0 (dOY - 46.0) 18 "#0f172a" "start" "700"
        "D.  The turning budget: the fifteen turnings add up to t\u00b7log|M|",
      textTag 62.0 (dOY - 24.0) 13 "#475569" "start" "400"
        ("\u2211_p v_p(|M|)\u00b7t\u00b7log p = t\u00b7log|M| (monster_total_turning), which is exactly the" ++
          " turning \u2211_{n &lt; |M|} t\u00b7log((n+1)/n) of the zeta spiral truncated at N = |M|" ++
          " (monster_turning_eq_zeta_turning)")] ++
     (mFactors.zipIdx.map fun (pe, i) => dBar i pe) ++
     [lineTag dOX (dOY + 15.0 * dRow + 4.0) (dOX + dW) (dOY + 15.0 * dRow + 4.0) "#0f172a" 1.2 "",
      textTag (dOX - 14.0) (dOY + 15.0 * dRow + 24.0) 14 "#0f172a" "end" "700" "total",
      textTag dOX (dOY + 15.0 * dRow + 24.0) 14 "#0f172a" "start" "700"
        ("t\u00b7log|M| = " ++ fmtFixed 2 (totalTurning rho1) ++ " rad = " ++
          fmtFixed 2 (totalTurning rho1 / twoPiF) ++ " turns   (log|M| = " ++
          fmtFixed 5 (totalTurning rho1 / rho1) ++ ", t = \u03c1\u2081 = 14.134725)")])

/-! ## Panel E: the twenty-four threads -/

private def eOX : Float := 62.0
private def eOY : Float := 2720.0
private def eBox : Float := 600.0

private def eMap : C → Float × Float := mapBox eOX eOY eBox 0.0 0.0 1.15

private def fOX : Float := 720.0
private def fMap : C → Float × Float := mapBox fOX eOY eBox 0.3 1.05 1.35

/-- Twenty-four hues, one per residue class mod 24. -/
private def threadColor (a : Nat) : String :=
  hsvHex (Float.ofNat a / 24.0) 0.72 0.85

private def panelE : String :=
  let chain := threadChain eK sig0 rho1
  let fin := chain.getLastD (0.0, 0.0)
  String.intercalate "\n"
    ([textTag eOX (eOY - 70.0) 18 "#0f172a" "start" "700"
        "E.  The other separation: the zeta polygon in twenty-four threads (mod 24)",
      textTag eOX (eOY - 48.0) 13 "#475569" "start" "400"
        ("left: each thread \u2211_{n \u2261 a (24), n \u2264 500} n^(-s) drawn from the origin;" ++
          " a thread step turns by t\u00b7log((n+24)/n), the turning of the 24 zeta steps it spans" ++
          " (threadTurn_eq_sum_turn)"),
      textTag eOX (eOY - 28.0) 13 "#475569" "start" "400"
        ("right: the twenty-four thread vectors added head to tail give back the whole" ++
          " polygon (sum_thread); the separation itself is finite Fourier inversion against" ++
          " the 24 McKay\u2013Thompson twists (thread_eq_fourier)"),
      rectTag eOX eOY eBox eBox "#ffffff" "#cbd5e1" 1.0,
      lineTag eOX ((eMap (0.0, 0.0)).2) (eOX + eBox) ((eMap (0.0, 0.0)).2) "#e2e8f0" 1.0 "",
      lineTag ((eMap (0.0, 0.0)).1) eOY ((eMap (0.0, 0.0)).1) (eOY + eBox) "#e2e8f0" 1.0 ""] ++
     ((List.range 24).map fun a =>
        polylineTag (((0.0, 0.0) :: threadVerts a eK sig0 rho1).map eMap) (threadColor a) 1.3) ++
     ((List.range 24).map fun a =>
        let z := threadValue a eK sig0 rho1
        circleTag ((eMap z).1) ((eMap z).2) 4.0 (threadColor a) "#ffffff") ++
     ((List.range 24).map fun a =>
        let z := threadValue a eK sig0 rho1
        textTag ((eMap z).1 + 7.0) ((eMap z).2 - 6.0) 11 (threadColor a) "start" "700"
          (toString a)) ++
     [rectTag fOX eOY eBox eBox "#ffffff" "#cbd5e1" 1.0,
      lineTag fOX ((fMap (0.0, 0.0)).2) (fOX + eBox) ((fMap (0.0, 0.0)).2) "#e2e8f0" 1.0 "",
      lineTag ((fMap (0.0, 0.0)).1) eOY ((fMap (0.0, 0.0)).1) (eOY + eBox) "#e2e8f0" 1.0 "",
      polylineTag (chain.map fMap) "#0f172a" 1.4] ++
     (chain.zipIdx.map fun (z, i) =>
        circleTag ((fMap z).1) ((fMap z).2) 4.0
          (if i == 0 then "#0f172a" else threadColor (i - 1)) "#ffffff") ++
     [circleTag ((fMap fin).1) ((fMap fin).2) 6.0 "#0f172a" "#ffffff",
      textTag (fOX + 14.0) (eOY + eBox - 40.0) 13 "#0f172a" "start" "700"
        ("\u2211_{n \u2264 500} n^(-s) = " ++ fmtFixed 6 fin.1 ++
          (if fin.2 < 0.0 then " - " ++ fmtFixed 6 (-fin.2) else " + " ++ fmtFixed 6 fin.2) ++
          "i"),
      textTag (fOX + 14.0) (eOY + eBox - 20.0) 13 "#334155" "start" "500"
        ("|\u2211| = " ++ fmtFixed 6 (cabs fin) ++
          ";  the twenty-four threads are 24 slow copies of the same spiral")])

/-! ## Panel F: where the two separations meet -/

/-- The residue class mod 24 of `2^k`: which thread the `k`-th step of the factor spiral of `2`
belongs to. -/
def twoPowClass (k : Nat) : Nat := 2 ^ k % 24

private def gOY : Float := 3490.0
private def gX0 : Float := 120.0
private def gCell : Float := 34.0

private def gSquare (k : Nat) : String :=
  let x := gX0 + Float.ofNat (k - 1) * gCell
  let a := twoPowClass k
  String.intercalate "\n"
    [rectTag x gOY (gCell - 4.0) 34.0 (threadColor a) "" 0.92,
     textTag (x + (gCell - 4.0) / 2.0) (gOY - 8.0) 11 "#475569" "middle" "400" (toString k),
     textTag (x + (gCell - 4.0) / 2.0) (gOY + 22.0) 12 "#ffffff" "middle" "700" (toString a)]

private def panelF : String :=
  String.intercalate "\n"
    ([textTag 62.0 (gOY - 78.0) 18 "#0f172a" "start" "700"
        "F.  Where the two separations meet: the forty-six exponents of 2 among the twenty-four threads",
      textTag 62.0 (gOY - 56.0) 13 "#475569" "start" "400"
        ("the k-th step of the factor spiral of 2 is the term (2^k)^(-s) of the thread" ++
          " 2^k mod 24; only four threads are ever visited (two_pow_mod24_mem_four), and the" ++
          " counts are 1, 1, 22, 22 (two_pow_thread_counts)"),
      textTag 62.0 (gOY - 36.0) 13 "#475569" "start" "400"
        ("the other twenty threads contain no power of 2 at all (thread_no_two_power);" ++
          " |M|'s own 2^46 sits in the thread 16 (ZetaMoonshine.monster_two_pow_isotypic)")] ++
     ((List.range 46).map fun i => gSquare (i + 1)) ++
     [textTag 62.0 (gOY + 70.0) 13 "#334155" "start" "500"
        ("k = 1 \u2026 46 above, the class 2^k mod 24 inside; classes 2 and 4 occur once each," ++
          " then 8 and 16 alternate to the end, 2^46 \u2261 16")])

/-! ## The document -/

def monsterSpiralSvg : String :=
  let width : Float := 1800.0
  let height : Float := 3620.0
  "<svg xmlns=\"http://www.w3.org/2000/svg\" " ++ attr "width" (fmt width) ++ " " ++
    attr "height" (fmt height) ++ " " ++
    attr "viewBox" ("0 0 " ++ fmt width ++ " " ++ fmt height) ++ ">\n" ++
  "<defs>\n" ++
  String.intercalate "\n"
    (((List.range 15).map fun i =>
        clipDef ("acell" ++ toString i) (cellOX i) (cellOY i) aBox aBox) ++
      [clipDef "ccell" cOX cOY cBox cBox]) ++
  "\n</defs>\n" ++
  rectTag 0.0 0.0 width height "#ffffff" "" 1.0 ++ "\n" ++
  textTag 62.0 54.0 24 "#0f172a" "start" "700"
    "Separating the spiral, and putting it back together" ++ "\n" ++
  textTag 62.0 84.0 15 "#334155" "start" "400"
    ("Everything at s = 1/2 + i\u03c1\u2081 on the critical line, \u03c1\u2081 = 14.134725 the first zero of" ++
      " \u03b6.  The zeta polygon \u2211_{n \u2264 N} n^(-s) turns by t\u00b7log N; the Monster's divisor sum" ++
      " \u2211_{d | |M|} d^(-s) is the same walk repackaged.") ++ "\n" ++
  textTag 62.0 108.0 15 "#334155" "start" "400"
    ("Multiplicatively it separates into fifteen equiangular factor spirals (A), which" ++
      " multiply back together (B); the prime 2 contributes forty-six steps (C) and the" ++
      " fifteen turnings add to t\u00b7log|M| (D).") ++ "\n" ++
  textTag 62.0 132.0 15 "#334155" "start" "400"
    ("Additively it separates into twenty-four threads mod 24 \u2014 the exponent of \u0394 = \u03b7^24 and" ++
      " the moonshine group of this project \u2014 which add back up (E).") ++ "\n" ++
  panelA ++ "\n" ++ panelB ++ "\n" ++ panelC ++ "\n" ++ panelD ++ "\n" ++ panelE ++ "\n" ++
  panelF ++ "\n" ++
  "</svg>\n"

/-! ## The table -/

def monsterSpiralCsv : String :=
  let hdr := "prime,exponent,factor_re,factor_im,factor_abs,factor_arg,turning_rad,turns," ++
    "running_re,running_im\n"
  let rows := (mFactors.zipIdx.map fun (pe, i) =>
    let v := facValue pe.1 pe.2 sig0 rho1
    let run := (runningProducts sig0 rho1).getD (i + 1) (0.0, 0.0)
    let turn := facTurning pe.1 pe.2 rho1
    toString pe.1 ++ "," ++ toString pe.2 ++ "," ++ fmtFixed 6 v.1 ++ "," ++ fmtFixed 6 v.2 ++
      "," ++ fmtFixed 6 (cabs v) ++ "," ++ fmtFixed 6 (carg v) ++ "," ++ fmtFixed 4 turn ++
      "," ++ fmtFixed 4 (turn / twoPiF) ++ "," ++ fmtFixed 6 run.1 ++ "," ++ fmtFixed 6 run.2)
  let thdr := "\nresidue_mod_24,terms,thread_re,thread_im,thread_abs,partial_sum_re," ++
    "partial_sum_im\n"
  let trows := ((List.range 24).map fun a =>
    let v := threadValue a eK sig0 rho1
    let c := (threadChain eK sig0 rho1).getD (a + 1) (0.0, 0.0)
    toString a ++ "," ++ toString (threadIdx a eK).length ++ "," ++ fmtFixed 6 v.1 ++ "," ++
      fmtFixed 6 v.2 ++ "," ++ fmtFixed 6 (cabs v) ++ "," ++ fmtFixed 6 c.1 ++ "," ++
      fmtFixed 6 c.2)
  hdr ++ String.intercalate "\n" rows ++ "\n" ++ thdr ++ String.intercalate "\n" trows ++ "\n"

end MonsterSpiralSvg

import Mathlib
import RequestProject.GF27
import RequestProject.Visualization
import RequestProject.FieldSizeScan
import RequestProject.SvgCore

/-!
# Three more pictures: the clock, the heat map and the analogy

This file adds the *visually intuitive* views of the two themes of the project, in the same
style as `RequestProject/Visualization.lean`: the drawn data is computed in Lean and pinned
down by kernel computation, the drawing itself is pure string manipulation.

* `svg/frobenius-clock.svg` (`ClockViz.clockSvg`) — the sharpest picture of the Frobenius
  endomorphism.  Choosing the generator `g = −t` of `GF(27)ˣ` turns the 26 nonzero elements
  into a clock face `ℤ/26`, and then
  - Frobenius `x ↦ x³` is simply **multiplication of the exponent by 3 mod 26**
    (`ClockViz.frobenius_on_clock`),
  - its fixed points are `e = 0` and `e = 13`, i.e. exactly `𝔽₃ˣ = {1, 2}`
    (`ClockViz.frobenius_fixed_on_clock`),
  - the orbit product `N(x) = x¹³` is `e ↦ 13e mod 26`, i.e. it just reads the **parity** of
    the discrete logarithm (`ClockViz.norm_on_clock`), so it retracts the clock onto the two
    gold positions.
* `svg/frobenius-defect-heatmap.svg` (`HeatViz.heatSvg`) — the error `frobDefect p k` of
  `GF(pᵏ)` as a heat map over characteristic `p` (rows) and degree `k` (columns).  The green
  cells (error `0`, i.e. genuine retraction) form vertical stripes because each row is
  periodic with period `p − 1` (`HeatViz.frobDefect_periodic`) and vanishes exactly on
  `k ≡ 1 mod (p − 1)` (`FieldSizeScan.frobDefect_eq_zero_iff_modEq`).
* `svg/retraction-analogy.svg` (`HeroViz.analogySvg`) — the two themes side by side: the same
  diagram `A ↪ B → A` with `r ∘ ι = id`, once for `Z(G) ↪ G` and once for `𝔽ₚ ↪ 𝔽_q`.

`Gallery.indexHtml` collects all thirteen pictures into `svg/index.html`.
-/

namespace ClockViz

open GF27 SvgCore

/-! ### The clock: `GF(27)ˣ` as `ℤ/26` -/

/-- The generator `g = −t = 2t` of the cyclic group `GF(27)ˣ`.  (The element `t` itself is
*not* a generator: `t¹³ = 1`.) -/
def gen : GF27 := ⟨0, 2, 0⟩

/-- `g^e`, in kernel-friendly form: the element at position `e` of the clock. -/
def pw (e : ℕ) : GF27 := pow' gen e

theorem pw_eq (e : ℕ) : pw e = gen ^ e := pow'_eq gen e

/-- The clock face: the 26 positions `g⁰, g¹, …, g²⁵`. -/
def clock : List GF27 := (List.range 26).map pw

/-- The positions are pairwise distinct, so `g` really has order 26. -/
theorem clock_nodup : clock.Nodup := by decide +kernel

/-- The clock face is exactly the set of nonzero elements: `g` generates `GF(27)ˣ`. -/
theorem mem_clock_iff (x : GF27) : x ∈ clock ↔ x ≠ 0 := by revert x; decide +kernel

/-- `g` has order 26 in `GF(27)ˣ`: the clock face really is all of `GF(27)ˣ`. -/
theorem orderOf_gen : orderOf gen = 26 := by
  have h26 : gen ^ 26 = 1 := by
    have : pw 26 = 1 := by decide +kernel
    simpa [pw_eq] using this
  have hmem : orderOf gen ∈ Nat.divisors 26 :=
    Nat.mem_divisors.2 ⟨orderOf_dvd_of_pow_eq_one h26, by norm_num⟩
  have hset : Nat.divisors 26 = {1, 2, 13, 26} := by decide
  rw [hset] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  have hpow := pow_orderOf_eq_one gen
  rcases hmem with h | h | h | h <;> rw [h] at hpow ⊢
  · exact absurd hpow (by decide)
  · exact absurd hpow (by decide)
  · exact absurd hpow (by decide)

/-- **Frobenius is multiplication by 3 on the clock**: `(gᵉ)³ = g^(3e mod 26)`. -/
theorem frobenius_on_clock (e : ℕ) (he : e < 26) : (pw e) ^ 3 = pw (3 * e % 26) := by
  have h : ∀ e ∈ List.range 26, pow' (pw e) 3 = pw (3 * e % 26) := by decide +kernel
  simpa [pow'_eq] using h e (List.mem_range.2 he)

/-- **The Frobenius fixed points on the clock are `e = 0` and `e = 13`**, i.e. `1` and `2`,
i.e. the nonzero elements of the prime subfield `𝔽₃`. -/
theorem frobenius_fixed_on_clock (e : ℕ) (he : e < 26) :
    (pw e) ^ 3 = pw e ↔ (e = 0 ∨ e = 13) := by
  have h : ∀ e ∈ List.range 26, (pow' (pw e) 3 = pw e ↔ (e = 0 ∨ e = 13)) := by decide +kernel
  simpa [pow'_eq] using h e (List.mem_range.2 he)

/-- **The orbit product reads the parity of the discrete logarithm**: `(gᵉ)¹³ = 1` for even
`e` and `= 2` for odd `e`.  In particular it lands in `𝔽₃ˣ = {1, 2}`. -/
theorem norm_on_clock (e : ℕ) (he : e < 26) :
    (pw e) ^ 13 = if e % 2 = 0 then (1 : GF27) else 2 := by
  have h : ∀ e ∈ List.range 26, pow' (pw e) 13 = if e % 2 = 0 then (1 : GF27) else 2 := by
    decide +kernel
  simpa [pow'_eq] using h e (List.mem_range.2 he)

/-- The two gold positions of the clock are `g⁰ = 1` and `g¹³ = 2`. -/
theorem gold_positions : pw 0 = 1 ∧ pw 13 = 2 := by decide +kernel

/-! ### Rendering the clock -/

private def pi : Float := 3.14159265358979

private def bigR : Float := 372.0
private def cxc : Float := 560.0
private def cyc : Float := 600.0
private def nodeR : Float := 20.0

private def angleOf (e : Nat) : Float := -pi / 2.0 + e.toFloat * (2.0 * pi / 26.0)

private def posOf (e : Nat) : Float × Float :=
  (cxc + bigR * Float.cos (angleOf e), cyc + bigR * Float.sin (angleOf e))

private def isGold (e : Nat) : Bool := e == 0 || e == 13

private def fillOf (e : Nat) : String :=
  if isGold e then "url(#fill-gold)" else if e % 2 == 0 then "url(#fill-blue)"
  else "url(#fill-pink)"

private def strokeOf (e : Nat) : String :=
  if isGold e then "#b45309" else if e % 2 == 0 then "#1d4ed8" else "#be185d"

private def markerOf (e : Nat) : String :=
  if isGold e then "gold" else if e % 2 == 0 then "blue" else "pink"

private def sup (n : Nat) : String :=
  let digit (c : Char) : String :=
    match c with
    | '0' => "⁰" | '1' => "¹" | '2' => "²" | '3' => "³" | '4' => "⁴"
    | '5' => "⁵" | '6' => "⁶" | '7' => "⁷" | '8' => "⁸" | _ => "⁹"
  String.join ((toString n).toList.map digit)

/-- The clock picture: `GF(27)ˣ ≅ ℤ/26`, Frobenius as `e ↦ 3e`. -/
def clockSvg : String :=
  let w := 1120.0
  let h := 1200.0
  let title :=
    [ text (w / 2.0) 52.0 "The Frobenius clock of GF(27)" 30.0 "url(#ink)" "middle" "bold",
      text (w / 2.0) 82.0
        "pick the generator g = −t of GF(27)ˣ; every nonzero x is gᵉ with e ∈ ℤ/26"
        15.0 "#475569",
      text (w / 2.0) 106.0
        "then Frobenius x ↦ x³ becomes the rotation-like map e ↦ 3e (mod 26)"
        15.0 "#475569" ]
  -- the faint guide circle
  let guide :=
    [ circle cxc cyc bigR "none" "#cbd5e1" 1.0 "stroke-dasharray=\"3 6\"" ]
  -- one Frobenius chord per position, with a bead of light running along it
  let chords := (List.range 26).flatMap fun e =>
    let (x1, y1) := posOf e
    let (x2, y2) := posOf (3 * e % 26)
    if e == 0 || e == 13 then
      [ selfLoop x1 y1 nodeR "#b45309" "gold",
        pulse x1 y1 (nodeR + 12.0) "#fbbf24" 2.8 (e.toFloat * 0.4) ]
    else
      let d := curveD x1 y1 x2 y2 (nodeR + 3.0) (nodeR + 9.0) 26.0
      [ path d (strokeOf e) 1.5 (markerOf e) "none" "opacity=\"0.55\"",
        comet d (strokeOf e) 4.2 3.6 (e.toFloat * 0.14) 300.0 ]
  -- the 26 clock positions
  let nodes := (List.range 26).flatMap fun e =>
    let (x, y) := posOf e
    let (lx, ly) := (cxc + (bigR + 40.0) * Float.cos (angleOf e),
                     cyc + (bigR + 40.0) * Float.sin (angleOf e))
    [ nodeGroup
        [ circle x y nodeR (fillOf e) (strokeOf e) 2.0 "class=\"pop\"",
          textMid x y (GF27Viz.code (pw e)) 11.5 "#0f172a" "middle" "bold" ] ] ++
    (if isGold e then [] else
      [ textMid lx ly ("g" ++ sup e) 13.0 "#64748b" ])
  -- the two fixed positions, called out
  let golds :=
    [ textMid cxc (cyc - bigR - 76.0) "g⁰ = 1 ∈ 𝔽₃ : fixed by Frobenius" 15.0 "#92400e"
        "middle" "bold",
      textMid cxc (cyc + bigR + 76.0) "g¹³ = 2 ∈ 𝔽₃ : fixed by Frobenius" 15.0 "#92400e"
        "middle" "bold" ]
  -- central explanation card
  let panelW := 470.0
  let ph := 240.0
  let panel :=
    [ card (cxc - panelW / 2.0) (cyc - ph / 2.0) panelW ph 22.0 "#ffffffee" "#c7d2fe" 1.6,
      textMid cxc (cyc - ph / 2.0 + 34.0) "GF(27)ˣ ≅ ℤ/26" 20.0 "#3730a3" "middle" "bold",
      textMid cxc (cyc - 40.0) "Frobenius:   gᵉ ↦ g³ᵉ" 16.0 "#0f172a",
      textMid cxc (cyc - 12.0) "fixed ⟺ 3e ≡ e ⟺ 2e ≡ 0 (mod 26)" 14.5 "#475569",
      textMid cxc (cyc + 14.0) "⟺ e ∈ {0, 13}  =  𝔽₃ˣ" 14.5 "#b45309" "middle" "bold",
      line (cxc - 190.0) (cyc + 36.0) (cxc + 190.0) (cyc + 36.0) "#e2e8f0" 1.2,
      textMid cxc (cyc + 60.0) "orbit product:   N(gᵉ) = g¹³ᵉ" 16.0 "#0f172a",
      textMid cxc (cyc + 86.0) "= 1 if e is even, 2 if e is odd" 14.5 "#475569" ]
  -- legend
  let ly := h - 76.0
  let legend :=
    [ card 70.0 (ly - 34.0) (w - 140.0) 78.0 16.0 "#ffffffcc" "#e2e8f0" 1.0,
      circle 110.0 ly 12.0 "url(#fill-blue)" "#1d4ed8" 1.8,
      text 130.0 (ly + 5.0) "even e : N(gᵉ) = 1" 13.5 "#475569" "start",
      circle 320.0 ly 12.0 "url(#fill-pink)" "#be185d" 1.8,
      text 340.0 (ly + 5.0) "odd e : N(gᵉ) = 2" 13.5 "#475569" "start",
      circle 530.0 ly 12.0 "url(#fill-gold)" "#b45309" 1.8,
      text 550.0 (ly + 5.0) "Frobenius-fixed: the prime subfield 𝔽₃" 13.5 "#475569" "start",
      text 870.0 (ly + 5.0) "arrow / running bead: x ↦ x³" 13.5 "#475569" "start" ]
  document w h (title ++ guide ++ chords ++ nodes ++ golds ++ panel ++ legend)

end ClockViz

namespace HeatViz

open SvgCore FieldSizeScan

/-! ### The heat map of the error `frobDefect p k` -/

/-- The characteristics shown as rows of the heat map. -/
def heatPrimes : List ℕ := [2, 3, 5, 7, 11, 13]

/-- The degrees shown as columns of the heat map. -/
def heatDegrees : List ℕ := List.range' 1 16

/-- The drawn table: for each characteristic `p`, the errors `frobDefect p k` for
`k = 1, …, 16`. -/
def heatTable : List (ℕ × List ℕ) :=
  heatPrimes.map fun p => (p, heatDegrees.map fun k => frobDefect p k)

/-- The numbers actually drawn.  In characteristic 2 the error is always `0` (every `GF(2ᵏ)`
retracts); the other rows are periodic with period `p − 1`, starting at `0` for `k = 1`. -/
theorem heatTable_eq :
    heatTable =
      [(2, [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
       (3, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]),
       (5, [0, 3, 2, 3, 0, 3, 2, 3, 0, 3, 2, 3, 0, 3, 2, 3]),
       (7, [0, 5, 4, 3, 4, 5, 0, 5, 4, 3, 4, 5, 0, 5, 4, 3]),
       (11, [0, 9, 8, 9, 8, 5, 8, 9, 8, 9, 0, 9, 8, 9, 8, 5]),
       (13, [0, 11, 10, 9, 8, 11, 6, 11, 8, 9, 10, 11, 0, 11, 10, 9])] := by
  decide

/-- **Each row of the heat map is periodic with period `p − 1`.**  This is why the green
(error `0`) cells line up in vertical stripes. -/
theorem frobDefect_periodic (p k : ℕ) (hk : 1 ≤ k) :
    frobDefect p (k + (p - 1)) = frobDefect p k := by
  unfold frobDefect
  have hkk : k + (p - 1) - 1 = (k - 1) + (p - 1) := by omega
  rw [hkk, Nat.gcd_add_self_right]

/-! The green cells are exactly the retractions: for a prime `p` and a degree `k ≥ 1` the
error vanishes iff `k ≡ 1 mod (p − 1)` (`FieldSizeScan.frobDefect_eq_zero_iff_modEq`), and
then — and only then — the Frobenius orbit product of `GF(pᵏ)` is a retraction onto the prime
subfield `𝔽ₚ` (`FieldSizeScan.retraction_iff_frobDefect_eq_zero`). -/

/-! ### Rendering the heat map -/

private def cellW : Float := 56.0
private def cellH : Float := 46.0
private def gridX : Float := 150.0
private def gridY : Float := 176.0

private def cellFill (p v : ℕ) : String :=
  if v == 0 then "#10b981"
  else heatRamp (v.toFloat / ((p - 1 : ℕ).toFloat))

/-- The heat map picture. -/
def heatSvg : String :=
  let cols := heatDegrees.length.toFloat
  let rows := heatPrimes.length.toFloat
  let w := gridX + cellW * cols + 250.0
  let h := gridY + cellH * rows + 200.0
  let title :=
    [ text (w / 2.0) 54.0 "How far is the Frobenius orbit product from a retraction?" 28.0
        "url(#ink)" "middle" "bold",
      text (w / 2.0) 84.0
        "cell (p, k) : how many elements of 𝔽ₚ are moved by the orbit product N of GF(pᵏ)"
        15.0 "#475569",
      text (w / 2.0) 108.0
        "green = 0 = genuine retraction onto 𝔽ₚ ; hotter = larger error, up to p − 1"
        15.0 "#475569" ]
  let colHeads := (heatDegrees.zipIdx).map fun (k, j) =>
    textMid (gridX + cellW * (j.toFloat + 0.5)) (gridY - 22.0) (toString k) 14.0 "#334155"
      "middle" "bold"
  let axisLabels :=
    [ textMid (gridX + cellW * cols / 2.0) (gridY - 50.0) "degree k" 16.0 "#0f172a"
        "middle" "bold",
      text 40.0 (gridY + cellH * rows / 2.0) "characteristic p" 16.0 "#0f172a" "middle" "bold"
        "normal" ("transform=\"rotate(-90 40 " ++ num (gridY + cellH * rows / 2.0) ++ ")\"") ]
  let body := (heatTable.zipIdx).flatMap fun ((p, vals), i) =>
    let y := gridY + cellH * i.toFloat
    let rowHead :=
      [ textMid (gridX - 30.0) (y + cellH / 2.0) (toString p) 15.0 "#0f172a" "end" "bold",
        textMid (gridX + cellW * cols + 60.0) (y + cellH / 2.0)
          ("period " ++ toString (p - 1)) 13.0 "#64748b" "start" ]
    let cells := (vals.zipIdx).flatMap fun (v, j) =>
      let x := gridX + cellW * j.toFloat
      [ rect (x + 2.0) (y + 2.0) (cellW - 4.0) (cellH - 4.0) 7.0 (cellFill p v)
          (if v == 0 then "#047857" else "#ffffff") (if v == 0 then 2.0 else 1.0) ""
          "class=\"cell\"",
        textMid (x + cellW / 2.0) (y + cellH / 2.0) (toString v) 14.0
          (if v == 0 then "#ffffff" else if v.toFloat > (p - 1 : ℕ).toFloat / 2.0
            then "#ffffff" else "#7c2d12") "middle" "bold" ]
    rowHead ++ cells
  let legendY := gridY + cellH * rows + 60.0
  let legend :=
    [ text 150.0 (legendY - 14.0) "error, as a fraction of the maximum p − 1" 13.5 "#475569"
        "start" ] ++
    rampBar 150.0 legendY 260.0 18.0 24 heatRamp ++
    [ text 150.0 (legendY + 34.0) "0" 12.0 "#64748b" "start",
      text 410.0 (legendY + 34.0) "p − 1" 12.0 "#64748b" "end",
      rect 470.0 legendY 26.0 18.0 6.0 "#10b981" "#047857" 2.0,
      text 506.0 (legendY + 14.0) "error 0 : N is a retraction onto 𝔽ₚ" 13.5 "#475569"
        "start",
      text 150.0 (legendY + 66.0)
        "the stripes are a theorem: frobDefect p (k + (p−1)) = frobDefect p k, and the error is 0 exactly when k ≡ 1 (mod p−1)"
        13.5 "#334155" "start" ]
  document w h (title ++ axisLabels ++ colHeads ++ body ++ legend)

end HeatViz

namespace HeroViz

open SvgCore

/-! ### The analogy picture -/

private def sideDiagram (x0 y0 : Float) (titleStr subtitle small big : String)
    (arrowLeft arrowRight caption : String) (accent : String) (marker exampleLine : String) :
    List String :=
  let ax := x0 + 120.0
  let bx := x0 + 300.0
  let cx := x0 + 480.0
  let y := y0 + 190.0
  let dIota := curveD ax y bx y 60.0 72.0 0.0
  let dR := curveD bx y cx y 70.0 62.0 0.0
  [ card x0 y0 600.0 452.0 26.0 "#ffffffdd" "#e2e8f0" 1.4,
    textMid (x0 + 300.0) (y0 + 46.0) titleStr 22.0 accent "middle" "bold",
    textMid (x0 + 300.0) (y0 + 76.0) subtitle 14.0 "#475569",
    -- the three objects
    pulse ax y 66.0 "#fbbf24" 3.2 0.0,
    circle ax y 54.0 "url(#fill-gold)" "#b45309" 2.2 "class=\"pop\"",
    textMid ax y small 19.0 "#0f172a" "middle" "bold",
    circle bx y 62.0 "url(#fill-violet)" "#6d28d9" 2.2 "class=\"pop\"",
    textMid bx y big 21.0 "#0f172a" "middle" "bold",
    pulse cx y 66.0 "#fbbf24" 3.2 1.6,
    circle cx y 54.0 "url(#fill-gold)" "#b45309" 2.2 "class=\"pop\"",
    textMid cx y small 19.0 "#0f172a" "middle" "bold",
    -- the two arrows, with a bead of light running along each
    path dIota "#334155" 2.2 "slate",
    comet dIota "#0ea5e9" 5.0 2.4 0.0 120.0,
    textMid ((ax + bx) / 2.0) (y - 20.0) arrowLeft 16.0 "#334155" "middle" "bold",
    path dR "#b45309" 2.6 "gold",
    comet dR "#fbbf24" 5.0 2.4 1.2 120.0,
    textMid ((bx + cx) / 2.0) (y - 20.0) arrowRight 16.0 "#b45309" "middle" "bold",
    -- the composite
    curve ax (y + 54.0) cx (y + 54.0) 8.0 12.0 92.0 "#047857" "green" 2.2,
    textMid ((ax + cx) / 2.0) (y + 152.0) "r ∘ ι = id" 17.0 "#047857" "middle" "bold",
    textMid (x0 + 300.0) (y0 + 380.0) caption 13.5 "#475569",
    textMid (x0 + 300.0) (y0 + 418.0) exampleLine 13.5 "#7c3aed" "middle" "bold" ] ++
  [ chip (x0 + 300.0) (y0 + 110.0) 300.0 26.0 marker "#eef2ff" "#c7d2fe" "#3730a3" 12.5 ]

/-- The side-by-side analogy: the group retraction and the field retraction. -/
def analogySvg : String :=
  let w := 1320.0
  let h := 700.0
  let title :=
    [ text (w / 2.0) 52.0 "One picture, two theories: a retraction onto the centre" 29.0
        "url(#ink)" "middle" "bold",
      text (w / 2.0) 82.0
        "a map back onto a distinguished sub-object which is the identity there"
        15.0 "#475569" ]
  let left := sideDiagram 40.0 120.0 "Groups" "the centre Z(G) inside G"
    "Z(G)" "G" "ι" "r"
    "r is a homomorphism G → Z(G) fixing Z(G) pointwise; then G ≅ ker r × Z(G)"
    "#4338ca" "Z(G) ↪ G → Z(G)"
    "example: G = D₆ (4 ∤ 6), r reads the parity of the rotation"
  let right := sideDiagram 680.0 120.0 "Finite fields"
    "the prime subfield 𝔽ₚ inside GF(q), q = pᵏ"
    "𝔽ₚ" "GF(q)" "ι" "N"
    "N(x) = x · xᵖ · ⋯ · x^(pᵏ⁻¹) is Frobenius-invariant, so it lands in 𝔽ₚ"
    "#be185d" "𝔽ₚ ↪ GF(q) → 𝔽ₚ"
    "example: q = 27, p = 3, N(x) = x¹³"
  document w h (title ++ left ++ right)

end HeroViz

namespace Gallery

/-- A small dark-themed gallery page collecting every picture of the project, the six-part series on the twist first. -/
def indexHtml : String :=
  let card (file caption body : String) : String :=
    "  <figure class=\"card\">\n" ++
    "    <a href=\"" ++ file ++ "\"><img src=\"" ++ file ++ "\" alt=\"" ++ caption ++
      "\"/></a>\n" ++
    "    <figcaption><b>" ++ caption ++ "</b><span>" ++ body ++ "</span></figcaption>\n" ++
    "  </figure>"
  String.intercalate "\n"
    [ "<!DOCTYPE html>",
      "<html lang=\"en\"><head><meta charset=\"utf-8\"/>",
      "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"/>",
      "<title>Retractions onto the centre — pictures</title>",
      "<style>",
      "  :root { color-scheme: dark; }",
      "  body { margin:0; padding:48px 24px 80px; background:radial-gradient(1200px 700px at 50% -10%, #1e293b 0%, #0b1120 60%, #060911 100%); color:#e2e8f0; font-family:'DejaVu Sans',system-ui,Helvetica,Arial,sans-serif; }",
      "  h1 { text-align:center; font-size:2.2rem; margin:0 0 8px; background:linear-gradient(90deg,#60a5fa,#c084fc,#f472b6); -webkit-background-clip:text; background-clip:text; color:transparent; }",
      "  p.lede { text-align:center; max-width:820px; margin:0 auto 48px; color:#94a3b8; line-height:1.6; }",
      "  .grid { display:grid; gap:32px; grid-template-columns:repeat(auto-fit,minmax(420px,1fr)); max-width:1600px; margin:0 auto; }",
      "  .card { margin:0; background:#f8fafc; border-radius:20px; overflow:hidden; box-shadow:0 18px 40px rgba(0,0,0,.55); transition:transform .25s ease, box-shadow .25s ease; }",
      "  .card:hover { transform:translateY(-6px) scale(1.01); box-shadow:0 26px 60px rgba(56,189,248,.35); }",
      "  .card img { display:block; width:100%; height:auto; background:#fff; }",
      "  figcaption { padding:16px 20px 22px; background:#0f172a; }",
      "  figcaption b { display:block; font-size:1.05rem; color:#e2e8f0; margin-bottom:6px; }",
      "  figcaption span { color:#94a3b8; font-size:.92rem; line-height:1.5; }",
      "  footer { text-align:center; color:#64748b; margin-top:56px; font-size:.9rem; }",
      "  code { color:#a5b4fc; }",
      "</style></head><body>",
      "<h1>Retractions onto the centre</h1>",
      "<p class=\"lede\">Every picture below is generated from Lean data in this project, and the data is checked against the formal statements by kernel computation. Two themes, one shape: a map back onto a distinguished sub-object that is the identity there — the centre <code>Z(G)</code> of a group, and the prime subfield <code>𝔽ₚ</code> of a finite field. The sheet at the top is the atlas: Pascal's triangle mod 3, one row per picture, every row a link. The six posters after it are meant for students: they start from Pascal's triangle and end at the transfer homomorphism.</p>",
      "<div class=\"grid\">",
      card "student-0-atlas.svg" "The atlas — 27 rows, 27 pictures"
        "Pascal's triangle mod 3 expanded to 27 = 3³ rows and used as the index of this gallery: every row is a link to one picture, and the three base-3 digits of the row number name an element of GF(27). The gold rows 1, 3, 9 are the ones with a vanishing interior — provably, the powers of 3.",
      card "student-1-freshmans-dream.svg" "For students, 1 — why xᵖ is a homomorphism"
        "Pascal's triangle mod 3, twenty-seven rows of it: the interior of row 3, and of every row 3ʲ, is divisible by 3, so (x+y)³ = x³ + y³. Beside it the same triangle mod 2 (Sierpiński), mod 5 and mod 7, and the row census (nᵢ+1)(nᵢ₊₁+1)⋯ that explains all of them.",
      card "student-2-cyclotomic-clocks.svg" "For students, 2 — Frobenius orbits without a field"
        "Write every nonzero element as a power of a generator and x ↦ xᵖ becomes j ↦ p·j on ℤ/(pᵏ−1). The orbits are then the cyclotomic cosets, drawn here for GF(8), GF(9), GF(16); the gold fixed points are 𝔽ₚˣ.",
      card "student-3-subfield-tower.svg" "For students, 3 — the subfields of GF(2¹²)"
        "Six floors, one per divisor of 12, each the fixed field of an iterate of Frobenius; the prime subfield 𝔽₂ at the bottom is the fixed field of Frobenius itself.",
      card "student-4-dictionary.svg" "For students, 4 — the dictionary"
        "Ten lines translating the group half of the project into the field half: centre ↔ prime subfield, transfer ↔ orbit product, index ↔ 1 + p + ⋯ + p^(k−1), and the same coprimality test for whether the retraction exists.",
      card "student-5-orbit-spiral.svg" "For students, 5 — why the orbit product lands in 𝔽ₚ"
        "The four conjugates of x in GF(81) spiralling into the prime subfield: their product is x⁴⁰, and (p−1)·40 = 3⁴ − 1, so the answer satisfies y³ = y.",
      card "student-6-exercise-ladder.svg" "For students, 6 — ten things to try"
        "A ladder of exercises from a five-line computation in 𝔽₅ to the transfer homomorphism, each rung naming the theorem in this project that settles it.",
      card "twist-1-dead-dial.svg" "The twist, Act I — the dial that dies"
        "On the prime subfield the Frobenius orbit sum is a single scalar, Tr(a) = k·a; when p ∣ k that scalar is 0 and the whole prime subfield collapses onto 0. A rescaling x ↦ c·Tr(x) repairs the orbit sum exactly when p ∤ k.",
      card "twist-2-still-onto.svg" "The twist, Act II — onto, but aimed wrongly (animated, 3-d)"
        "GF(27) cut into the three level sets of Tr, nine elements each: the orbit sum is onto 𝔽₃, so nothing is missing on the value side. What is wrong is that all three points of 𝔽₃ lie in the same level, Tr = 0.",
      card "twist-3-the-twist.svg" "The twist, Act III — turn the field, not the value (animated, 3-d)"
        "Multiplication by c = 2t² carries 𝔽₃ out of the kernel and across all three levels, one point each. That is the whole trick: Tr is 𝔽₃-linear, so Tr(c·a) = a·Tr(c) = a.",
      card "twist-4-repaired-map.svg" "The twist, Act IV — the repaired map"
        "R(x) = Tr(2t²·x) = x.c₀ + x.c₂ : three fibres of nine, each containing exactly one point of 𝔽₃ — its own value. Additive, 𝔽₃-linear, onto, idempotent, the identity on 𝔽₃; and not multiplicative, which is what the repair costs.",
      card "twist-5-nine-twists.svg" "The twist, Act V — nine twists, nine repairs"
        "Every c with Tr(c) = 1 gives a retraction, and GF(27) has nine of them. Read through the basis 1, t, t², they are exactly the nine 𝔽₃-linear functionals sending 1 ↦ 1: there is no canonical additive retraction, only a canonical supply.",
      card "twist-6-census.svg" "The twist, Act VI — where it is indispensable"
        "All 310 field sizes q = pᵏ ≤ 1824. Seven have a dead dial (p ∣ k): 4, 16, 27, 64, 256, 729, 1024. Of those only 729 also fails multiplicatively — the one size in the scan where neither dial turns and the twist is the only repair left.",
      card "twist-7-pivot-ladder.svg" "The twist, Act VII — the pivot ladder"
        "The same question past the end of the scan, on a logarithmic axis up to 10¹². Sizes where both canonical maps are broken are very rare: 729, 531441, 9765625, 387420489, 30517578125, 282429536481, 678223072849 — one below 10³, two below 10⁶, four below 10⁹, seven below 10¹². A dual failure is exactly an odd p with k = m·p and m ≢ 1 (mod p−1).",
      card "repair-wheel-3d.svg" "Why the orbit product lands in 𝔽ₚ (animated, 3-d)"
        "GF(125)ˣ ≅ ℤ/124 as a slowly turning wheel. On labels the orbit product N(x) = x³¹ is j ↦ 31j, so it crushes each Frobenius orbit onto the small wheel 𝔽₅ˣ = ℤ/4. Restricted there it is the gear ratio k = 3, which is what the error measures — and gcd(3,4) = 1 lets one turn the gear back: R(x) = N(x)³ = x⁹³.",
      card "repair-gears-3d.svg" "The two dials of a finite field (animated, 3-d)"
        "On the prime field the orbit product is the exponent k on ℤ/(p−1) and the orbit sum is the scalar k on ℤ/p. A repair exists exactly when that ratio can be inverted: gcd(k, p−1) = 1 multiplicatively, p ∤ k additively. GF(9), GF(125) and GF(729) show all three outcomes.",
      card "repair-atlas-3d.svg" "Every error of the scan, repaired (animated, 3-d)"
        "The 18 field sizes q ≤ 1824 whose orbit product is not a retraction, as bars of height equal to their error, rocking in three dimensions and sinking to flat green as the repaired map replaces the orbit product. Gold rims: a multiplicative repair also exists (q = 125, 1331). Violet rim: rescaling fails (q = 729).",
      card "retraction-analogy.svg" "The analogy"
        "The same diagram A ↪ B → A with r ∘ ι = id, once for the centre Z(G) inside a group G, once for the prime subfield 𝔽ₚ inside GF(q).",
      card "frobenius-clock.svg" "The Frobenius clock of GF(27)"
        "With g = −t a generator, GF(27)ˣ is the clock ℤ/26 and Frobenius is e ↦ 3e. Its fixed points 0 and 13 are exactly 𝔽₃ˣ, and the orbit product N(x) = x¹³ reads the parity of the discrete logarithm.",
      card "frobenius-orbits.svg" "Frobenius orbits in GF(27)"
        "All 27 elements, partitioned into the orbits of x ↦ x³: three fixed points (the prime subfield 𝔽₃) and eight 3-cycles.",
      card "frobenius-norm-retraction.svg" "The orbit product as a retraction"
        "N(x) = x · x³ · x⁹ = x¹³ collapses GF(27) onto 𝔽₃; the gold arrows N(a) = a are the retraction property.",
      card "gf9-error-repair.svg" "The smallest error, and its repair"
        "GF(9) is the smallest field size whose orbit product is not a retraction: the crimson arrow N(2) = 1 is the whole error. No multiplicative map can straighten it, but the normalized additive orbit sum R(x) = 2·(x + x³) is a genuine retraction onto 𝔽₃.",
      card "frobenius-defect-heatmap.svg" "How far from a retraction?"
        "The error of GF(pᵏ) as a heat map in (p, k). The green stripes — error 0 — are the genuine retractions, and they recur with period p − 1.",
      card "frobenius-defect-3d.svg" "The error surface in three dimensions"
        "The same error raised into a solid bar over each (p, k), across the reach of the expanded scan q ≤ 1824: flat green tiles are the genuine retractions, gold rims mark the cells that really are field sizes pᵏ ≤ 1824, and the ridge k = 2 climbs to error 39 at GF(1681) = GF(41²).",
      card "field-size-scan.svg" "Every size q = 2 … 97, tested"
        "One column per candidate field size: grey × when no field of that size exists, green when the orbit product retracts, a red error bar when it does not.",
      card "field-size-scan-degrees.svg" "The same scan by degree"
        "Four panels, one per characteristic: the error of GF(pⁿ) against n, vanishing exactly on n ≡ 1 (mod p − 1).",
      card "center-retraction.svg" "The group-theoretic zoo"
        "Which families of groups retract onto their centre — each row naming the theorem in this project that proves it.",
      "</div>",
      "<footer>Regenerate with <code>lake env lean --run scripts/GenerateSvg.lean</code></footer>",
      "</body></html>", "" ]

end Gallery

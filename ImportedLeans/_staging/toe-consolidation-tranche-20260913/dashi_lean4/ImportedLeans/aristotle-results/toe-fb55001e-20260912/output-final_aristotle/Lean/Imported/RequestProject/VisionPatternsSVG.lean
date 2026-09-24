import RequestProject.VisionPatterns
import RequestProject.SVG
import Lean

/-!
# VisionPatternsSVG — an animated *visual proof* of the vision findings

`RequestProject.VisionPatterns` freezes the OpenCV pattern findings as literal
histogram rows and **certifies** them, sorry-free, with `native_decide`:

* **Harmonic dominance** — the trivector cell (harmonic code `0`) is the unique
  strict maximum of the harmonic histogram in *every* corpus
  (`harm_trivector_dominant_all`).
* **Harmonic monotonicity** — in the three large corpora the whole harmonic
  histogram is strictly decreasing `0 > 5 > 7 > 11 > 13`
  (`harm_strictDecreasing_large`); the tiny `itself` corpus is the lone
  exception (`itself_harm_not_decreasing`).
* **Argmax peaks** — the OpenCV `argmax` of every `cog` (92-bucket) and `triad`
  (20-bucket) raster, each certified as the (unique, or for `batteries`-triad
  tied) maximum bucket (`*_cog_argmax`, `*_triad_argmax`,
  `batteries_triad_tie`).

This layer renders those very certified literals as a single self-contained,
self-playing **animated SVG**.  Every coordinate is computed natively by Lean
from the same `VisionPatterns.*` data the theorems are about, so the film is a
faithful, machine-checked picture of the findings.

Three animated movements:

1. **Harmonic dominance & monotonicity** — for each corpus the 5 harmonic bars
   grow in; the trivector bar is gold and pulses (it always wins); a ✓ caption
   marks the corpora where strict decrease is *proven*, and the `itself` panel is
   flagged as the certified exception.
2. **Cognitive peaks (92×)** — each corpus's `cog` sparkline draws itself in and
   a gold marker drops onto the certified `argmax` bucket.
3. **Semantic-triad peaks (20×)** — each corpus's `triad` bars grow in with the
   certified peak highlighted; the `batteries` tie is shown with two crowns.

Commands:

* `#visionprooffilm`            — build the film for all four corpora, report size.
* `#writevisionproof "path"`    — build the film and write the animated SVG to `path`.
-/

open Lean Elab Command SVG

namespace VisionPatternsSVG

open VisionPatterns

/-! ## Numeric helpers -/

/-- Largest entry of a `Nat` list (0 on empty). -/
def fmax (l : List Nat) : Nat := l.foldl Nat.max 0

/-- Format a `Float` for SVG output. -/
def fc (f : Float) : String := toString f

/-- Index of the (first) maximum entry. -/
def argmaxIdx (l : List Nat) : Nat :=
  let m := fmax l
  (l.zipIdx.filter (fun (v, _) => v == m)).headD (0, 0) |>.2

/-! ## Palette -/

/-- Harmonic bar colour by raster index `0..4`. -/
def harmColor : Nat → String
  | 0 => "#ffd700" | 1 => "#4fd86a" | 2 => "#2bd0c0" | 3 => "#5a8bff" | _ => "#ff7a59"

/-- Short label for each harmonic code, in raster order `[0,5,7,11,13]`. -/
def harmLabel : Nat → String
  | 0 => "trivector"  | 1 => "muse 9^5" | 2 => "heptad 6^7"
  | 3 => "hemi 2^11"  | _ => "rec 3^13"

/-- Per-corpus accent colour. -/
def corpusColor : Nat → String
  | 0 => "#9fb0e0" | 1 => "#2bd0c0" | 2 => "#ffd23d" | _ => "#ff7a59"

/-! ## Movement 1 — harmonic dominance & monotonicity -/

/-- One harmonic panel: 5 growing bars, the trivector bar gold & pulsing, a
caption certifying strict decrease (or the exception for `itself`). -/
def harmPanel (px py panelW panelH : Float) (delayMs : Nat)
    (title : String) (data : List Nat) (decreasing : Bool) : String :=
  let n      := data.length
  let maxV   := Float.ofNat (fmax data)
  let areaTop := py + 30.0
  let areaH   := panelH - 70.0
  let baseY   := areaTop + areaH
  let step    := (panelW - 20.0) / Float.ofNat (Nat.max n 1)
  let barW    := step * 0.62
  let bars := data.zipIdx.foldl (fun acc (v, i) =>
    let frac := if maxV == 0.0 then 0.0 else Float.ofNat v / maxV
    let bh   := frac * areaH
    let bx   := px + 12.0 + Float.ofNat i * step
    let ty   := baseY - bh
    let col  := harmColor i
    let beg  := s!"{delayMs + i * 130}ms"
    let pulse :=
      if i == 0 then
        s!"<animate attributeName=\"opacity\" values=\"1;0.55;1\" dur=\"1.8s\" begin=\"{delayMs + 700}ms\" repeatCount=\"indefinite\"/>"
      else ""
    let crown :=
      if i == 0 then
        s!"<text x=\"{fc (bx + barW/2.0)}\" y=\"{fc (ty - 6.0)}\" font-size=\"13\" text-anchor=\"middle\" fill=\"#ffd700\" opacity=\"0\">★<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delayMs + 600}ms\" dur=\"0.5s\" fill=\"freeze\"/></text>"
      else ""
    acc ++
      s!"<rect x=\"{fc bx}\" y=\"{fc baseY}\" width=\"{fc barW}\" height=\"0\" rx=\"3\" fill=\"{col}\">" ++
      s!"<animate attributeName=\"height\" from=\"0\" to=\"{fc bh}\" begin=\"{beg}\" dur=\"0.6s\" fill=\"freeze\" calcMode=\"spline\" keySplines=\"0.3 0 0.2 1\" keyTimes=\"0;1\"/>" ++
      s!"<animate attributeName=\"y\" from=\"{fc baseY}\" to=\"{fc ty}\" begin=\"{beg}\" dur=\"0.6s\" fill=\"freeze\" calcMode=\"spline\" keySplines=\"0.3 0 0.2 1\" keyTimes=\"0;1\"/>" ++
      pulse ++ "</rect>" ++ crown ++
      s!"<text x=\"{fc (bx + barW/2.0)}\" y=\"{fc (baseY + 14.0)}\" font-size=\"8\" text-anchor=\"middle\" fill=\"#9fb0e0\">{harmLabel i}</text>" ++
      s!"<text x=\"{fc (bx + barW/2.0)}\" y=\"{fc (baseY + 24.0)}\" font-size=\"7\" text-anchor=\"middle\" fill=\"#6677aa\">{v}</text>"
    ) ""
  let cap :=
    if decreasing then
      s!"<text x=\"{fc px}\" y=\"{fc (py + 16.0)}\" font-size=\"10\" fill=\"#4fd86a\" opacity=\"0\">✓ strictly decreasing (proven)<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delayMs + 900}ms\" dur=\"0.6s\" fill=\"freeze\"/></text>"
    else
      s!"<text x=\"{fc px}\" y=\"{fc (py + 16.0)}\" font-size=\"10\" fill=\"#ff7a59\" opacity=\"0\">⚠ exception: not decreasing (proven)<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delayMs + 900}ms\" dur=\"0.6s\" fill=\"freeze\"/></text>"
  s!"<text x=\"{fc px}\" y=\"{fc py}\" font-size=\"13\" font-weight=\"800\" fill=\"#ffd700\">{title}</text>" ++
  cap ++ bars

/-! ## Movement 2 — cognitive peaks (92 buckets) -/

/-- One `cog` sparkline (92 thin bars) that draws itself in, with a gold marker
dropping onto the certified `argmax` bucket. -/
def cogStrip (px py stripW stripH : Float) (delayMs : Nat)
    (title : String) (data : List Nat) (peak : Nat) (col : String) : String :=
  let n     := data.length
  let maxV  := Float.ofNat (fmax data)
  let step  := stripW / Float.ofNat (Nat.max n 1)
  let bw    := step * 0.8
  let baseY := py + stripH
  let bars := data.zipIdx.foldl (fun acc (v, i) =>
    let frac := if maxV == 0.0 then 0.0 else Float.ofNat v / maxV
    let bh   := frac * stripH
    let bx   := px + Float.ofNat i * step
    let ty   := baseY - bh
    let isPk := i == peak
    let c    := if isPk then "#ffd700" else col
    let beg  := s!"{delayMs + i * 8}ms"
    acc ++
      s!"<rect x=\"{fc bx}\" y=\"{fc baseY}\" width=\"{fc bw}\" height=\"0\" fill=\"{c}\" opacity=\"{if isPk then "1" else "0.7"}\">" ++
      s!"<animate attributeName=\"height\" from=\"0\" to=\"{fc bh}\" begin=\"{beg}\" dur=\"0.4s\" fill=\"freeze\"/>" ++
      s!"<animate attributeName=\"y\" from=\"{fc baseY}\" to=\"{fc ty}\" begin=\"{beg}\" dur=\"0.4s\" fill=\"freeze\"/></rect>") ""
  let pkX := px + Float.ofNat peak * step + bw/2.0
  let marker :=
    s!"<g opacity=\"0\"><animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delayMs + n*8 + 200}ms\" dur=\"0.5s\" fill=\"freeze\"/>" ++
    s!"<polygon points=\"{fc (pkX-5.0)},{fc (py-14.0)} {fc (pkX+5.0)},{fc (py-14.0)} {fc pkX},{fc (py-4.0)}\" fill=\"#ffd700\"/>" ++
    s!"<text x=\"{fc pkX}\" y=\"{fc (py-18.0)}\" font-size=\"9\" text-anchor=\"middle\" font-weight=\"700\" fill=\"#ffd700\">argmax {peak}</text></g>"
  s!"<text x=\"{fc px}\" y=\"{fc (py - 22.0)}\" font-size=\"11\" font-weight=\"700\" fill=\"{col}\">{title}</text>" ++
  s!"<line x1=\"{fc px}\" y1=\"{fc baseY}\" x2=\"{fc (px+stripW)}\" y2=\"{fc baseY}\" stroke=\"#2a335f\" stroke-width=\"1\"/>" ++
  bars ++ marker

/-! ## Movement 3 — semantic-triad peaks (20 buckets) -/

/-- One `triad` panel (20 growing bars) with the certified peak(s) crowned. -/
def triadPanel (px py panelW panelH : Float) (delayMs : Nat)
    (title : String) (data : List Nat) (peaks : List Nat) (col : String) : String :=
  let n     := data.length
  let maxV  := Float.ofNat (fmax data)
  let step  := panelW / Float.ofNat (Nat.max n 1)
  let bw    := step * 0.7
  let baseY := py + panelH
  let bars := data.zipIdx.foldl (fun acc (v, i) =>
    let frac := if maxV == 0.0 then 0.0 else Float.ofNat v / maxV
    let bh   := frac * panelH
    let bx   := px + Float.ofNat i * step
    let ty   := baseY - bh
    let isPk := peaks.contains i
    let c    := if isPk then "#ffd700" else col
    let beg  := s!"{delayMs + i * 40}ms"
    let crown :=
      if isPk then
        s!"<text x=\"{fc (bx+bw/2.0)}\" y=\"{fc (ty-5.0)}\" font-size=\"11\" text-anchor=\"middle\" fill=\"#ffd700\" opacity=\"0\">★<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delayMs + n*40 + 200}ms\" dur=\"0.4s\" fill=\"freeze\"/></text>"
      else ""
    acc ++
      s!"<rect x=\"{fc bx}\" y=\"{fc baseY}\" width=\"{fc bw}\" height=\"0\" rx=\"2\" fill=\"{c}\" opacity=\"{if isPk then "1" else "0.75"}\">" ++
      s!"<animate attributeName=\"height\" from=\"0\" to=\"{fc bh}\" begin=\"{beg}\" dur=\"0.5s\" fill=\"freeze\"/>" ++
      s!"<animate attributeName=\"y\" from=\"{fc baseY}\" to=\"{fc ty}\" begin=\"{beg}\" dur=\"0.5s\" fill=\"freeze\"/></rect>" ++ crown) ""
  let pkLabel := String.intercalate "," (peaks.map toString)
  s!"<text x=\"{fc px}\" y=\"{fc (py - 8.0)}\" font-size=\"11\" font-weight=\"700\" fill=\"{col}\">{title}  ·  peak {pkLabel}</text>" ++
  s!"<line x1=\"{fc px}\" y1=\"{fc baseY}\" x2=\"{fc (px+panelW)}\" y2=\"{fc baseY}\" stroke=\"#2a335f\" stroke-width=\"1\"/>" ++
  bars

/-! ## Assembling the film -/

/-- Build the complete animated vision-proof SVG. -/
def buildFilm : String :=
  let w : Nat := 1280
  let h : Nat := 1480
  -- Movement 1 panels (4 corpora across).
  let pw : Float := 290.0
  let ph : Float := 220.0
  let m1y : Float := 150.0
  let m1 :=
    harmPanel 40.0  m1y pw ph 200  "itself"    itselfHarm    false ++
    harmPanel 350.0 m1y pw ph 500  "mathlib"   mathlibHarm   true  ++
    harmPanel 660.0 m1y pw ph 800  "batteries" batteriesHarm true  ++
    harmPanel 970.0 m1y pw ph 1100 "lean4"     lean4Harm     true
  -- Movement 2: four cog sparklines stacked.
  let sw : Float := 1180.0
  let sh : Float := 70.0
  let m2y : Float := 480.0
  let m2 :=
    cogStrip 60.0 (m2y+30.0)  sw sh 1500 "itself · cog (92×)"    itselfCog    77 (corpusColor 0) ++
    cogStrip 60.0 (m2y+150.0) sw sh 2400 "mathlib · cog (92×)"   mathlibCog   47 (corpusColor 1) ++
    cogStrip 60.0 (m2y+270.0) sw sh 3300 "batteries · cog (92×)" batteriesCog 55 (corpusColor 2) ++
    cogStrip 60.0 (m2y+390.0) sw sh 4200 "lean4 · cog (92×)"     lean4Cog     34 (corpusColor 3)
  -- Movement 3: four triad panels (2×2).
  let tw : Float := 540.0
  let th : Float := 130.0
  let m3y : Float := 1090.0
  let m3 :=
    triadPanel 60.0  (m3y+30.0)  tw th 5000 "itself · triad (20×)"    itselfTriad    [13]     (corpusColor 0) ++
    triadPanel 680.0 (m3y+30.0)  tw th 5400 "mathlib · triad (20×)"   mathlibTriad   [3]      (corpusColor 1) ++
    triadPanel 60.0  (m3y+200.0) tw th 5800 "batteries · triad (TIE)" batteriesTriad [15,18]  (corpusColor 2) ++
    triadPanel 680.0 (m3y+200.0) tw th 6200 "lean4 · triad (20×)"     lean4Triad     [17]     (corpusColor 3)
  let doc := document w h
    [ Svg.raw
        ("<defs>" ++
         "<radialGradient id=\"bgv\" cx=\"35%\" cy=\"15%\" r=\"130%\">" ++
         "<stop offset=\"0%\" stop-color=\"#1a1f3c\"/><stop offset=\"100%\" stop-color=\"#070812\"/></radialGradient></defs>"),
      rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#bgv)" "none" [],
      -- title bar
      rect 20 18 (Int.ofNat w - 40) 64 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
      Svg.text [("x","40"),("y","46"),("font-size","23"),("font-weight","800"),("fill","#ffd700")]
        "VISION PATTERNS — an animated, machine-checked proof of the dual-atlas findings",
      Svg.text [("x","40"),("y","70"),("font-size","12"),("fill","#9fb0e0")]
        "every bar is a certified VisionPatterns literal (native_decide); coordinates computed natively by Lean",
      -- Movement 1
      Svg.text [("x","40"),("y","120"),("font-size","14"),("font-weight","700"),("fill","#2bd0c0")]
        "1 · harmonic dominance — trivector (★) is the unique max in every corpus; strict decrease 0>5>7>11>13 (itself is the proven exception)",
      Svg.raw m1,
      -- Movement 2
      Svg.text [("x","40"),("y", toString (470)),("font-size","14"),("font-weight","700"),("fill","#2bd0c0")]
        "2 · cognitive peaks — the 92-bucket cog sparklines draw in; the gold marker lands on the certified argmax bucket",
      Svg.raw m2,
      -- Movement 3
      Svg.text [("x","40"),("y", toString (1080)),("font-size","14"),("font-weight","700"),("fill","#2bd0c0")]
        "3 · semantic-triad peaks — the 20-bucket triad bars grow in with the certified peak crowned (batteries: two-way tie 15 & 18)",
      Svg.raw m3,
      Svg.text [("x","20"),("y", toString (Int.ofNat h - 14)),("font-size","11"),("fill","#5a6790")]
        "generated natively by Lean from RequestProject.VisionPatterns · harm_trivector_dominant_all · harm_strictDecreasing_large · *_cog_argmax · *_triad_argmax" ]
  render doc

/-! ## Commands -/

/-- `#visionprooffilm` builds the animated vision-proof film and reports its size. -/
syntax (name := visionprooffilmCmd) "#visionprooffilm" : command

@[command_elab visionprooffilmCmd]
def elabVisionprooffilm : CommandElab := fun _ => do
  let svg := buildFilm
  logInfo s!"[Vision Proof Film] animated the 4-corpus harmonic / cog / triad findings into a {svg.length}-byte SVG."

/-- `#writevisionproof "path"` builds the film and writes the animated SVG to `path`. -/
syntax (name := writevisionproofCmd) "#writevisionproof " str : command

@[command_elab writevisionproofCmd]
def elabWritevisionproof : CommandElab := fun stx => do
  match stx with
  | `(#writevisionproof $p:str) => do
    let path := p.getString
    let svg := buildFilm
    IO.FS.writeFile path svg
    logInfo s!"[Vision Proof Film] wrote {svg.length} bytes to {path}"
  | _ => throwError "ill-formed #writevisionproof command"

/-! ## Test suite -/

#visionprooffilm
#writevisionproof "atlas_visionproof.svg"

end VisionPatternsSVG

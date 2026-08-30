import RequestProject.DualAtlas
import RequestProject.SVG
import Lean

/-!
# DualAtlasSVG: the dual-atlas coordinate functor, *as an animation*

This layer turns the `DualAtlas` construction into a single self-contained,
self-playing **animated SVG**.  Everything it draws is computed natively by
Lean from the same definitions the proofs use (`DualAtlas.dualizePair` via
`primalAtlas`/`dualAtlas`, `cogProj`, `triadProj`, `harmCode`/`harmLabel`),
so the picture is faithful to the formalised mathematics.

The film has four animated movements:

1. **Dualization** — the six structured prime powers `p^e` of `|𝕄|` flip to
   their duals `e^p` (`2^46 ↦ 46^2`, …), the involution `dualFunctor` made
   visible.  An arrow pulses back and forth, recalling
   `dualFunctor_involutive` (dualizing twice is the identity).
2. **Cognitive grid (46×2)** — the `92`-cell grid of `cogProj`; reflected
   declarations drop into their cognitive cell `(h % 92) + 1`.
3. **Semantic triad (20×3)** — the `20`-lane recursion of `triadProj`;
   markers slide to `⌊(h % 60)/3⌋`.
4. **Harmonic classifier** — the priority wheel `13 > 11 > 7 > 5 > default`
   of `harmCode`, with each reflected declaration's cell lighting up.

Commands:

* `#dualfilm`              — build the film for the featured examples, report size.
* `#writedualatlas "path"` — build the film and write the SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace DualAtlasSVG

open DualAtlas

/-- The declarations featured in the film. -/
def featured : List Name :=
  [`Nat.add, `List.map, `Prod.fst,
   `DualAtlas.dualFunctor, `Holograms.dualizePair, `AristoTask.primalCoord]

/-- Per-prime colour for the six structured prime powers (warm → cool). -/
def primeColor : Nat → String
  | 2  => "#ff5db1"
  | 3  => "#ff7a59"
  | 5  => "#ffd23d"
  | 7  => "#4fd86a"
  | 11 => "#2bb6ff"
  | 13 => "#8a6bff"
  | _  => "#9aa3b8"

/-- Per-declaration marker colour (by index). -/
def markColor : Nat → String
  | 0 => "#ff5db1" | 1 => "#ffd23d" | 2 => "#4fd86a"
  | 3 => "#2bb6ff" | 4 => "#c45dff" | _ => "#ff7a59"

/-- Short tag for a declaration name (last component), for compact labels. -/
def shortName (n : Name) : String := n.toString

/-! ## Movement 1 — the dualization flip cards -/

/-- One flip card for the prime power `p^e ↦ e^p` at column `idx`. -/
def flipCard (idx : Nat) (p e : Nat) : Svg :=
  let x : Int := 30 + (Int.ofNat idx) * 140
  let y : Int := 90
  let col := primeColor p
  let begin := s!"{idx * 250}ms"
  -- the original `p^e` text fades out, the dual `e^p` text fades in, on a loop
  group
    [ Svg.elem "rect"
        [("x", toString x), ("y", toString y), ("width","120"), ("height","120"),
         ("rx","14"), ("fill","#0c0f22"), ("stroke", col), ("stroke-width","2"),
         ("opacity","0")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{begin}\" dur=\"0.5s\" fill=\"freeze\"/>" ],
      -- original prime power
      Svg.elem "text"
        [("x", toString (x + 60)), ("y", toString (y + 60)),
         ("font-size","30"), ("font-weight","800"), ("text-anchor","middle"),
         ("fill", col), ("opacity","0")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0;1;1;0;0\" keyTimes=\"0;0.1;0.45;0.55;1\" begin=\"{begin}\" dur=\"4s\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"{p}<tspan baseline-shift=\"super\" font-size=\"18\">{e}</tspan>" ],
      -- dualized prime power
      Svg.elem "text"
        [("x", toString (x + 60)), ("y", toString (y + 60)),
         ("font-size","30"), ("font-weight","800"), ("text-anchor","middle"),
         ("fill","#ffd700"), ("opacity","0")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0;0;1;1;0\" keyTimes=\"0;0.55;0.65;0.9;1\" begin=\"{begin}\" dur=\"4s\" repeatCount=\"indefinite\"/>",
          Svg.raw s!"{e}<tspan baseline-shift=\"super\" font-size=\"18\">{p}</tspan>" ],
      -- the dualization arrow, pulsing
      Svg.elem "text"
        [("x", toString (x + 60)), ("y", toString (y + 100)),
         ("font-size","16"), ("text-anchor","middle"), ("fill","#9fb0e0")]
        [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0.3;1;0.3\" begin=\"{begin}\" dur=\"2s\" repeatCount=\"indefinite\"/>",
          Svg.raw "p&#8319; &#8596; e&#7510;" ] ]
    []

/-- All six flip cards drawn from `primalAtlas`. -/
def flipRow : List Svg :=
  primalAtlas.zipIdx.map (fun ((p, e), i) => flipCard i p e)

/-! ## Movement 2 — the cognitive 46×2 grid -/

/-- The empty `46×2` cognitive grid (92 cells), with featured markers dropping in. -/
def cognitiveGrid (items : List (Name × Nat)) (y0 : Int) : Svg :=
  let cellW : Int := 18
  let cellH : Int := 20
  let gx : Int := 30
  -- the 92 background cells
  let cells := (List.range 92).map (fun k =>
    let col : Int := Int.ofNat (k % 46)
    let row : Int := Int.ofNat (k / 46)
    rect (gx + col * cellW) (y0 + row * cellH) (cellW - 2) (cellH - 2)
      "#10142c" "#2a335f" [("rx","2")])
  -- markers for the featured declarations
  let marks := items.zipIdx.map (fun ((_, h), i) =>
    let cog := DualAtlas.cogProj h           -- 1 ≤ cog ≤ 92
    let k := cog - 1
    let col : Int := Int.ofNat (k % 46)
    let row : Int := Int.ofNat (k / 46)
    let cx : Int := gx + col * cellW + (cellW - 2) / 2
    let cyTo : Int := y0 + row * cellH + (cellH - 2) / 2
    let begin := s!"{1000 + i * 350}ms"
    Svg.elem "circle"
      [("cx", toString cx), ("cy", toString cyTo), ("r","6"),
       ("fill", markColor i), ("stroke","#fff"), ("stroke-width","1"),
       ("opacity","0")]
      [ Svg.raw s!"<animate attributeName=\"cy\" from=\"{cyTo - 40}\" to=\"{cyTo}\" begin=\"{begin}\" dur=\"0.6s\" fill=\"freeze\" calcMode=\"spline\" keySplines=\"0.3 0 0.2 1\" keyTimes=\"0;1\"/>",
        Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{begin}\" dur=\"0.4s\" fill=\"freeze\"/>" ])
  group (cells ++ marks) []

/-! ## Movement 3 — the semantic 20-lane triad recursion -/

/-- The `20`-lane semantic triad strip, markers sliding to `triadProj`. -/
def triadStrip (items : List (Name × Nat)) (y0 : Int) : Svg :=
  let laneW : Int := 41
  let gx : Int := 30
  let lanes := (List.range 20).map (fun k =>
    let lx : Int := gx + Int.ofNat k * laneW
    group
      [ rect lx y0 (laneW - 3) 36 "#10142c" "#2a335f" [("rx","3")],
        Svg.text [("x", toString (lx + (laneW - 3)/2)), ("y", toString (y0 + 23)),
                  ("font-size","11"), ("text-anchor","middle"), ("fill","#5a6790")]
          (toString k) ] [])
  let marks := items.zipIdx.map (fun ((_, h), i) =>
    let t := DualAtlas.triadProj h           -- 0 ≤ t ≤ 19
    let lx : Int := gx + Int.ofNat t * laneW + (laneW - 3)/2
    let cy : Int := y0 + 18
    let begin := s!"{1500 + i * 300}ms"
    Svg.elem "circle"
      [("cx", toString lx), ("cy", toString cy), ("r","7"),
       ("fill", markColor i), ("stroke","#fff"), ("stroke-width","1"),
       ("opacity","0")]
      [ Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"0.92\" begin=\"{begin}\" dur=\"0.4s\" fill=\"freeze\"/>",
        Svg.raw s!"<animate attributeName=\"r\" values=\"3;9;7\" begin=\"{begin}\" dur=\"0.5s\" fill=\"freeze\"/>" ])
  group (lanes ++ marks) []

/-! ## Movement 4 — the harmonic classifier wheel -/

/-- The harmonic-cell rows of the priority classifier, lit by featured decls. -/
def harmonicRows (items : List (Name × Nat)) (y0 : Int) : Svg :=
  let rows : List (Nat × String × String) :=
    [ (13, "Recursion (3^13)",  primeColor 13),
      (11, "Hemispheres (2^11)", primeColor 11),
      (7,  "Heptad (6^7)",       primeColor 7),
      (5,  "Muse Cycle (9^5)",   primeColor 5),
      (0,  "Trivector Default",  "#9aa3b8") ]
  -- count how many featured decls fall in each harmonic code
  let codeOf (h : Nat) : Nat := DualAtlas.harmCode h
  let rowSvgs := rows.zipIdx.map (fun ((code, label, col), j) =>
    let ry : Int := y0 + Int.ofNat j * 34
    let hits := items.filter (fun (_, h) => codeOf h == code)
    let begin := s!"{2200 + j * 200}ms"
    group
      ([ Svg.elem "rect"
           [("x","30"), ("y", toString ry), ("width","430"), ("height","28"),
            ("rx","6"), ("fill","#10142c"), ("stroke", col), ("stroke-width","2"),
            ("opacity","0.35")]
           [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0.35;0.9;0.35\" begin=\"{begin}\" dur=\"2.5s\" repeatCount=\"indefinite\"/>" ],
         Svg.text [("x","44"), ("y", toString (ry + 19)), ("font-size","13"),
                   ("font-weight","700"), ("fill", col)] label ]
       ++ hits.zipIdx.map (fun ((nm, _), k) =>
            let cx : Int := 480 + Int.ofNat k * 150
            Svg.text [("x", toString cx), ("y", toString (ry + 19)),
                      ("font-size","11"), ("fill","#cfd8f5")] (shortName nm)))
      [])
  group rowSvgs []

/-! ## Assembling the film -/

/-- Build the complete animated dual-atlas SVG for the reflected `items`. -/
def buildFilm (items : List (Name × Nat)) : String :=
  let h : Nat := 760
  let doc := document 900 h
    ([ Svg.raw ("<defs><radialGradient id=\"bgd\" cx=\"50%\" cy=\"0%\" r=\"110%\">" ++
        "<stop offset=\"0%\" stop-color=\"#1a1f3c\"/><stop offset=\"100%\" stop-color=\"#070812\"/></radialGradient></defs>"),
       rect 0 0 900 (Int.ofNat h) "url(#bgd)" "none" [],
       -- title bar
       rect 20 18 860 56 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x","40"),("y","44"),("font-size","22"),("font-weight","800"),
                 ("fill","#ffd700")] "DUAL-ATLAS FUNCTOR — p^e ↦ e^p, animated",
       Svg.text [("x","40"),("y","65"),("font-size","12"),("fill","#9fb0e0")]
         "the involution dualizes every structured prime power of |𝕄|; coordinates are computed natively by Lean",
       -- Movement 1
       Svg.text [("x","30"),("y","90"),("font-size","13"),("font-weight","700"),
                 ("fill","#2bd0c0")] "1 · dualization (dualFunctor is involutive)" ]
     ++ flipRow
     ++ [ -- Movement 2
          Svg.text [("x","30"),("y","250"),("font-size","13"),("font-weight","700"),
                    ("fill","#2bd0c0")] "2 · cognitive grid 46×2 — cog = (h mod 92) + 1",
          cognitiveGrid items 262 ]
     ++ [ -- Movement 3
          Svg.text [("x","30"),("y","350"),("font-size","13"),("font-weight","700"),
                    ("fill","#2bd0c0")] "3 · semantic triad 20×3 — triad = ⌊(h mod 60)/3⌋",
          triadStrip items 360 ]
     ++ [ -- Movement 4
          Svg.text [("x","30"),("y","440"),("font-size","13"),("font-weight","700"),
                    ("fill","#2bd0c0")] "4 · harmonic classifier — priority 13 > 11 > 7 > 5 > default",
          harmonicRows items 452 ]
     ++ [ -- legend of featured declarations
          Svg.text [("x","30"),("y","640"),("font-size","12"),("font-weight","700"),
                    ("fill","#cfd8f5")] "featured declarations" ]
     ++ items.zipIdx.map (fun ((nm, _), i) =>
          let lx : Int := 30 + Int.ofNat i * 145
          group
            [ circle (lx + 6) 658 6 (markColor i) "#fff" [("stroke-width","1")],
              Svg.text [("x", toString (lx + 18)),("y","662"),("font-size","11"),
                        ("fill","#9fb0e0")] (shortName nm) ] [])
     ++ [ Svg.text [("x","20"),("y", toString (Int.ofNat h - 14)),("font-size","11"),
                    ("fill","#5a6790")]
            "generated natively by Lean · faithful cogProj/triadProj/harmCode projections · #writedualatlas" ])
  render doc

/-- Reflect the featured declarations into `(name, hash)` pairs. -/
def gatherFeatured : CommandElabM (List (Name × Nat)) := do
  let env ← getEnv
  let mut out : List (Name × Nat) := []
  for nm in featured do
    match env.find? nm with
    | some info =>
      match info.value? with
      | some e => out := (nm, e.hash.toNat) :: out
      | none   => pure ()
    | none => pure ()
  return out.reverse

/-! ## Commands -/

/-- `#dualfilm` builds the animated dual-atlas film and reports its size. -/
syntax (name := dualfilmCmd) "#dualfilm" : command

@[command_elab dualfilmCmd]
def elabDualfilm : CommandElab := fun _ => do
  let items ← gatherFeatured
  let svg := buildFilm items
  logInfo s!"[Dual Atlas Film] animated {items.length} reflected declarations into a {svg.length}-byte SVG."

/-- `#writedualatlas "path"` builds the film and writes the SVG file to `path`. -/
syntax (name := writedualatlasCmd) "#writedualatlas " str : command

@[command_elab writedualatlasCmd]
def elabWritedualatlas : CommandElab := fun stx => do
  match stx with
  | `(#writedualatlas $p:str) => do
    let path := p.getString
    let items ← gatherFeatured
    let svg := buildFilm items
    IO.FS.writeFile path svg
    logInfo s!"[Dual Atlas Film] wrote {svg.length} bytes ({items.length} declarations) to {path}"
  | _ => throwError "ill-formed #writedualatlas command"

/-! ## Test suite -/

#dualfilm
#writedualatlas "atlas_dual.svg"

end DualAtlasSVG

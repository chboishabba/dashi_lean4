import RequestProject.Introspect
import RequestProject.SVG
import Lean

/-!
# IntrospectSVG: the SVG + animation layer (the introspective comic book)

This layer turns the introspective projection of the *entire source code* into a
single self-contained **animated 2D/3D SVG comic book** that shows where each
declaration lands in the dual atlas.

The comic has four regions:

1. a comic title banner;
2. the **2D atlas hero panel** — cognitive axis (`cog`, 46×2) horizontally,
   semantic axis (`triad`, 20×3) vertically, one animated marker per declaration,
   colour-coded by harmonic class and shaped by cognitive layer band;
3. the **3D isometric panel** — the same atlas projected isometrically with a
   harmonic `z`-lift and a gentle rotation animation;
4. three **chapter cells** — one comic page per module
   (`Holograms`, `AristoTask`, `DualAtlas`) with halftone backgrounds and a chip
   for every declaration in that module.

Animation is native SMIL (`<animate>` / `<animateTransform>`): staggered entrances
plus per-harmonic motion (recursion spirals/drifts, hemisphere oscillation, heptad
cycles, Muse pulses).

Commands:

* `#svgatlas`           — build the comic and report its size.
* `#writecomic "path"`  — build the comic and write the SVG file to `path`.
-/

open Lean Meta Elab Command SVG

namespace IntrospectSVG

open Introspect DualAtlas AristoTask

/-! ## Palette and geometry -/

/-- `(fill, glow)` colours per style class. -/
def colorOf : Nat → String × String
  | 4 => ("#8a2be2", "#d6b3ff")   -- recursion  → violet
  | 3 => ("#ffd700", "#fff2a8")   -- hemispheres → gold
  | 2 => ("#5e34c4", "#b79bff")   -- heptad     → indigo
  | 1 => ("#00c2c2", "#a8fbfb")   -- Muse       → teal
  | _ => ("#8a93a6", "#d6dce8")   -- trivector  → gray

/-- Cognitive *layer* (1..46) of a grid column `cog` (1..92). -/
def layerOf (cog : Nat) : Nat := ((cog - 1) / 2) + 1

/-- Unit polygons (coords ×1000) for the shape bands. -/
def hexUnit : List (Int × Int) :=
  [(0,-1000),(866,-500),(866,500),(0,1000),(-866,500),(-866,-500)]
def octUnit : List (Int × Int) :=
  [(383,-924),(924,-383),(924,383),(383,924),(-383,924),(-924,383),(-924,-383),(-383,-924)]
def starUnit : List (Int × Int) :=
  [(0,-1000),(224,-309),(951,-309),(363,118),(588,809),
   (0,382),(-588,809),(-363,118),(-951,-309),(-224,-309)]

/-- Render a polygon from a unit shape scaled by `r` and centred at `(cx,cy)`. -/
def polyAt (cx cy r : Int) (unit : List (Int × Int)) (fill stroke : String)
    (extra : List (String × String)) : Svg :=
  polygon (unit.map (fun (x, y) => (cx + x * r / 1000, cy + y * r / 1000)))
    fill stroke extra

/-- The marker shape for a declaration, chosen by its cognitive layer band:
rect (1–10), hexagon (11–20), octagon (21–30), circle (31–40), star (41–46). -/
def shapeAt (cx cy r : Int) (cog : Nat) (fill stroke : String)
    (extra : List (String × String)) : Svg :=
  let l := layerOf cog
  if l ≤ 10 then
    rect (cx - r) (cy - r) (2*r) (2*r) fill stroke (("rx","2") :: extra)
  else if l ≤ 20 then polyAt cx cy r hexUnit fill stroke extra
  else if l ≤ 30 then polyAt cx cy r octUnit fill stroke extra
  else if l ≤ 40 then circle cx cy r fill stroke extra
  else polyAt cx cy r starUnit fill stroke extra

/-! ## Per-harmonic motion -/

/-- SMIL motion fragment for a marker group, keyed by style class.  Plus a
staggered fade-in entrance keyed by `idx`. -/
def motionRaw (idx : Nat) (style : Nat) : String :=
  let begin := s!"{(idx % 64) * 4}" -- centiseconds → tenths below
  let delay := s!"0.{if (idx % 64) < 10 then s!"0{idx % 64}" else s!"{(idx % 64)}"}s"
  let entrance :=
    s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delay}\" dur=\"0.6s\" fill=\"freeze\"/>"
  let _ := begin
  let move :=
    match style with
    | 4 => -- recursion: slow inward/outward spiral drift
      "<animateTransform attributeName=\"transform\" type=\"translate\" additive=\"sum\" values=\"0 0; 3 -3; 0 -5; -3 -3; 0 0\" dur=\"6s\" repeatCount=\"indefinite\"/>"
    | 3 => -- hemispheres: left/right oscillation
      "<animateTransform attributeName=\"transform\" type=\"translate\" additive=\"sum\" values=\"-4 0; 4 0; -4 0\" dur=\"3.5s\" repeatCount=\"indefinite\"/>"
    | 2 => -- heptad: 7-step cycle
      "<animateTransform attributeName=\"transform\" type=\"rotate\" additive=\"sum\" values=\"0;360\" dur=\"7s\" repeatCount=\"indefinite\"/>"
    | 1 => -- Muse: rhythmic pulse
      "<animateTransform attributeName=\"transform\" type=\"scale\" additive=\"sum\" values=\"1;1.25;1\" dur=\"2.2s\" repeatCount=\"indefinite\"/>"
    | _ => "" -- trivector: static
  entrance ++ move

/-! ## 2D hero panel -/

def heroX (cog : Nat) : Int := 90 + (Int.ofNat (cog - 1)) * 900 / 91
def heroY (triad : Nat) : Int := 600 - (Int.ofNat triad) * 410 / 19

/-- One animated marker in the 2D hero panel. -/
def heroMarker (idx : Nat) (p : IntrospectivePanel) : Svg :=
  let (fill, glow) := colorOf p.style
  let cx := heroX p.dual.cog
  let cy := heroY p.dual.triad
  let r : Int := 5 + (Int.ofNat (p.primal.depth)) / 5
  group
    [ Svg.raw s!"<title>{SVG.esc p.name.toString} · cog {p.dual.cog} triad {p.dual.triad} · {styleName p.style}</title>",
      shapeAt cx cy (r+2) p.dual.cog "none" glow [("opacity","0.35")],
      shapeAt cx cy r p.dual.cog fill "#0b0c18" [("stroke-width","1")],
      Svg.raw (motionRaw idx p.style) ]
    []

/-! ## 3D isometric panel -/

def isoX (cog triad : Nat) : Int := 1330 + (Int.ofNat cog - Int.ofNat triad) * 3
def isoY (cog triad z : Nat) : Int :=
  255 + (Int.ofNat cog + Int.ofNat triad) * 2 - (Int.ofNat z) * 18

/-- One animated marker in the 3D isometric panel. -/
def isoMarker (idx : Nat) (p : IntrospectivePanel) : Svg :=
  let (fill, glow) := colorOf p.style
  let cx := isoX p.dual.cog p.dual.triad
  let cy := isoY p.dual.cog p.dual.triad p.z
  let baseY := isoY p.dual.cog p.dual.triad 0
  let r : Int := 4 + (Int.ofNat p.z)
  group
    [ -- z-lift stem from the floor
      line cx baseY cx cy glow [("stroke-width","1"),("opacity","0.4")],
      circle cx baseY 2 "#1b1f3a" "#3b4170" [],
      shapeAt cx cy (r+2) p.dual.cog "none" glow [("opacity","0.3")],
      shapeAt cx cy r p.dual.cog fill "#0b0c18" [("stroke-width","1")],
      Svg.raw s!"<title>{SVG.esc p.name.toString} · cog {p.dual.cog} triad {p.dual.triad} · z {p.z} · {styleName p.style}</title>",
      Svg.raw (motionRaw idx p.style) ]
    []

/-! ## Comic chrome (defs, banner, panels, chapter cells) -/

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"bg\" cx=\"50%\" cy=\"30%\" r=\"90%\">" ++
    "<stop offset=\"0%\" stop-color=\"#1a1f3c\"/><stop offset=\"100%\" stop-color=\"#070812\"/></radialGradient>" ++
  "<linearGradient id=\"banner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#ff5db1\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#5db1ff\"/></linearGradient>" ++
  "<pattern id=\"halftone\" width=\"10\" height=\"10\" patternUnits=\"userSpaceOnUse\">" ++
    "<rect width=\"10\" height=\"10\" fill=\"#11142a\"/><circle cx=\"3\" cy=\"3\" r=\"1.4\" fill=\"#222a52\"/></pattern>" ++
  "<filter id=\"soft\" x=\"-30%\" y=\"-30%\" width=\"160%\" height=\"160%\">" ++
    "<feGaussianBlur stdDeviation=\"2.2\"/></filter>" ++
  "</defs>"

/-- A jagged comic "burst" caption box (approximate spiky polygon). -/
def burst (cx cy r : Int) (fill stroke : String) : Svg :=
  let pts : List (Int × Int) :=
    [(0,-1000),(180,-420),(760,-640),(380,-130),(980,0),(380,130),
     (760,640),(180,420),(0,1000),(-180,420),(-760,640),(-380,130),
     (-980,0),(-380,-130),(-760,-640),(-180,-420)]
  polyAt cx cy r pts fill stroke [("stroke-width","2")]

def titleBanner : Svg :=
  group
    [ rect 30 24 1620 92 "url(#banner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","60"),("y","74"),("font-size","40"),("font-weight","800"),
                ("fill","#0b0c18"),("letter-spacing","2")]
        "ARISTO  ·  INTROSPECTIVE  ATLAS  COMIC",
      Svg.text [("x","62"),("y","104"),("font-size","17"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "the source code sees itself — every decl projected into the dual Monster-atlas (2D + 3D, animated)" ]

/-- Frame + axis labels for the 2D hero panel. -/
def heroFrame : Svg :=
  group
    [ rect 40 150 980 510 "#0c0f22" "#3a4a8a" [("rx","12"),("stroke-width","2")],
      Svg.text [("x","60"),("y","178"),("font-size","18"),("font-weight","700"),
                ("fill","#ffd700")] "PANEL I — THE ATLAS (2D)",
      Svg.text [("x","430"),("y","648"),("font-size","13"),("fill","#9fb0e0")]
        "Cognitive Manifold  →  cog (46×2)",
      Svg.elem "g"
        [("transform","rotate(-90 24 400)")]
        [Svg.text [("x","-120"),("y","30"),("font-size","13"),("fill","#9fb0e0")]
          "Semantic Triads  →  triad (20×3)"] ]

/-- Frame for the 3D isometric panel. -/
def isoFrame : Svg :=
  group
    [ rect 1040 150 610 510 "#0c0f22" "#3a4a8a" [("rx","12"),("stroke-width","2")],
      Svg.text [("x","1060"),("y","178"),("font-size","18"),("font-weight","700"),
                ("fill","#ffd700")] "PANEL II — ISOMETRIC (3D)",
      Svg.text [("x","1060"),("y","648"),("font-size","13"),("fill","#9fb0e0")]
        "z-lift = harmonic class · gentle auto-rotation" ]

/-- Legend chip for one harmonic class. -/
def legendChip (x y : Int) (style : Nat) (label : String) : Svg :=
  let (fill, _) := colorOf style
  group
    [ rect x y 14 14 fill "#0b0c18" [("rx","3")],
      Svg.text [("x", toString (x+22)),("y", toString (y+12)),("font-size","12"),
                ("fill","#cfd8f5")] label ]

def legend : Svg :=
  group
    [ legendChip 60 196 4 "Recursion (3^13) · violet · star/spiral",
      legendChip 60 216 3 "Hemispheres (2^11) · gold · oscillate",
      legendChip 320 196 2 "Heptad (6^7) · indigo · 7-cycle",
      legendChip 320 216 1 "Muse Cycle (9^5) · teal · pulse",
      legendChip 580 196 0 "Trivector · gray · static" ]

/-- Drop the leading module component of a declaration name. -/
def shortName (s : String) : String :=
  String.intercalate "." ((s.splitOn ".").drop 1)

/-- A single chapter comic cell for `modName`: a header burst plus a two-column
"cast list" with one coloured chip + name per declaration in that module. -/
def chapterCell (i : Nat) (modName subtitle : String)
    (panels : List IntrospectivePanel) : Svg :=
  let x : Int := 40 + (Int.ofNat i) * 543
  let y : Int := 690
  let w : Int := 513
  let h : Int := 330
  let n := panels.length
  let rows : Nat := (n + 1) / 2
  let entries := (panels.zipIdx.map (fun (p, j) =>
    let col := Int.ofNat (j / rows)
    let row := Int.ofNat (j % rows)
    let cx := x + 20 + col * 250
    let cy := y + 86 + row * 14
    let (fill, _) := colorOf p.style
    group
      [ shapeAt (cx+5) (cy-3) 5 p.dual.cog fill "#0b0c18" [("stroke-width","1")],
        Svg.text [("x", toString (cx+15)),("y", toString cy),("font-size","8"),
                  ("fill","#cfd8f5")]
          (shortName p.name.toString),
        Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{i}.{j % 10}s\" dur=\"0.5s\" fill=\"freeze\"/>" ]
      []))
  group
    ([ rect x y w h "url(#halftone)" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       rect x y w 40 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x", toString (x+18)),("y", toString (y+27)),("font-size","18"),
                 ("font-weight","800"),("fill","#ffd700")]
         s!"CH.{i+1} — {modName}",
       Svg.text [("x", toString (x+18)),("y", toString (y+62)),("font-size","12"),
                 ("fill","#9fb0e0")]
         s!"{subtitle}  ·  {n} decls" ] ++ entries)

/-! ## Assembling the comic -/

/-- Build the full animated comic SVG document string for a panel list. -/
def buildComic (panels : List IntrospectivePanel) : String :=
  let holo := panels.filter (·.name.toString.startsWith "Holograms.")
  let arist := panels.filter (·.name.toString.startsWith "AristoTask.")
  let dual := panels.filter (·.name.toString.startsWith "DualAtlas.")
  let heroMarkers := group (panels.zipIdx.map (fun (p, i) => heroMarker i p))
  let isoMarkers :=
    Svg.elem "g"
      [("transform","rotate(0 1330 400)")]
      ([ Svg.raw "<animateTransform attributeName=\"transform\" type=\"rotate\" values=\"-4 1330 400; 4 1330 400; -4 1330 400\" dur=\"9s\" repeatCount=\"indefinite\"/>" ]
        ++ panels.zipIdx.map (fun (p, i) => isoMarker i p))
  let doc := document 1680 1040
    [ Svg.raw defsRaw,
      rect 0 0 1680 1040 "url(#bg)" "none" [],
      titleBanner,
      heroFrame, legend, heroMarkers,
      isoFrame, isoMarkers,
      chapterCell 0 "Holograms" "Foundations of the world" holo,
      chapterCell 1 "AristoTask" "The primal atlas" arist,
      chapterCell 2 "DualAtlas" "The mirror world" dual,
      Svg.text [("x","40"),("y","1034"),("font-size","11"),("fill","#5a6790")]
        "generated natively by Lean · faithful e.hash.toNat projection · #writecomic" ]
  render doc

/-! ## Commands -/

/-- `#svgatlas` builds the comic from the whole project and reports its size. -/
syntax (name := svgatlasCmd) "#svgatlas" : command

@[command_elab svgatlasCmd]
def elabSvgatlas : CommandElab := fun _ => do
  let panels ← projectProject
  let svg := buildComic panels
  logInfo s!"[Introspective Comic] rendered {panels.length} declarations into a {svg.length}-byte animated 2D/3D SVG."

/-- `#writecomic "path"` builds the comic and writes the SVG file to `path`. -/
syntax (name := writecomicCmd) "#writecomic " str : command

@[command_elab writecomicCmd]
def elabWritecomic : CommandElab := fun stx => do
  match stx with
  | `(#writecomic $p:str) => do
    let path := p.getString
    let panels ← projectProject
    let svg := buildComic panels
    IO.FS.writeFile path svg
    logInfo s!"[Introspective Comic] wrote {svg.length} bytes ({panels.length} decls) to {path}"
  | _ => throwError "ill-formed #writecomic command"

/-! ## Test suite -/

#introspect Nat.add
#introspect List.map
#introspect Prod.fst

#atlasmap

#svgatlas

end IntrospectSVG

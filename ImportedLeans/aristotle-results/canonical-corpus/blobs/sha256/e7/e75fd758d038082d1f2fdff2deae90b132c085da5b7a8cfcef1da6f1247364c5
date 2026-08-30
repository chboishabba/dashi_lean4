import RequestProject.IntrospectSVG

/-!
# AtlasGuide: the minimap + motion-gallery overview page

The introspective comic (`IntrospectSVG`) is busy: dozens of markers entering,
drifting, oscillating, spinning and pulsing all at once.  This module adds a
single companion page that answers two questions at a glance:

1. **What is everything?** — a compact **minimap** that plots *every* declaration
   of the project as one coloured dot in the dual atlas (cognitive axis `cog`
   horizontally, semantic axis `triad` vertically), together with an inventory
   panel counting decls per harmonic class and per module.

2. **What is moving?** — a **motion gallery**: one comic strip per *moving thing*
   in the animated comic.  Each strip shows a *live* animated example on the
   left, then a **key-frame sequence** (a row of film cells freezing the
   animation at successive keyframes), and a plain-language explanation plus the
   exact SMIL it corresponds to.

Everything is emitted natively by Lean as one self-contained, animated SVG.

Commands:

* `#minimap`                 — build the page and report its size / inventory.
* `#writeguide "path"`       — build the page and write the SVG file to `path`.
-/

open Lean Meta Elab Command SVG

namespace AtlasGuide

open Introspect DualAtlas AristoTask IntrospectSVG

/-! ## Small numeric formatting helpers -/

/-- Left-pad a `Nat` to (at least) 3 digits with zeros. -/
def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length ≥ 3 then s else String.ofList (List.replicate (3 - s.length) '0') ++ s

/-- Format a per-mille scale (`1000` = `1.0`) as a decimal string. -/
def scaleStr (sc : Nat) : String := s!"{sc / 1000}.{pad3 (sc % 1000)}"

/-- Format a per-mille opacity (`1000` = `1.0`) as a decimal string. -/
def opStr (op : Nat) : String := s!"{op / 1000}.{pad3 (op % 1000)}"

/-! ## Glyphs -/

/-- A marker glyph centred at the origin (so a wrapping `transform` rotates and
scales it about its own centre). -/
def glyph0 (r : Int) (style : Nat) : Svg :=
  let (fill, glow) := colorOf style
  group
    [ polyAt 0 0 (r + 2) starUnit "none" glow [("opacity", "0.4")],
      polyAt 0 0 r starUnit fill "#0b0c18" [("stroke-width", "1")] ]

/-! ## The motion catalogue -/

/-- One frozen keyframe of an animation, rendered as a static transformed glyph. -/
structure KFrame where
  dx    : Int := 0
  dy    : Int := 0
  rot   : Int := 0
  scale : Nat := 1000
  op    : Nat := 1000
  label : String := ""

/-- One *moving thing*: its name, meaning, the literal SMIL it uses, a colour
class, a looping live-demo SMIL fragment, and its key-frame sequence. -/
structure MSpec where
  title    : String
  meaning  : String
  smilText : String
  style    : Nat
  liveSmil : String
  frames   : List KFrame

/-- The catalogue of every animated element in the introspective comic. -/
def motions : List MSpec :=
  [ { title := "Entrance — staggered fade-in"
    , meaning := "Every marker enters opacity 0 to 1, delayed by its index, so the whole atlas draws itself one declaration at a time."
    , smilText := "animate opacity 0 -> 1, begin = idx*0.01s, dur 0.6s, freeze"
    , style := 0
    , liveSmil := "<animate attributeName=\"opacity\" values=\"0;1;1;0\" keyTimes=\"0;0.3;0.85;1\" dur=\"2.5s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { op := 0,    label := "0%" },
          { op := 250,  label := "25%" },
          { op := 500,  label := "50%" },
          { op := 750,  label := "75%" },
          { op := 1000, label := "100%" } ] }
  , { title := "Recursion (3^13) — spiral drift"
    , meaning := "The 13-divisible deep-recursion cells drift in a slow inward/outward spiral, wandering up and back to home."
    , smilText := "translate values 0 0; 3 -3; 0 -5; -3 -3; 0 0, dur 6s, loop"
    , style := 4
    , liveSmil := "<animateTransform attributeName=\"transform\" type=\"translate\" additive=\"sum\" values=\"0 0; 12 -12; 0 -20; -12 -12; 0 0\" dur=\"6s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { dx := 0,   dy := 0,   label := "0s" },
          { dx := 12,  dy := -12, label := "1.5s" },
          { dx := 0,   dy := -20, label := "3s" },
          { dx := -12, dy := -12, label := "4.5s" },
          { dx := 0,   dy := 0,   label := "6s" } ] }
  , { title := "Hemispheres (2^11) — oscillation"
    , meaning := "The 11-divisible two-hemisphere cells rock side to side, sweeping left then right then back."
    , smilText := "translate values -4 0; 4 0; -4 0, dur 3.5s, loop"
    , style := 3
    , liveSmil := "<animateTransform attributeName=\"transform\" type=\"translate\" additive=\"sum\" values=\"-16 0; 16 0; -16 0\" dur=\"3.5s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { dx := -16, label := "0s" },
          { dx := 0,   label := "0.9s" },
          { dx := 16,  label := "1.75s" },
          { dx := 0,   label := "2.6s" },
          { dx := -16, label := "3.5s" } ] }
  , { title := "Heptad (6^7) — 7-phase rotation"
    , meaning := "The 7-divisible heptad cells turn through a full 360 degree rotation, shown here in its seven phases over 7 seconds."
    , smilText := "rotate values 0; 360, dur 7s, loop"
    , style := 2
    , liveSmil := "<animateTransform attributeName=\"transform\" type=\"rotate\" additive=\"sum\" values=\"0;360\" dur=\"7s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { rot := 0,   label := "1" },
          { rot := 51,  label := "2" },
          { rot := 103, label := "3" },
          { rot := 154, label := "4" },
          { rot := 206, label := "5" },
          { rot := 257, label := "6" },
          { rot := 309, label := "7" } ] }
  , { title := "Muse Cycle (9^5) — pulse"
    , meaning := "The 5-divisible Muse-cycle cells breathe, scaling 1 to 1.25 and back in a steady rhythm."
    , smilText := "scale values 1; 1.25; 1, dur 2.2s, loop"
    , style := 1
    , liveSmil := "<animateTransform attributeName=\"transform\" type=\"scale\" additive=\"sum\" values=\"1;1.25;1\" dur=\"2.2s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { scale := 1000, label := "x1.00" },
          { scale := 1125, label := "x1.12" },
          { scale := 1250, label := "x1.25" },
          { scale := 1125, label := "x1.12" },
          { scale := 1000, label := "x1.00" } ] }
  , { title := "Isometric panel — parallax sway"
    , meaning := "The entire 3D isometric panel sways plus/minus 4 degrees every 9 seconds, gently parallax-rotating the whole constellation."
    , smilText := "rotate values -4 1330 400; 4 1330 400; -4 1330 400, dur 9s, loop"
    , style := 4
    , liveSmil := "<animateTransform attributeName=\"transform\" type=\"rotate\" additive=\"sum\" values=\"-10;10;-10\" dur=\"9s\" repeatCount=\"indefinite\"/>"
    , frames :=
        [ { rot := -10, label := "0s" },
          { rot := -5,  label := "2.25s" },
          { rot := 0,   label := "4.5s" },
          { rot := 5,   label := "6.75s" },
          { rot := 10,  label := "9s" } ] } ]

/-! ## Rendering a key-frame sequence -/

/-- Render one frozen keyframe glyph at `(cx, cy)`. -/
def frameGlyph (cx cy r : Int) (style : Nat) (f : KFrame) : Svg :=
  group [ glyph0 r style ]
    [ ("transform",
       s!"translate({cx + f.dx},{cy + f.dy}) rotate({f.rot}) scale({scaleStr f.scale})"),
      ("opacity", opStr f.op) ]

/-- A single film cell (border + frozen glyph + frame number + label). -/
def filmCell (x y w h : Int) (style idx : Nat) (f : KFrame) : Svg :=
  let r : Int := min ((min w h) / 2 - 8) 18
  group
    [ rect x y w h "#0c1024" "#33407a" [("rx", "6")],
      Svg.text [("x", toString (x + 6)), ("y", toString (y + 13)),
                ("font-size", "9"), ("fill", "#7c89c0")] s!"#{idx}",
      frameGlyph (x + w / 2) (y + h / 2 + 2) r style f,
      Svg.text [("x", toString (x + w / 2)), ("y", toString (y + h - 7)),
                ("font-size", "9"), ("fill", "#cfd8f5"), ("text-anchor", "middle")]
        f.label ]

/-- Naive greedy word-wrap to lines of at most `maxLen` characters. -/
def wrapText (maxLen : Nat) (s : String) : List String :=
  let words := s.splitOn " "
  let step := words.foldl (fun (acc : List String × String) w =>
      let (lines, cur) := acc
      if cur == "" then (lines, w)
      else if cur.length + 1 + w.length ≤ maxLen then (lines, cur ++ " " ++ w)
      else (lines ++ [cur], w)) ([], "")
  step.1 ++ (if step.2 == "" then [] else [step.2])

/-- One comic strip for a moving thing: title + wrapped meaning + live demo +
key-frame film sequence + the literal SMIL. -/
def motionStrip (m : MSpec) (sy : Int) : Svg :=
  let x : Int := 40
  let w : Int := 1600
  let h : Int := 150
  let n := m.frames.length
  let fx : Int := x + 560
  let fw : Int := w - 580
  let cellW : Int := if n == 0 then fw else fw / Int.ofNat n
  let cells := m.frames.zipIdx.map (fun (f, j) =>
      filmCell (fx + Int.ofNat j * cellW + 4) (sy + 34) (cellW - 8) (h - 46)
        m.style (j + 1) f)
  let mlines := wrapText 58 m.meaning
  let meaningSvgs := mlines.zipIdx.map (fun (ln, k) =>
      Svg.text [("x", toString (x + 18)), ("y", toString (sy + 52 + Int.ofNat k * 15)),
                ("font-size", "11"), ("fill", "#cfd8f5")] ln)
  group
    ([ rect x sy w h "url(#halftone)" "#3a4a8a" [("rx", "12"), ("stroke-width", "2")],
       Svg.text [("x", toString (x + 18)), ("y", toString (sy + 28)),
                 ("font-size", "16"), ("font-weight", "800"), ("fill", "#ffd700")]
         m.title ]
     ++ meaningSvgs
     ++ [ Svg.text [("x", toString (x + 18)), ("y", toString (sy + h - 12)),
                    ("font-size", "9"), ("fill", "#7c89c0")] s!"SMIL · {m.smilText}",
          Svg.text [("x", toString (x + 470)), ("y", toString (sy + 26)),
                    ("font-size", "9"), ("fill", "#9fb0e0"), ("text-anchor", "middle")]
            "LIVE",
          group [ glyph0 20 m.style, Svg.raw m.liveSmil ]
            [("transform", s!"translate({x + 470},{sy + 92})")],
          Svg.text [("x", toString (fx)), ("y", toString (sy + 28)),
                    ("font-size", "10"), ("fill", "#9fb0e0")]
            "KEY SEQUENCE →" ]
     ++ cells)

/-! ## The minimap -/

/-- The minimap panel: every declaration plotted as one coloured dot. -/
def minimapPanel (panels : List IntrospectivePanel) : Svg :=
  let x : Int := 40
  let y : Int := 140
  let w : Int := 760
  let h : Int := 430
  let plotX (cog : Nat) : Int := x + 36 + Int.ofNat (cog - 1) * 690 / 91
  let plotY (triad : Nat) : Int := y + h - 44 - Int.ofNat triad * 330 / 19
  let dots := panels.map (fun p =>
      let (fill, _) := colorOf p.style
      group
        [ Svg.raw s!"<title>{SVG.esc p.name.toString} · cog {p.dual.cog} triad {p.dual.triad} · {styleName p.style}</title>",
          circle (plotX p.dual.cog) (plotY p.dual.triad) 3 fill "#0b0c18"
            [("stroke-width", "1"), ("opacity", "0.92")] ])
  group
    ([ rect x y w h "#0c0f22" "#3a4a8a" [("rx", "12"), ("stroke-width", "2")],
       Svg.text [("x", toString (x + 18)), ("y", toString (y + 28)),
                 ("font-size", "18"), ("font-weight", "800"), ("fill", "#ffd700")]
         "MINIMAP — EVERY DECLARATION",
       Svg.text [("x", toString (x + 18)), ("y", toString (y + 46)),
                 ("font-size", "11"), ("fill", "#9fb0e0")]
         s!"all {panels.length} decls plotted by (cog, triad), coloured by harmonic class",
       Svg.text [("x", toString (x + 18)), ("y", toString (y + h - 14)),
                 ("font-size", "11"), ("fill", "#9fb0e0")]
         "cognitive axis  →  cog (46×2)            semantic axis  ↑  triad (20×3)" ]
     ++ dots)

/-! ## The inventory -/

/-- Inventory panel: counts per harmonic class and per module. -/
def inventoryPanel (panels : List IntrospectivePanel) : Svg :=
  let x : Int := 820
  let y : Int := 140
  let w : Int := 820
  let h : Int := 430
  let cnt (k : Nat) : Nat := (panels.filter (fun p => p.style == k)).length
  let modCnt (pre : String) : Nat :=
    (panels.filter (fun p => p.name.toString.startsWith pre)).length
  let classRow (i : Nat) (k : Nat) (label : String) : Svg :=
    let (fill, _) := colorOf k
    let ry := y + 72 + Int.ofNat i * 30
    group
      [ rect (x + 20) ry 16 16 fill "#0b0c18" [("rx", "3")],
        Svg.text [("x", toString (x + 46)), ("y", toString (ry + 13)),
                  ("font-size", "13"), ("fill", "#cfd8f5")] label,
        Svg.text [("x", toString (x + w - 30)), ("y", toString (ry + 13)),
                  ("font-size", "14"), ("font-weight", "700"),
                  ("fill", "#ffd700"), ("text-anchor", "end")] s!"{cnt k}" ]
  let modRow (i : Nat) (label pre : String) : Svg :=
    let ry := y + 250 + Int.ofNat i * 28
    group
      [ Svg.text [("x", toString (x + 24)), ("y", toString (ry + 13)),
                  ("font-size", "13"), ("fill", "#cfd8f5")] label,
        Svg.text [("x", toString (x + w - 30)), ("y", toString (ry + 13)),
                  ("font-size", "14"), ("font-weight", "700"),
                  ("fill", "#8fd0ff"), ("text-anchor", "end")] s!"{modCnt pre}" ]
  group
    [ rect x y w h "#0c0f22" "#3a4a8a" [("rx", "12"), ("stroke-width", "2")],
      Svg.text [("x", toString (x + 18)), ("y", toString (y + 28)),
                ("font-size", "18"), ("font-weight", "800"), ("fill", "#ffd700")]
        "INVENTORY — WHAT IS EVERYTHING",
      Svg.text [("x", toString (x + 18)), ("y", toString (y + 60)),
                ("font-size", "12"), ("font-weight", "700"), ("fill", "#9fb0e0")]
        "by harmonic class",
      classRow 0 4 "Recursion (3^13) · violet · spiral drift",
      classRow 1 3 "Hemispheres (2^11) · gold · oscillation",
      classRow 2 2 "Heptad (6^7) · indigo · 7-cycle",
      classRow 3 1 "Muse Cycle (9^5) · teal · pulse",
      classRow 4 0 "Trivector · gray · static (no motion)",
      Svg.text [("x", toString (x + 18)), ("y", toString (y + 240)),
                ("font-size", "12"), ("font-weight", "700"), ("fill", "#9fb0e0")]
        "by module",
      modRow 0 "Holograms — foundations" "Holograms.",
      modRow 1 "AristoTask — primal atlas" "AristoTask.",
      modRow 2 "DualAtlas — mirror world" "DualAtlas.",
      Svg.text [("x", toString (x + 18)), ("y", toString (y + h - 14)),
                ("font-size", "11"), ("fill", "#7c89c0")]
        s!"total: {panels.length} declarations · {motions.length} distinct motions catalogued" ]

/-! ## Assembling the guide page -/

/-- The guide title banner. -/
def guideBanner : Svg :=
  group
    [ rect 30 24 1620 92 "url(#banner)" "#0b0c18" [("rx", "14"), ("stroke-width", "3")],
      Svg.text [("x", "60"), ("y", "74"), ("font-size", "38"), ("font-weight", "800"),
                ("fill", "#0b0c18"), ("letter-spacing", "2")]
        "ARISTO  ·  ATLAS MINIMAP & MOTION GALLERY",
      Svg.text [("x", "62"), ("y", "104"), ("font-size", "16"), ("font-weight", "600"),
                ("fill", "#1a1f3c")]
        "one page: every declaration on the minimap, and every moving thing plotted & explained as a key-frame comic strip" ]

/-- Build the full guide SVG document string for a panel list. -/
def buildGuide (panels : List IntrospectivePanel) : String :=
  let n := motions.length
  let H : Nat := 610 + n * 156 + 60
  let strips := motions.zipIdx.map (fun (m, i) =>
      motionStrip m (610 + Int.ofNat i * 156))
  let doc := document 1680 H
    ([ Svg.raw defsRaw,
       rect 0 0 1680 (Int.ofNat H) "url(#bg)" "none" [],
       guideBanner,
       minimapPanel panels,
       inventoryPanel panels,
       Svg.text [("x", "40"), ("y", "600"), ("font-size", "20"), ("font-weight", "800"),
                 ("fill", "#ffd700")]
         "MOTION GALLERY — every moving thing, plotted & explained" ]
     ++ strips
     ++ [ Svg.text [("x", "40"), ("y", toString (Int.ofNat H - 16)),
                    ("font-size", "11"), ("fill", "#5a6790")]
            "generated natively by Lean · faithful e.hash.toNat projection · companion to atlas_comic.svg" ])
  render doc

/-! ## Commands -/

/-- `#minimap` builds the guide from the whole project and reports its size. -/
syntax (name := minimapCmd) "#minimap" : command

@[command_elab minimapCmd]
def elabMinimap : CommandElab := fun _ => do
  let panels ← projectProject
  let svg := buildGuide panels
  logInfo s!"[Atlas Guide] minimap of {panels.length} declarations + {motions.length} motion strips → {svg.length}-byte animated SVG."

/-- `#writeguide "path"` builds the guide and writes the SVG file to `path`. -/
syntax (name := writeguideCmd) "#writeguide " str : command

@[command_elab writeguideCmd]
def elabWriteguide : CommandElab := fun stx => do
  match stx with
  | `(#writeguide $p:str) => do
    let path := p.getString
    let panels ← projectProject
    let svg := buildGuide panels
    IO.FS.writeFile path svg
    logInfo s!"[Atlas Guide] wrote {svg.length} bytes ({panels.length} decls, {motions.length} motions) to {path}"
  | _ => throwError "ill-formed #writeguide command"

/-! ## Generate the artifact at build time -/

#minimap

#writeguide "atlas_minimap.svg"

end AtlasGuide

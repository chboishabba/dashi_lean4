import RequestProject.SVG

/-!
# TourSVG: one self-contained animated SVG *guided tour* of the whole project

The project already emits a couple of dozen individual SVG atlases — one per
layer (`atlas_comic.svg`, `atlas_minimap.svg`, `atlas_cosmos.svg`,
`atlas_anatomy.svg`, `atlas_dual.svg`, `atlas_moonshine.svg`, …).  This module
ties them all together into a single, self-playing **slideshow tour**: a looping
animated SVG that cross-fades through one *scene* per chapter of the work, from
the proven number-theoretic foundations all the way up to the Moonshine
flip-books, the universe scan, the quine, and the certified vision FFI.

Everything is produced *natively* in Lean using the tiny `SVG` AST
(`RequestProject/SVG.lean`); the looping is plain SMIL (`<animate>` /
`<animateTransform>`), so the result plays in any browser with no JavaScript and
no external assets.  The committed artifact is `atlas_tour.svg`.
-/

namespace TourSVG

open SVG

/-! ## Numeric formatting helpers (for SMIL `keyTimes`) -/

/-- Format `k / tot` as a fixed `0.dddddd` decimal string in `[0,1]`. -/
def dec (k tot : Nat) : String :=
  let scaled := k * 1000000 / tot
  let ip := scaled / 1000000
  let fp := scaled % 1000000
  let fps := toString fp
  let pad := String.ofList (List.replicate (6 - fps.length) '0')
  s!"{ip}.{pad}{fps}"

/-! ## A scene of the tour -/

/-- One chapter of the guided tour. -/
structure Scene where
  num      : String
  title    : String
  subtitle : String
  lines    : List String
  accent   : String

/-- A `<text>` convenience builder. -/
def txt (x y : Int) (size : Nat) (fill : String) (content : String)
    (extra : List (String × String) := []) : Svg :=
  Svg.text ([("x", toString x), ("y", toString y),
             ("font-size", toString size), ("fill", fill)] ++ extra) content

/-! ## Animated motifs (one decorative loop per scene, varied by index) -/

/-- A small animated decoration centred on the right of the stage, varied by
`i % 6` so successive scenes feel distinct. -/
def motifRaw (i : Nat) (c : String) : String :=
  match i % 6 with
  | 0 =>
    -- rotating hexagon ring
    s!"<g transform=\"translate(1230,470)\">\
<polygon points=\"130,0 65,113 -65,113 -130,0 -65,-113 65,-113\" fill=\"none\" \
stroke=\"{c}\" stroke-width=\"4\" opacity=\"0.85\">\
<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"0\" to=\"360\" \
dur=\"14s\" repeatCount=\"indefinite\"/></polygon>\
<polygon points=\"80,0 40,69 -40,69 -80,0 -40,-69 40,-69\" fill=\"none\" \
stroke=\"{c}\" stroke-width=\"2\" opacity=\"0.5\">\
<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"360\" to=\"0\" \
dur=\"10s\" repeatCount=\"indefinite\"/></polygon>\
<circle r=\"11\" fill=\"{c}\"/></g>"
  | 1 =>
    -- pulsing concentric rings
    s!"<g transform=\"translate(1230,470)\">\
<circle r=\"40\" fill=\"none\" stroke=\"{c}\" stroke-width=\"3\">\
<animate attributeName=\"r\" values=\"24;140;24\" dur=\"4s\" repeatCount=\"indefinite\"/>\
<animate attributeName=\"opacity\" values=\"0.9;0;0.9\" dur=\"4s\" repeatCount=\"indefinite\"/></circle>\
<circle r=\"40\" fill=\"none\" stroke=\"{c}\" stroke-width=\"3\">\
<animate attributeName=\"r\" values=\"24;140;24\" dur=\"4s\" begin=\"2s\" repeatCount=\"indefinite\"/>\
<animate attributeName=\"opacity\" values=\"0.9;0;0.9\" dur=\"4s\" begin=\"2s\" repeatCount=\"indefinite\"/></circle>\
<circle r=\"13\" fill=\"{c}\"/></g>"
  | 2 =>
    -- orbiting satellites
    s!"<g transform=\"translate(1230,470)\">\
<circle r=\"60\" fill=\"none\" stroke=\"{c}\" stroke-width=\"2\" opacity=\"0.45\"/>\
<g><animateTransform attributeName=\"transform\" type=\"rotate\" from=\"0\" to=\"360\" \
dur=\"9s\" repeatCount=\"indefinite\"/>\
<circle cx=\"130\" cy=\"0\" r=\"15\" fill=\"{c}\"/>\
<circle cx=\"-130\" cy=\"0\" r=\"15\" fill=\"{c}\"/>\
<circle cx=\"0\" cy=\"130\" r=\"15\" fill=\"{c}\"/>\
<circle cx=\"0\" cy=\"-130\" r=\"15\" fill=\"{c}\"/></g>\
<circle r=\"14\" fill=\"{c}\"/></g>"
  | 3 =>
    -- rising bar chart (growth)
    let bar := fun (k : Nat) (bg : String) =>
      s!"<rect x=\"{k*52}\" y=\"-40\" width=\"34\" height=\"40\" rx=\"4\" fill=\"{c}\" opacity=\"0.9\">\
<animate attributeName=\"height\" values=\"24;180;24\" dur=\"3s\" begin=\"{bg}\" repeatCount=\"indefinite\"/>\
<animate attributeName=\"y\" values=\"-24;-180;-24\" dur=\"3s\" begin=\"{bg}\" repeatCount=\"indefinite\"/></rect>"
    let begins := ["0s", "0.4s", "0.8s", "1.2s"]
    let bars := String.join (begins.zipIdx.map (fun (bg, k) => bar k bg))
    s!"<g transform=\"translate(1120,560)\">{bars}</g>"
  | 4 =>
    -- twinkling constellation
    let dot := fun (x y : Int) (bg : String) =>
      s!"<circle cx=\"{x}\" cy=\"{y}\" r=\"8\" fill=\"{c}\">\
<animate attributeName=\"opacity\" values=\"0.15;1;0.15\" dur=\"2.6s\" begin=\"{bg}\" repeatCount=\"indefinite\"/></circle>"
    let pts : List ((Int × Int) × String) :=
      [((-120, -90), "0s"), ((-40, -130), "0.3s"), ((70, -70), "0.7s"),
       ((130, 30), "1.1s"), ((40, 110), "1.5s"), ((-70, 90), "0.9s"),
       ((-140, 20), "0.5s"), ((0, 0), "1.3s")]
    let dots := String.join (pts.map (fun ((x, y), bg) => dot x y bg))
    s!"<g transform=\"translate(1230,470)\">{dots}</g>"
  | _ =>
    -- bobbing wave of nodes
    let node := fun (k : Nat) (bg : String) =>
      s!"<circle cx=\"{k*48}\" cy=\"0\" r=\"13\" fill=\"{c}\">\
<animateTransform attributeName=\"transform\" type=\"translate\" values=\"0,-46;0,46;0,-46\" \
dur=\"3.2s\" begin=\"{bg}\" repeatCount=\"indefinite\"/></circle>"
    let begins := ["0s", "0.4s", "0.8s", "1.2s", "1.6s", "2.0s"]
    let nodes := String.join (begins.zipIdx.map (fun (bg, k) => node k bg))
    s!"<g transform=\"translate(1090,470)\">{nodes}</g>"

/-! ## Assembling one scene -/

/-- Build the opacity-loop animation that makes scene `i` (of `n`) visible only
during its time slot of the full `dur`-second loop, with a soft cross-fade. -/
def sceneFade (i n : Nat) (dur : Nat) : String :=
  let tot := 200 * n
  let a := 200 * i
  let b := a + 36
  let c := 200 * i + 164
  let d := 200 * (i + 1)
  let mk := fun (ks : List Nat) (vs : List String) =>
    let kt := String.intercalate ";" (ks.map (fun k => dec k tot))
    let vl := String.intercalate ";" vs
    s!"<animate attributeName=\"opacity\" dur=\"{dur}s\" repeatCount=\"indefinite\" \
calcMode=\"linear\" keyTimes=\"{kt}\" values=\"{vl}\"/>"
  if i == 0 then
    mk [0, b, c, d, tot] ["0", "1", "1", "0", "0"]
  else if d == tot then
    mk [0, a, b, c, tot] ["0", "0", "1", "1", "0"]
  else
    mk [0, a, b, c, d, tot] ["0", "0", "1", "1", "0", "0"]

/-- Render a single scene as a (initially invisible) group with its fade loop. -/
def sceneSvg (i n dur : Nat) (sc : Scene) : Svg :=
  let bodyLines : List Svg :=
    sc.lines.zipIdx.map (fun (ln, j) =>
      txt 96 (Int.ofNat (404 + j * 46)) 26 "#c7d0ee" ln)
  Svg.elem "g" [("opacity", "0")]
    ([ Svg.raw (sceneFade i n dur),
       -- accent rail
       rect 0 0 12 900 sc.accent "none" [],
       -- big chapter number, faint
       txt 70 215 150 sc.accent sc.num [("opacity", "0.16"), ("font-weight", "700")],
       -- title + underline + subtitle
       txt 96 250 56 "#ffffff" sc.title [("font-weight", "700")],
       rect 98 268 360 5 sc.accent "none" [],
       txt 98 318 28 sc.accent sc.subtitle,
       Svg.raw (motifRaw i sc.accent) ]
      ++ bodyLines)

/-! ## The scene list — the tour of everything we did -/

/-- The ordered chapters of the tour. -/
def scenes : List Scene :=
  [ { num := "", title := "Aristo Dual-Atlas",
      subtitle := "A guided tour of the whole project",
      accent := "#7ee0ff",
      lines :=
        [ "A Lean 4 atlas of the Monster sporadic group 𝕄,",
          "self-introspecting source code, and native animated SVG.",
          "",
          "Builds with lake build · no sorry · standard axioms only.",
          "Sit back — this slideshow loops through every layer." ] },
    { num := "01", title := "Foundations",
      subtitle := "Holograms.lean — proven number theory",
      accent := "#9be3a2",
      lines :=
        [ "|𝕄| = 2⁴⁶·3²⁰·5⁹·7⁶·11²·13³·17·19·23·29·31·41·47·59·71",
          "monster_divisor_count : 424,488,960 divisors.",
          "monster_threeadic_depth : v₃(d) ≤ 20 for every divisor.",
          "divisors_partition_mod : partition by residue (5,7,11,13).",
          "dualizePair_involutive : pᵉ ↦ eᵖ is an involution." ] },
    { num := "02", title := "Primal Atlas",
      subtitle := "AristoTask.lean — declarations as coordinates",
      accent := "#ffd166",
      lines :=
        [ "AristoCoordinate { size, cell, depth }.",
          "primalCoord : reflect a decl's value-hash into",
          "Monster-divisor space (size), harmonic cell, depth.",
          "primalCoord_depth_le : depth ≤ 20 (the 3-adic bound).",
          "Command: #stratify f." ] },
    { num := "03", title := "Dual Atlas",
      subtitle := "DualAtlas.lean — the mirror world",
      accent := "#ff7eb6",
      lines :=
        [ "DualCoordinate { cog, triad, harm }: 46×2 cognitive grid,",
          "20×3 semantic triads, harmonic classifier 13>11>7>5.",
          "dualFunctor dualizes each prime power pᵉ ↦ eᵖ.",
          "dualFunctor_involutive : dualizing twice is the identity.",
          "Commands: #dualstratify f · #atlas f." ] },
    { num := "04", title := "Introspective Comic",
      subtitle := "IntrospectSVG.lean — the code draws itself",
      accent := "#7ee0ff",
      lines :=
        [ "Every project declaration fused into one animated SVG.",
          "Panel I: 2D atlas (cog × triad), shaped by harmonic class.",
          "Panel II: isometric 3D atlas with a harmonic z-lift.",
          "Chapters per module, SMIL entrances and per-class motion.",
          "Artifact: atlas_comic.svg." ] },
    { num := "05", title := "Minimap & Motion",
      subtitle := "AtlasGuide.lean — the calm overview",
      accent := "#b6a6ff",
      lines :=
        [ "A minimap dotting every declaration in the dual atlas,",
          "with a per-class / per-module inventory.",
          "A motion gallery: each animated effect frozen into",
          "key-frame film cells beside its live example + SMIL.",
          "Artifact: atlas_minimap.svg." ] },
    { num := "06", title := "The Universe",
      subtitle := "Cosmos.lean — every decl in scope",
      accent := "#9be3a2",
      lines :=
        [ "Scans the entire environment: Lean compiler, core,",
          "Std, Batteries and all of Mathlib — via the live uses graph.",
          "≈ 707,165 declarations across 9,981 modules.",
          "Modular view + functional dependency view, one SVG.",
          "Artifact: atlas_cosmos.svg." ] },
    { num := "07", title := "Anatomy",
      subtitle := "Anatomy.lean — what a term is made of",
      accent := "#ffd166",
      lines :=
        [ "Reflects each kernel Expr: which of the 12 constructors",
          "appear (a features/12 coverage score), AST depth,",
          "node size, and distinct constants referenced.",
          "Exactly the data the kernel stores.",
          "Commands: #anatomy f · #anatomymap." ] },
    { num := "08", title := "Anatomy Film",
      subtitle := "AnatomySVG.lean — examples that assemble",
      accent := "#ff7eb6",
      lines :=
        [ "An animated film: anatomy cards build themselves.",
          "Constructor counters grow 0 → true value as bar charts,",
          "12 language-coverage cells light up, a depth ladder rises.",
          "Featured: Nat.add, List.map, dualFunctor, dualizePair…",
          "Artifact: atlas_anatomy.svg." ] },
    { num := "09", title := "The Quine",
      subtitle := "Quine.lean — the program reproduced",
      accent := "#7ee0ff",
      lines :=
        [ "A genuine two-line Lean 4 quine: it prints its own source",
          "with no input and without reading its file.",
          "quine_is_fixpoint : reproduce body = quineSource.",
          "Commands: #quine · #writequine · #verifyquine.",
          "Artifact: quine.lean." ] },
    { num := "10", title := "Moonshine Flip-Book",
      subtitle := "Moonshine + MoonshineSVG.lean",
      accent := "#b6a6ff",
      lines :=
        [ "Source atoms projected into the 194 Monster irreps,",
          "played back keyed by the q-expansion of Klein's j.",
          "j built from first principles: E₄, Δ, jSeries = E₄³/Δ.",
          "Head identities proved: 196884 = 1 + 196883, …",
          "Artifact: atlas_moonshine.svg." ] },
    { num := "11", title := "Prime-Modulus Atlas",
      subtitle := "PrimeProjection.lean — multi-mod views",
      accent := "#9be3a2",
      lines :=
        [ "Projects declarations across several prime moduli at once,",
          "with a q-keyed selector to flip between residue views.",
          "Artifact: atlas_primeview.svg." ] },
    { num := "12", title := "Separation Theorem",
      subtitle := "Monster/Moonshine address pipeline",
      accent := "#ffd166",
      lines :=
        [ "MonsterAddress.lean + MoonshineAddress.lean assign each",
          "declaration a structured address, and prove a separation",
          "theorem: distinct inputs get distinguishable addresses." ] },
    { num := "13", title := "FRACTRAN Biomes",
      subtitle := "FractranWalk + FractranBiome.lean",
      accent := "#ff7eb6",
      lines :=
        [ "Conway's FRACTRAN / PRIMEGAME walked across the irrep",
          "biomes of the Monster, rendered as an animated traversal.",
          "Artifacts: atlas_fractran.svg, atlas_atomforest.svg." ] },
    { num := "14", title := "Irrep Fold",
      subtitle := "IrrepFold.lean — squeezed into the primes",
      accent := "#7ee0ff",
      lines :=
        [ "Declarations folded into the available Monster primes,",
          "with the residual structure drawn as interlocking gears.",
          "Artifacts: atlas_irrepfold.svg, atlas_irrepgears.svg." ] },
    { num := "15", title := "q-Deformation",
      subtitle := "QDeform.lean — projection in motion",
      accent := "#b6a6ff",
      lines :=
        [ "The atlas projection deformed continuously along the",
          "104 q-expansion frames — the coordinate field breathing.",
          "Artifact: atlas_qdeform.svg." ] },
    { num := "16", title := "Dual Functor, Animated",
      subtitle := "DualAtlasSVG.lean",
      accent := "#9be3a2",
      lines :=
        [ "The involutive dual functor pᵉ ↦ eᵖ shown as an animation:",
          "each prime power flips to its dual and back, a faithful",
          "re-coordinatisation made visible.",
          "Artifacts: atlas_dual.svg, atlas_dualdeform.svg." ] },
    { num := "17", title := "Corpus Graph",
      subtitle := "CorpusGraph.lean — the project's own web",
      accent := "#ffd166",
      lines :=
        [ "The whole corpus as a dependency graph: declarations as",
          "nodes, the uses relation as edges, laid out and animated.",
          "Artifacts: atlas_corpus.svg, atlas_declweave.svg." ] },
    { num := "18", title := "Monster Bitmap",
      subtitle := "MonsterBitmapSVG.lean",
      accent := "#ff7eb6",
      lines :=
        [ "The 194 × 100 Monster–Moonshine bitmap: irreps against",
          "j-expansion frames, animated cell by cell.",
          "Artifact: atlas_bitmap.svg." ] },
    { num := "19", title := "Breaking the Smushes",
      subtitle := "QExpansionLadder + DuplicateGlossary",
      accent := "#7ee0ff",
      lines :=
        [ "Where the projection collapses distinct decls together,",
          "the q-expansion ladder separates the persistent smushes,",
          "catalogued as a glossary of genuine duplicate clusters." ] },
    { num := "20", title := "Fiber Homes",
      subtitle := "FiberHome.lean — a home for every decl",
      accent := "#b6a6ff",
      lines :=
        [ "The natural home of each declaration in the fibered atlas:",
          "each lands in exactly one fiber over the base coordinates,",
          "the partition made total and explicit." ] },
    { num := "21", title := "Certified Vision FFI",
      subtitle := "VisionFFI + VisionFFICert.lean",
      accent := "#9be3a2",
      lines :=
        [ "The per-decl embedding exposed over a C ABI (@[export]),",
          "with range certs (cog 1..92, triad ≤19, harm ∈ {0,5,7,11,13})",
          "and proofs the FFI matches the certified projections.",
          "Loadable from Python/C as libaristovision.so." ] },
    { num := "★", title := "End of Tour",
      subtitle := "…and it all loops",
      accent := "#ffd166",
      lines :=
        [ "Proven foundations → self-introspecting atlases →",
          "the whole Lean/Mathlib universe → Moonshine → a quine →",
          "a certified FFI, every picture generated natively in Lean.",
          "",
          "lake build · no sorry · this tour replays from the top." ] } ]

/-! ## Document assembly -/

/-- Seconds each scene is on screen. -/
def slotSeconds : Nat := 5

/-- Background, persistent header/footer, and a sweeping progress bar. -/
def chromeRaw (dur : Nat) : String :=
  s!"<animate attributeName=\"width\" from=\"0\" to=\"1540\" dur=\"{dur}s\" repeatCount=\"indefinite\"/>"

/-- The full tour SVG document string. -/
def buildTour : String :=
  let n := scenes.length
  let dur := n * slotSeconds
  let sceneEls := scenes.zipIdx.map (fun (sc, i) => sceneSvg i n dur sc)
  let defs := Svg.raw
    "<defs>\
<radialGradient id=\"bg\" cx=\"30%\" cy=\"25%\" r=\"90%\">\
<stop offset=\"0%\" stop-color=\"#141a33\"/>\
<stop offset=\"60%\" stop-color=\"#0c1022\"/>\
<stop offset=\"100%\" stop-color=\"#070912\"/>\
</radialGradient>\
<linearGradient id=\"prog\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">\
<stop offset=\"0%\" stop-color=\"#7ee0ff\"/>\
<stop offset=\"100%\" stop-color=\"#ff7eb6\"/>\
</linearGradient></defs>"
  let header :=
    Svg.elem "g" []
      [ txt 30 56 22 "#8fa0d8" "Aristo Dual-Atlas",
        txt 30 84 16 "#54618f" "guided tour · generated natively by Lean" ]
  let footer :=
    Svg.elem "g" []
      [ txt 30 872 15 "#54618f"
          "a single self-playing SVG · SMIL only · no scripts · loops forever",
        rect 30 884 1540 6 "#1c2444" "none" [("rx", "3")],
        Svg.elem "rect"
          [ ("x", "30"), ("y", "884"), ("width", "0"), ("height", "6"),
            ("rx", "3"), ("fill", "url(#prog)") ]
          [ Svg.raw (chromeRaw (scenes.length * slotSeconds)) ] ]
  let doc := document 1600 900
    ([ defs,
       rect 0 0 1600 900 "url(#bg)" "none" [],
       header ]
      ++ sceneEls
      ++ [ footer ])
  render doc

/-- The tour as a single string value (also usable from other modules). -/
def tourSvg : String := buildTour

/-! Write the committed artifact at build time. -/
#eval do
  IO.FS.writeFile "atlas_tour.svg" tourSvg
  IO.println s!"[Tour] wrote {tourSvg.length} bytes, {scenes.length} scenes, \
{scenes.length * slotSeconds}s loop to atlas_tour.svg"

end TourSVG

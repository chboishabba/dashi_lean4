import RequestProject.Anatomy
import RequestProject.SVG
import Lean

/-!
# AnatomySVG: a few worked examples, *constructed as animation*

The `Anatomy` layer measures, for each declaration, how much of the Lean 4 term
language composes it and how deep it is.  This layer turns a handful of those
measurements into a short **animated film**: for each featured example it draws
an *anatomy card* that builds itself up before your eyes —

* the twelve `Expr`-constructor counters grow from `0` to their true value as
  staggered bar-charts (this is literally *how much of the language* the term
  uses, drawn proportionally);
* a **depth meter** fills to the term's AST depth;
* twelve **language-coverage cells** light up one by one — one per `Expr`
  constructor actually used — so you can watch the alphabet of the term assemble;
* a **depth ladder** of rungs rises to the measured depth.

Everything animates with native SMIL (`<animate>`), so the SVG plays on its own.

Commands:

* `#anatomyfilm`          — build the film for the featured examples, report size.
* `#writeanatomy "path"`  — build the film and write the SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace AnatomySVG

open Anatomy

/-- The declarations featured in the film: three illustrative core declarations
and three from the project itself. -/
def featured : List Name :=
  [`Nat.add, `List.map, `Prod.fst,
   `DualAtlas.dualFunctor, `Holograms.dualizePair, `AristoTask.primalCoord]

/-- Colour for a constructor bar, by kind index (warm → cool sweep). -/
def kindColor : Nat → String
  | 0 => "#ff5db1" | 1 => "#ff7a59" | 2 => "#ffa13d" | 3 => "#ffd23d"
  | 4 => "#b6e000" | 5 => "#4fd86a" | 6 => "#2bd0c0" | 7 => "#2bb6ff"
  | 8 => "#5d8bff" | 9 => "#8a6bff" | 10 => "#c45dff" | 11 => "#ff5de0"
  | _ => "#9aa3b8"

/-- One animated anatomy card for a named profile at vertical offset `y0`,
appearing with a stagger keyed by `idx`. -/
def card (idx : Nat) (y0 : Int) (np : NamedProfile) : Svg :=
  let p := np.profile
  let delay := s!"{idx}00ms"   -- 0ms, 100ms, …, cards enter in turn
  -- scale: longest bar = 360px maps to the max nonzero count (≥1)
  let maxC := (p.counts.foldl (fun m (_, n) => max m n) 1)
  let barFull (n : Nat) : Int := (Int.ofNat n) * 360 / (Int.ofNat maxC)
  -- the twelve constructor bars
  let bars := p.counts.zipIdx.map (fun ((k, n), j) =>
    let by_ : Int := y0 + 70 + (Int.ofNat j) * 13
    let w := barFull n
    let begin := s!"{idx * 100 + j * 60}ms"
    group
      [ Svg.text [("x","40"),("y", toString (by_ + 9)),("font-size","9"),
                  ("fill","#9fb0e0"),("text-anchor","end")] k.label,
        rect 50 by_ 360 10 "#10142c" "#2a335f" [("rx","2")],
        Svg.elem "rect"
          [("x","50"),("y", toString by_),("height","10"),("rx","2"),
           ("fill", kindColor j),("width","0")]
          [ Svg.raw s!"<animate attributeName=\"width\" from=\"0\" to=\"{w}\" begin=\"{begin}\" dur=\"0.7s\" fill=\"freeze\" calcMode=\"spline\" keySplines=\"0.2 0.8 0.2 1\" keyTimes=\"0;1\"/>" ],
        Svg.text [("x", toString (50 + w + 6)),("y", toString (by_ + 9)),
                  ("font-size","9"),("fill","#cfd8f5")]
          (if n = 0 then "" else toString n) ]
      [])
  -- language-coverage cells: one lights up per constructor actually used
  let cells := p.counts.zipIdx.map (fun ((_, n), j) =>
    let cx : Int := 470 + (Int.ofNat (j % 6)) * 26
    let cy : Int := y0 + 78 + (Int.ofNat (j / 6)) * 26
    let lit := n > 0
    let begin := s!"{idx * 100 + 200 + j * 90}ms"
    group
      [ rect cx cy 22 22 (if lit then kindColor j else "#10142c")
          "#2a335f" (("rx","4") ::
            (if lit then
              [("opacity","0")]
            else [("opacity","0.5")])),
        (if lit then
          Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{begin}\" dur=\"0.4s\" fill=\"freeze\"/>"
         else Svg.raw "") ]
      [])
  -- depth ladder: rungs rising to the measured depth (capped at 24 rungs)
  let rungN := min p.depth 24
  let ladder := (List.range rungN).map (fun j =>
    let ry : Int := y0 + 188 - (Int.ofNat j) * 6
    let begin := s!"{idx * 100 + j * 40}ms"
    Svg.elem "line"
      [("x1","472"),("y1", toString ry),("x2","620"),("y2", toString ry),
       ("stroke","#2bd0c0"),("stroke-width","3"),("opacity","0")]
      [ Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"0.9\" begin=\"{begin}\" dur=\"0.25s\" fill=\"freeze\"/>" ])
  group
    ([ -- card frame, faded in
       Svg.elem "rect"
         [("x","20"),("y", toString y0),("width","800"),("height","210"),
          ("rx","12"),("fill","#0c0f22"),("stroke","#3a4a8a"),
          ("stroke-width","2"),("opacity","0")]
         [ Svg.raw s!"<animate attributeName=\"opacity\" from=\"0\" to=\"1\" begin=\"{delay}\" dur=\"0.5s\" fill=\"freeze\"/>" ],
       Svg.text [("x","40"),("y", toString (y0 + 30)),("font-size","18"),
                 ("font-weight","800"),("fill","#ffd700")] np.name.toString,
       Svg.text [("x","40"),("y", toString (y0 + 50)),("font-size","12"),
                 ("fill","#9fb0e0")]
         s!"depth {p.depth} · {p.size} nodes · {p.consts} distinct consts · language {p.features}/12 constructors",
       Svg.text [("x","470"),("y", toString (y0 + 66)),("font-size","11"),
                 ("font-weight","700"),("fill","#cfd8f5")] "language coverage",
       Svg.text [("x","472"),("y", toString (y0 + 204)),("font-size","11"),
                 ("font-weight","700"),("fill","#2bd0c0")]
         s!"depth ladder → {p.depth}" ]
     ++ bars ++ cells ++ ladder)
    []

/-- Build the full animated anatomy-film SVG for a list of named profiles. -/
def buildFilm (profs : List NamedProfile) : String :=
  let cards := profs.zipIdx.map (fun (np, i) =>
    card i (100 + (Int.ofNat i) * 230) np)
  let h : Nat := 130 + profs.length * 230
  let doc := document 840 h
    ([ Svg.raw ("<defs><radialGradient id=\"bg\" cx=\"50%\" cy=\"0%\" r=\"100%\">" ++
        "<stop offset=\"0%\" stop-color=\"#1a1f3c\"/><stop offset=\"100%\" stop-color=\"#070812\"/></radialGradient></defs>"),
       rect 0 0 840 (Int.ofNat h) "url(#bg)" "none" [],
       rect 20 24 800 56 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x","40"),("y","52"),("font-size","24"),("font-weight","800"),
                 ("fill","#ffd700")] "ANATOMY FILM — terms building themselves",
       Svg.text [("x","40"),("y","72"),("font-size","12"),("fill","#9fb0e0")]
         "each card animates how much of the Lean 4 term language composes the declaration, and its depth" ]
     ++ cards
     ++ [ Svg.text [("x","20"),("y", toString (Int.ofNat h - 12)),("font-size","11"),
                    ("fill","#5a6790")]
            "generated natively by Lean · counts are exact Expr-constructor tallies · #writeanatomy" ])
  render doc

/-- Gather the featured profiles by reflection. -/
def gatherFeatured : CommandElabM (List NamedProfile) := do
  let mut out : List NamedProfile := []
  for nm in featured do
    let p ← liftTermElabM <| Meta.MetaM.run' (analyzeDecl nm)
    out := { name := nm, profile := p } :: out
  return out.reverse

/-! ## Commands -/

/-- `#anatomyfilm` builds the animated example film and reports its size. -/
syntax (name := anatomyfilmCmd) "#anatomyfilm" : command

@[command_elab anatomyfilmCmd]
def elabAnatomyfilm : CommandElab := fun _ => do
  let profs ← gatherFeatured
  let svg := buildFilm profs
  logInfo s!"[Anatomy Film] animated {profs.length} worked examples into a {svg.length}-byte SVG."

/-- `#writeanatomy "path"` builds the film and writes the SVG file to `path`. -/
syntax (name := writeanatomyCmd) "#writeanatomy " str : command

@[command_elab writeanatomyCmd]
def elabWriteanatomy : CommandElab := fun stx => do
  match stx with
  | `(#writeanatomy $p:str) => do
    let path := p.getString
    let profs ← gatherFeatured
    let svg := buildFilm profs
    IO.FS.writeFile path svg
    logInfo s!"[Anatomy Film] wrote {svg.length} bytes ({profs.length} examples) to {path}"
  | _ => throwError "ill-formed #writeanatomy command"

/-! ## Test suite -/

#anatomyfilm
#writeanatomy "atlas_anatomy.svg"

end AnatomySVG

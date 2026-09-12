import RequestProject.Holograms
import RequestProject.DualAtlas
import RequestProject.SVG
import Lean

/-!
# MonsterOrrerySVG: the prime factorisation of `|𝕄|`, as an orrery animation

This layer renders the prime factorisation of the Monster order
`|𝕄| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71`
(the very definition `Holograms.monsterOrder` the proofs use) as a single
self-contained, self-playing **animated SVG orrery**.

Each prime factor `p^e` is a body on its own orbital ring:

* the six *structured* prime powers (`DualAtlas.primalAtlas`) orbit the inner
  rings; as they sweep, each periodically **dualizes** `p^e ↦ e^p` via
  `Holograms.dualizePair`, the involution made visible
  (`Holograms.dualizePair_involutive`);
* the nine *linear* primes `17 … 71` ride the outer ring.

Orbit period and body radius are computed natively by Lean from the exponents,
so the picture is faithful to the formalised factorisation.

Commands:

* `#orrery`               — build the orrery, report its size.
* `#writeorrery "path"`   — build the orrery and write the SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace MonsterOrrerySVG

open DualAtlas (primalAtlas)

/-- The nine *linear* prime factors of `|𝕄|` (exponent one). -/
def linearPrimes : List Nat := [17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- Per-prime colour (warm → cool with the prime size). -/
def primeColor : Nat → String
  | 2  => "#ff5db1"
  | 3  => "#ff7a59"
  | 5  => "#ffd23d"
  | 7  => "#4fd86a"
  | 11 => "#2bb6ff"
  | 13 => "#8a6bff"
  | _  => "#9aa3b8"

/-- Centre of the orrery. -/
def cx : Int := 450
def cy : Int := 460

/-! ## The orbital rings (drawn faint, behind the bodies) -/

/-- A faint dashed orbital circle of the given radius. -/
def orbitRing (r : Int) : Svg :=
  Svg.elem "circle"
    [("cx", toString cx), ("cy", toString cy), ("r", toString r),
     ("fill", "none"), ("stroke", "#2a335f"), ("stroke-width", "1"),
     ("stroke-dasharray", "3 6"), ("opacity", "0.6")] []

/-! ## A structured prime power as an orbiting, dualizing body -/

/-- One orbiting body for a structured prime power `p^e` at orbit index `idx`.

The body sits at distance `r` along the +x axis inside a `<g>` that is rotated
about the centre by an `animateTransform`, so the body orbits.  A counter-rotation
keeps the label upright.  The `p^e ↔ e^p` text cross-fades, exposing
`Holograms.dualizePair`. -/
def orbitBody (idx : Nat) (p e : Nat) : Svg :=
  let r : Int := 70 + Int.ofNat idx * 48
  -- inner orbits sweep faster; period grows with the ring index
  let dur : String := s!"{8 + idx * 4}s"
  -- body radius scaled (gently) by the exponent
  let bodyR : Int := 12 + Int.ofNat (Nat.min e 24) / 2
  let col := primeColor p
  let phase : String := s!"{idx * 60}ms"
  -- the dual of (p, e) via the formalised involution
  let d := Holograms.dualizePair (p, e)
  let pd := d.1
  let ed := d.2
  group
    [ Svg.elem "g" [("transform", s!"rotate(0 {cx} {cy})")]
        [ Svg.raw s!"<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"0 {cx} {cy}\" to=\"360 {cx} {cy}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          -- the body, parked at (cx + r, cy); counter-rotate to keep text upright
          Svg.elem "g" [("transform", s!"translate({cx + r} {cy})")]
            [ Svg.elem "g" [("transform", "rotate(0)")]
                [ Svg.raw s!"<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"0\" to=\"-360\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
                  -- glow + disc
                  Svg.elem "circle"
                    [("cx","0"),("cy","0"),("r", toString (bodyR + 4)),
                     ("fill", col),("opacity","0.18")]
                    [ Svg.raw s!"<animate attributeName=\"r\" values=\"{bodyR + 2};{bodyR + 8};{bodyR + 2}\" dur=\"2.5s\" repeatCount=\"indefinite\"/>" ],
                  Svg.elem "circle"
                    [("cx","0"),("cy","0"),("r", toString bodyR),
                     ("fill","#0c0f22"),("stroke", col),("stroke-width","2")] [],
                  -- original p^e  (fades out)
                  Svg.elem "text"
                    [("x","0"),("y","5"),("font-size","15"),("font-weight","800"),
                     ("text-anchor","middle"),("fill", col)]
                    [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"1;1;0;0;1\" keyTimes=\"0;0.4;0.5;0.9;1\" begin=\"{phase}\" dur=\"5s\" repeatCount=\"indefinite\"/>",
                      Svg.raw s!"{p}<tspan baseline-shift=\"super\" font-size=\"9\">{e}</tspan>" ],
                  -- dualized e^p  (fades in)
                  Svg.elem "text"
                    [("x","0"),("y","5"),("font-size","15"),("font-weight","800"),
                     ("text-anchor","middle"),("fill","#ffd700"),("opacity","0")]
                    [ Svg.raw s!"<animate attributeName=\"opacity\" values=\"0;0;1;1;0\" keyTimes=\"0;0.4;0.5;0.9;1\" begin=\"{phase}\" dur=\"5s\" repeatCount=\"indefinite\"/>",
                      Svg.raw s!"{pd}<tspan baseline-shift=\"super\" font-size=\"9\">{ed}</tspan>" ] ] ] ] ]
    []

/-! ## A linear prime on the outer ring -/

/-- One body for a linear prime `p` (exponent one) at outer-ring slot `idx` of `n`. -/
def linearBody (n idx : Nat) (p : Nat) : Svg :=
  let r : Int := 360
  let dur : String := "60s"
  -- distribute the linear primes evenly around the outer ring
  let ang : Int := Int.ofNat (idx * 360 / n)
  group
    [ Svg.elem "g" [("transform", s!"rotate({ang} {cx} {cy})")]
        [ Svg.raw s!"<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"{ang} {cx} {cy}\" to=\"{ang + 360} {cx} {cy}\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
          Svg.elem "g" [("transform", s!"translate({cx + r} {cy})")]
            [ Svg.elem "g" [("transform", "rotate(0)")]
                [ Svg.raw s!"<animateTransform attributeName=\"transform\" type=\"rotate\" from=\"0\" to=\"-360\" dur=\"{dur}\" repeatCount=\"indefinite\"/>",
                  Svg.elem "circle"
                    [("cx","0"),("cy","0"),("r","13"),
                     ("fill","#10142c"),("stroke","#9aa3b8"),("stroke-width","1.5")]
                    [ Svg.raw "<animate attributeName=\"opacity\" values=\"0.7;1;0.7\" dur=\"3s\" repeatCount=\"indefinite\"/>" ],
                  Svg.text [("x","0"),("y","4"),("font-size","12"),("font-weight","700"),
                            ("text-anchor","middle"),("fill","#cfd8f5")] (toString p) ] ] ] ]
    []

/-! ## Assembling the orrery -/

/-- Build the complete animated orrery SVG. -/
def buildOrrery : String :=
  let w : Nat := 900
  let h : Nat := 920
  let n := linearPrimes.length
  let rings := (List.range 6).map (fun i => orbitRing (70 + Int.ofNat i * 48))
  let bodies := primalAtlas.zipIdx.map (fun ((p, e), i) => orbitBody i p e)
  let linears := linearPrimes.zipIdx.map (fun (p, i) => linearBody n i p)
  let doc := document w h
    ([ Svg.raw ("<defs><radialGradient id=\"sky\" cx=\"50%\" cy=\"50%\" r=\"75%\">" ++
        "<stop offset=\"0%\" stop-color=\"#161c3a\"/><stop offset=\"100%\" stop-color=\"#05060e\"/></radialGradient></defs>"),
       rect 0 0 (Int.ofNat w) (Int.ofNat h) "url(#sky)" "none" [],
       -- title bar
       rect 20 18 860 64 "#1a1f3c" "#3a4a8a" [("rx","12"),("stroke-width","2")],
       Svg.text [("x","40"),("y","46"),("font-size","21"),("font-weight","800"),
                 ("fill","#ffd700")] "MONSTER ORRERY — the prime factorisation of |𝕄|, animated",
       Svg.text [("x","40"),("y","70"),("font-size","12"),("fill","#9fb0e0")]
         "2^46·3^20·5^9·7^6·11^2·13^3·17·19·23·29·31·41·47·59·71  ·  six structured powers dualize p^e ↦ e^p as they orbit" ]
     ++ rings
     -- central body: the Monster itself
     ++ [ Svg.elem "circle"
            [("cx", toString cx),("cy", toString cy),("r","34"),
             ("fill","#0c0f22"),("stroke","#ffd700"),("stroke-width","2")]
            [ Svg.raw "<animate attributeName=\"r\" values=\"32;37;32\" dur=\"4s\" repeatCount=\"indefinite\"/>" ],
          Svg.text [("x", toString cx),("y", toString (cy - 2)),("font-size","26"),
                    ("font-weight","800"),("text-anchor","middle"),("fill","#ffd700")] "𝕄",
          Svg.text [("x", toString cx),("y", toString (cy + 16)),("font-size","9"),
                    ("text-anchor","middle"),("fill","#9fb0e0")] "order" ]
     ++ bodies
     ++ linears
     ++ [ Svg.text [("x","20"),("y", toString (Int.ofNat h - 16)),("font-size","11"),
                    ("fill","#5a6790")]
            "generated natively by Lean · orbits & dualization from Holograms.dualizePair / DualAtlas.primalAtlas · #writeorrery" ])
  render doc

/-! ## Commands -/

/-- `#orrery` builds the animated orrery and reports its size. -/
syntax (name := orreryCmd) "#orrery" : command

@[command_elab orreryCmd]
def elabOrrery : CommandElab := fun _ => do
  let svg := buildOrrery
  logInfo s!"[Monster Orrery] animated {primalAtlas.length + linearPrimes.length} prime factors into a {svg.length}-byte SVG."

/-- `#writeorrery "path"` builds the orrery and writes the SVG file to `path`. -/
syntax (name := writeorreryCmd) "#writeorrery " str : command

@[command_elab writeorreryCmd]
def elabWriteorrery : CommandElab := fun stx => do
  match stx with
  | `(#writeorrery $p:str) => do
    let path := p.getString
    let svg := buildOrrery
    IO.FS.writeFile path svg
    logInfo s!"[Monster Orrery] wrote {svg.length} bytes to {path}"
  | _ => throwError "ill-formed #writeorrery command"

/-! ## Test suite -/

#orrery
#writeorrery "atlas_orrery.svg"

end MonsterOrrerySVG

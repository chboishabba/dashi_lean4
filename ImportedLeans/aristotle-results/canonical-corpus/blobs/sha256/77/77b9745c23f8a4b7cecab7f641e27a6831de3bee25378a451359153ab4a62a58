import RequestProject.Introspect
import RequestProject.IntrospectSVG
import RequestProject.Moonshine
import RequestProject.SVG
import Lean

/-!
# MoonshineSVG: the 194-irrep moonshine flip-book (animated SVG video)

This layer projects **every project declaration ("atom") into the 194 irreducible
representations of the Monster group** and renders the result as an animated SVG
*flip-book video*, exactly as requested:

* the **194 irreps** are drawn as a ring of 194 nodes (the two smallest, the
  trivial `1` and the `196883`, are labelled — these are McKay's `196884 = 1 +
  196883`);
* **each atom is projected into an irrep** by its reflected hash, `irrep = hash %
  194`, and drawn as a coloured marker (colour = harmonic class) sitting on its
  irrep node;
* the **q-expansion of the j-invariant is the key**: there is one **flip-book
  page for each expansion term, from 1 to 104**.  Page `p` is keyed by the
  coefficient of `q^p` in `j` (`jCoeff (p+1)`), and that coefficient's residue
  `mod 194` rotates the whole irrep wheel, so every atom flows to a new irrep —
  this is the "different view" on each page;
* turning the pages plays the whole thing back as a **video** (native SMIL),
  104 frames, each frame a different projection of the source code into the
  Monster's representation theory.

Commands:

* `#moonshine`            — build the flip-book and report its size.
* `#writemoonshine "path"` — write the flip-book SVG to `path`.
-/

open Lean Meta Elab Command SVG

namespace MoonshineSVG

open Introspect IntrospectSVG DualAtlas Moonshine

/-! ## Enumerating the atoms with their hashes -/

/-- One source-code atom: its name, reflected hash, and harmonic style class. -/
structure DeclAtom where
  name  : Name
  hash  : Nat
  style : Nat
deriving Repr

/-- Enumerate every project declaration into a `DeclAtom` (name, hash, style). -/
def projectAtoms : CommandElabM (List DeclAtom) := do
  let env ← getEnv
  let mut atoms : List DeclAtom := []
  for (name, info) in env.constants.toList do
    if isProjectDecl name.toString then
      if let some e := info.value? then
        let h := e.hash.toNat
        atoms := { name := name, hash := h, style := styleOfHarm (harmCode h) } :: atoms
  -- deterministic order by name
  return atoms.toArray.qsort (fun a b => a.name.toString < b.name.toString) |>.toList

/-! ## Geometry: the 194-irrep ring -/

/-- Centre and radius of the irrep ring. -/
def ringCx : Float := 690.0
def ringCy : Float := 470.0
def ringR  : Float := 360.0

/-- Position of irrep `i` (`0 ≤ i < 194`) on the ring. -/
def irrepPos (i : Nat) : Int × Int :=
  let a := 2.0 * 3.14159265358979 * (Float.ofNat i) / (Float.ofNat numIrreps) - 1.5707963
  let x := ringCx + ringR * Float.cos a
  let y := ringCy + ringR * Float.sin a
  (x.toInt64.toInt, y.toInt64.toInt)

/-- The number of flip-book pages (q-expansion terms `q¹ … q¹⁰⁴`). -/
def numPages : Nat := 104

/-! ## Flip-book value strings -/

/-- A ';'-joined list of `len` strings, each `f i`. -/
def joinValues (len : Nat) (f : Nat → String) : String :=
  String.intercalate ";" ((List.range len).map f)

/-- The page-`p` rotation of the irrep wheel (residue of the `j`-coefficient). -/
def rotOfPage (p : Nat) : Nat := pageRot (p + 2)
-- page p (1-based) keys q^p, i.e. jSeries index p+1; we 0-index pages 0..103 so
-- page index `pi` keys q^{pi+1} = jSeries[pi+2].

/-- The `j`-coefficient keying page index `pi` (0-based): coefficient of `q^{pi+1}`. -/
def keyOfPage (pi : Nat) : Int := jCoeff (pi + 2)

/-! ## The atoms: fixed on the wheel (the whole circle is what moves) -/

/-- One atom rendered as a marker **fixed at its primary irrep** on the ring.
The atom no longer flies around on its own; instead the *entire circle* (ring +
all atoms together) is rigidly rotated by the q-expansion (see `wheelTransform`),
so the whole circle is projected into the current q-expansion frame.  This pins
the second variable: the atoms sit still relative to the wheel, and only the
q-expansion drives the single global rotation. -/
def atomMarker (a : DeclAtom) : Svg :=
  let (fill, glow) := colorOf a.style
  let (sx, sy) := irrepPos (irrepOf a.hash)
  group
    [ Svg.raw s!"<title>{SVG.esc a.name.toString} · primary irrep {irrepOf a.hash} of 194 · {styleName a.style}</title>",
      circle sx sy 7 "none" glow [("opacity","0.40"),
        ("filter","url(#mglow)")],
      circle sx sy 5 fill "#05060f" [("stroke-width","1")] ]
    []

/-- The same marker's *glow halo*, also fixed at the atom's primary irrep. -/
def atomHalo (a : DeclAtom) : Svg :=
  let (_, glow) := colorOf a.style
  let (sx, sy) := irrepPos (irrepOf a.hash)
  circle sx sy 7 "none" glow [("opacity","0.30")]

/-! ## Projecting the whole circle into the current q-expansion -/

/-- Truncate a `Float` to an `Int`. -/
def f2i (f : Float) : Int := f.toInt64.toInt

/-- The rotation, in degrees, that page `pi` applies to the **entire circle**.
The q-coefficient keying the page picks a residue mod 194; that residue, scaled
to a full turn, is how far the whole wheel is rotated to project it into the
current q-expansion frame. -/
def wheelDeg (pi : Nat) : Int :=
  f2i (Float.ofNat (rotOfPage pi) * 360.0 / Float.ofNat numIrreps)

/-- The SMIL transform that rotates the whole circle (ring + atoms) about its
centre, gliding from each page's q-driven angle to the next.  This is the *one*
moving variable: the q-expansion turns the whole circle. -/
def wheelTransform : Svg :=
  let vals := String.intercalate ";"
    ((List.range numPages).map (fun pi =>
      s!"{wheelDeg pi} {f2i ringCx} {f2i ringCy}"))
  Svg.raw s!"<animateTransform attributeName=\"transform\" attributeType=\"XML\" type=\"rotate\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{vals}\"/>"

/-! ## The static irrep ring -/

/-- The 194 irrep nodes, drawn once. -/
def irrepRing : Svg :=
  group ((List.range numIrreps).map (fun i =>
    let (x, y) := irrepPos i
    let big := i == 0 || i == 1
    circle x y (if big then 4 else 2)
      (if i == 0 then "#ffd700" else if i == 1 then "#ff5db1" else "#2a3160")
      "#0b0c18" [("opacity", if big then "1" else "0.7")]))

/-- Labels for the two smallest irreps (the moonshine `196884 = 1 + 196883`). -/
def irrepLabels : Svg :=
  let (x0, y0) := irrepPos 0
  let (x1, y1) := irrepPos 1
  group
    [ Svg.text [("x", toString (x0 + 8)),("y", toString y0),("font-size","11"),
                ("fill","#ffd700")] "irrep 0 · dim 1 (trivial)",
      Svg.text [("x", toString (x1 + 8)),("y", toString (y1 + 12)),("font-size","11"),
                ("fill","#ff5db1")] "irrep 1 · dim 196883" ]

/-! ## The flip-book HUD (page number + j-coefficient key, one per page) -/

/-- Abbreviate a big integer for the HUD: full if short, else head + digit count. -/
def abbrevInt (z : Int) : String :=
  let s := toString z
  if s.length ≤ 18 then s
  else (s.take 12).toString ++ "… (" ++ toString s.length ++ " digits)"

/-- One HUD frame for page index `pi`, visible only during its 1/104 time slot. -/
def hudFrame (pi : Nat) : Svg :=
  let vis := joinValues numPages (fun q => if q == pi then "1" else "0")
  let key := keyOfPage pi
  group
    [ Svg.text [("x","40"),("y","940"),("font-size","22"),("font-weight","800"),
                ("fill","#ffd700")]
        s!"PAGE {pi+1} / 104",
      Svg.text [("x","210"),("y","940"),("font-size","16"),("fill","#9fb0e0")]
        s!"key = [q^{pi+1}] j = {abbrevInt key}",
      Svg.text [("x","40"),("y","968"),("font-size","13"),("fill","#7e8bbf")]
        s!"entire circle rotated by {wheelDeg pi}°  (q-residue {rotOfPage pi} of 194)   ·   atoms fixed on the wheel, only the q-expansion turns it",
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]
    []

/-! ## Chrome -/

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"mbg\" cx=\"50%\" cy=\"40%\" r=\"80%\">" ++
    "<stop offset=\"0%\" stop-color=\"#161c3e\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"mbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#8a2be2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#00c2c2\"/></linearGradient>" ++
  "<filter id=\"mglow\" x=\"-60%\" y=\"-60%\" width=\"220%\" height=\"220%\">" ++
    "<feGaussianBlur stdDeviation=\"2.4\"/></filter>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1320 86 "url(#mbanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","56"),("y","68"),("font-size","34"),("font-weight","800"),
                ("fill","#0b0c18"),("letter-spacing","1")]
        "MOONSHINE FLIP-BOOK · 194 IRREPS · 104 j-EXPANSION FRAMES",
      Svg.text [("x","58"),("y","96"),("font-size","14"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "every atom projected into the Monster's 194 irreducible representations; the q-expansion of j turns the pages" ]

/-! ## Assembly -/

/-- Build the full moonshine flip-book SVG document string.

The ring, the irrep labels and every atom are gathered into **one** group that
carries `wheelTransform`, so the q-expansion rotates the *entire circle* as a
single rigid body (the requested "project the entire circle into the current
q-expansion").  The HUD stays fixed outside the rotating group. -/
def buildFlipbook (atoms : List DeclAtom) : String :=
  let halos := atoms.map atomHalo
  let markers := atoms.map atomMarker
  let wheel := group (wheelTransform :: irrepRing :: irrepLabels :: (halos ++ markers))
  let huds := group ((List.range numPages).map hudFrame)
  let doc := document 1380 1000
    [ Svg.raw defsRaw,
      rect 0 0 1380 1000 "url(#mbg)" "none" [],
      banner,
      wheel,
      huds,
      Svg.text [("x","40"),("y","990"),("font-size","11"),("fill","#5a6790")]
        "generated natively by Lean · j computed from E4³/Δ · faithful e.hash.toNat → (h mod 194) projection · #writemoonshine" ]
  render doc

/-! ## Commands -/

/-- `#moonshine` builds the flip-book and reports its size. -/
syntax (name := moonshineCmd) "#moonshine" : command

@[command_elab moonshineCmd]
def elabMoonshine : CommandElab := fun _ => do
  let atoms ← projectAtoms
  let svg := buildFlipbook atoms
  logInfo s!"[Moonshine Flip-book] projected {atoms.length} atoms into {numIrreps} irreps across {numPages} j-expansion pages → {svg.length}-byte animated SVG."

/-- `#writemoonshine "path"` writes the flip-book SVG to `path`. -/
syntax (name := writemoonshineCmd) "#writemoonshine " str : command

@[command_elab writemoonshineCmd]
def elabWritemoonshine : CommandElab := fun stx => do
  match stx with
  | `(#writemoonshine $p:str) => do
    let path := p.getString
    let atoms ← projectAtoms
    let svg := buildFlipbook atoms
    IO.FS.writeFile path svg
    logInfo s!"[Moonshine Flip-book] wrote {svg.length} bytes ({atoms.length} atoms, {numPages} pages) to {path}"
  | _ => throwError "ill-formed #writemoonshine command"

/-! ## Build-time generation -/

#moonshine

#writemoonshine "atlas_moonshine.svg"

end MoonshineSVG

import RequestProject.FractranBiome
import RequestProject.Moonshine
import RequestProject.SVG
import Lean

/-!
# FractranBiomeSVG: PRIMEGAME's moonshine walk as a q-expansion flip-book

This layer **visualises the FRACTRAN-to-moonshine lift** of `FractranBiome`: it
runs Conway's PRIMEGAME and plays its trajectory back as an animated SVG
flip-book whose **104 pages are the q-expansion terms `q¹ … q¹⁰⁴` of the
j-invariant**, exactly as requested ("visualize it on the q-expansion from
1–104").

* The **194 irreps** are drawn once as a faint background ring (the Monster's
  194 biomes).
* PRIMEGAME is traced **one step per q-page**: page `p` (for `p = 1 … 104`) shows
  the machine's state after `p−1` steps, lit up in its biome `n % 194` on the
  ring.  Turning the 104 pages plays the whole computation back as a video.
* The **trajectory trail** — the polyline through every visited biome — is drawn
  faintly underneath, so you can see the path the program carves through the
  Monster's representation theory.
* **Primes light up.**  Whenever the state is a pure power of two `2^k` (the
  PRIMEGAME states that witness a prime `k`), the marker flares gold: those are
  the prime-generating events.
* Each page's **q-coefficient key** `[q^p] j` is shown in the HUD, together with
  the current state, its biome, and its 15-prime Monster address.

Commands:

* `#fractranbiome`            — build the flip-book and report its size.
* `#writefractranbiome "path"` — write the flip-book SVG to `path`.
-/

open Lean Elab Command SVG

namespace FractranBiomeSVG

open FractranBiome FractranWalk MoonshineAddress Moonshine

/-! ## Geometry: the 194-irrep ring -/

def ringCx : Float := 700.0
def ringCy : Float := 500.0
def ringR  : Float := 380.0

/-- Position of irrep `i` (`0 ≤ i < 194`) on the ring. -/
def irrepPos (i : Nat) : Int × Int :=
  let a := 2.0 * 3.14159265358979 * (Float.ofNat i) / (Float.ofNat numIrreps) - 1.5707963
  let x := ringCx + ringR * Float.cos a
  let y := ringCy + ringR * Float.sin a
  (x.toInt64.toInt, y.toInt64.toInt)

/-- The number of flip-book pages (q-expansion terms `q¹ … q¹⁰⁴`). -/
def numPages : Nat := 104

/-! ## The trajectory data (computed natively) -/

/-- The state of PRIMEGAME at step `t`. -/
def stateAt (t : Nat) : Nat := fractranState primegame 2 t

/-- The biome (primary irrep) of PRIMEGAME at step `t`. -/
def biomeAt (t : Nat) : Nat := stateAt t % numIrreps

/-- Is `n` a pure power of two (`n = 2^k`, `k ≥ 0`)?  These are PRIMEGAME's
prime-witnessing states. -/
def isPow2 : Nat → Bool
  | 0 => false
  | 1 => true
  | n => if n % 2 == 0 then isPow2Aux 64 (n / 2) else false
where
  isPow2Aux : Nat → Nat → Bool
    | 0,        _ => false
    | _,        1 => true
    | fuel + 1, m => if m % 2 == 0 then isPow2Aux fuel (m / 2) else false

/-! ## Flip-book value strings -/

/-- A ';'-joined list of `len` strings, each `f i`. -/
def joinValues (len : Nat) (f : Nat → String) : String :=
  String.intercalate ";" ((List.range len).map f)

/-- The `j`-coefficient keying page index `pi` (0-based): coefficient of `q^{pi+1}`. -/
def keyOfPage (pi : Nat) : Int := jCoeff (pi + 2)

/-! ## The trajectory trail -/

/-- The faint polyline through every visited biome over the 104 traced steps. -/
def trail : Svg :=
  let pts := (List.range numPages).map (fun t =>
    let (x, y) := irrepPos (biomeAt t)
    s!"{x},{y}")
  Svg.elem "polyline"
    [("points", String.intercalate " " pts),
     ("fill", "none"), ("stroke", "#39507f"),
     ("stroke-width", "1.2"), ("opacity", "0.45")] []

/-! ## The entire path, shown at once and coloured along the q-expansion -/

/-- The hue (`0 … 359`) assigned to q-page `t` from its j-coefficient.  This is
the single colour channel that carries the q-expansion onto the static path. -/
def hueOfPage (t : Nat) : Nat := ((keyOfPage t).emod 360).toNat

/-- **The whole FRACTRAN path drawn in one view**, with each segment coloured by
the q-expansion coefficient that keys it.  The path geometry is *fixed* (the
entire elliptic-curve-like trajectory is visible at once); the colour gradient
along it *is* the q-expansion.  This pins the second variable: the fractran walk
no longer moves — only the q-expansion does, mapped along the fixed curve. -/
def coloredPath : Svg :=
  group ((List.range (numPages - 1)).map (fun t =>
    let (x1, y1) := irrepPos (biomeAt t)
    let (x2, y2) := irrepPos (biomeAt (t + 1))
    line x1 y1 x2 y2 s!"hsl({hueOfPage t},85%,58%)"
      [("stroke-width","3"),("stroke-linecap","round"),("opacity","0.92")]))

/-- A small node at every visited biome, so the discrete steps along the
continuous path are visible. -/
def pathNodes : Svg :=
  group ((List.range numPages).map (fun t =>
    let (x, y) := irrepPos (biomeAt t)
    circle x y 2 s!"hsl({hueOfPage t},85%,70%)" "#05060f" [("opacity","0.9")]))

/-! ## The static irrep ring -/

/-- The 194 irrep nodes drawn once (the Monster's 194 biomes). -/
def irrepRing : Svg :=
  group ((List.range numIrreps).map (fun i =>
    let (x, y) := irrepPos i
    circle x y 2 "#2a3160" "#0b0c18" [("opacity", "0.6")]))

/-! ## The travelling marker (one step per q-page) -/

/-- The **q-expansion cursor**: a single marker that glides along the
*already-drawn* path as the q-expansion advances (`q¹ … q¹⁰⁴`), flaring gold on
pure powers of two (the prime-generating states).  The path itself is static, so
this cursor is the only thing in motion — it shows where in the fixed curve the
current q-term sits. -/
def walker : Svg :=
  let xs := joinValues numPages (fun t => toString (irrepPos (biomeAt t)).1)
  let ys := joinValues numPages (fun t => toString (irrepPos (biomeAt t)).2)
  -- radius/colour pulse: gold + large on powers of two, cyan otherwise
  let rs := joinValues numPages (fun t => if isPow2 (stateAt t) then "10" else "5")
  let cs := joinValues numPages (fun t => if isPow2 (stateAt t) then "#ffd700" else "#00e0d0")
  let (sx, sy) := irrepPos (biomeAt 0)
  group
    [ -- glow halo
      circle sx sy 12 "none" "#ffd700" [("opacity","0.30"),("filter","url(#fglow)")],
      Svg.raw s!"<animate attributeName=\"cx\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{xs}\"/>",
      Svg.raw s!"<animate attributeName=\"cy\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{ys}\"/>",
      -- core marker
      Svg.elem "circle"
        [("cx", toString sx), ("cy", toString sy), ("r", "5"),
         ("fill", "#00e0d0"), ("stroke", "#05060f"), ("stroke-width","1.4")]
        [ Svg.raw s!"<animate attributeName=\"cx\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{xs}\"/>",
          Svg.raw s!"<animate attributeName=\"cy\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"linear\" values=\"{ys}\"/>",
          Svg.raw s!"<animate attributeName=\"r\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{rs}\"/>",
          Svg.raw s!"<animate attributeName=\"fill\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{cs}\"/>" ] ]
    []

/-! ## The HUD (page number, state, biome, q-coefficient key, one per page) -/

/-- Abbreviate a big integer for the HUD. -/
def abbrevInt (z : Int) : String :=
  let s := toString z
  if s.length ≤ 20 then s
  else (s.take 14).toString ++ "… (" ++ toString s.length ++ " digits)"

/-- One HUD frame for page index `pi`, visible only during its 1/104 time slot. -/
def hudFrame (pi : Nat) : Svg :=
  let vis := joinValues numPages (fun q => if q == pi then "1" else "0")
  let n := stateAt pi
  let prime := isPow2 n
  group
    [ Svg.text [("x","40"),("y","952"),("font-size","22"),("font-weight","800"),
                ("fill","#ffd700")]
        s!"q^{pi+1} / 104   ·   PRIMEGAME step {pi}",
      Svg.text [("x","40"),("y","978"),("font-size","15"),("fill","#9fb0e0")]
        s!"state n = {n}   ·   biome (irrep n mod 194) = {biomeAt pi}   ·   key [q^{pi+1}] j = {abbrevInt (keyOfPage pi)}",
      Svg.text [("x","40"),("y","1000"),("font-size","13"),
                ("fill", if prime then "#ffd700" else "#7e8bbf")]
        (if prime then s!"★ pure power of two — a PRIME is generated"
         else s!"address mod (71,59,47,…,2) carries n through Monster-prime space"),
      Svg.raw s!"<animate attributeName=\"opacity\" dur=\"52s\" repeatCount=\"indefinite\" calcMode=\"discrete\" values=\"{vis}\"/>" ]
    []

/-! ## Chrome -/

def defsRaw : String :=
  "<defs>" ++
  "<radialGradient id=\"fbg\" cx=\"50%\" cy=\"40%\" r=\"80%\">" ++
    "<stop offset=\"0%\" stop-color=\"#161c3e\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"fbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#8a2be2\"/></linearGradient>" ++
  "<filter id=\"fglow\" x=\"-80%\" y=\"-80%\" width=\"260%\" height=\"260%\">" ++
    "<feGaussianBlur stdDeviation=\"3.0\"/></filter>" ++
  "</defs>"

def banner : Svg :=
  group
    [ rect 30 22 1340 86 "url(#fbanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","56"),("y","68"),("font-size","30"),("font-weight","800"),
                ("fill","#0b0c18"),("letter-spacing","1")]
        "FRACTRAN PRIMEGAME · MOONSHINE WALK · 104 q-EXPANSION FRAMES",
      Svg.text [("x","58"),("y","96"),("font-size","14"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "the entire PRIMEGAME trajectory shown at once as one coloured curve; the colour along it IS the q-expansion of j, and the cursor marks the current q-term" ]

/-! ## Assembly -/

/-- Build the full PRIMEGAME moonshine-walk flip-book SVG document string. -/
def buildFlipbook : String :=
  let huds := group ((List.range numPages).map hudFrame)
  let doc := document 1400 1040
    [ Svg.raw defsRaw,
      rect 0 0 1400 1040 "url(#fbg)" "none" [],
      banner,
      irrepRing,
      coloredPath,
      pathNodes,
      walker,
      huds,
      Svg.text [("x","40"),("y","1028"),("font-size","11"),("fill","#5a6790")]
        "generated natively by Lean · PRIMEGAME run via fractranState · biome = n mod 194 · one q-expansion term per step · #writefractranbiome" ]
  render doc

/-! ## Commands -/

/-- `#fractranbiome` builds the flip-book and reports its size. -/
syntax (name := fractranbiomeCmd) "#fractranbiome" : command

@[command_elab fractranbiomeCmd]
def elabFractranbiome : CommandElab := fun _ => do
  let svg := buildFlipbook
  logInfo s!"[PRIMEGAME Flip-book] traced Conway's PRIMEGAME across {numPages} q-expansion pages through {numIrreps} Monster biomes → {svg.length}-byte animated SVG."

/-- `#writefractranbiome "path"` writes the flip-book SVG to `path`. -/
syntax (name := writefractranbiomeCmd) "#writefractranbiome " str : command

@[command_elab writefractranbiomeCmd]
def elabWritefractranbiome : CommandElab := fun stx => do
  match stx with
  | `(#writefractranbiome $p:str) => do
    let path := p.getString
    let svg := buildFlipbook
    IO.FS.writeFile path svg
    logInfo s!"[PRIMEGAME Flip-book] wrote {svg.length} bytes ({numPages} q-pages) to {path}"
  | _ => throwError "ill-formed #writefractranbiome command"

/-! ## Build-time generation -/

#fractranbiome

#writefractranbiome "atlas_fractran.svg"

end FractranBiomeSVG

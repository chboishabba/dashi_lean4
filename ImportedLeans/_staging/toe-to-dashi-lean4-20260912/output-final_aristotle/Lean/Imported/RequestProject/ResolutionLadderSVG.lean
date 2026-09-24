import RequestProject.SVG
import Lean

/-!
# ResolutionLadderSVG — the resolution-ladder report, rendered as an SVG

`ResolutionLadder.#resladder` (and the bounded `#resladder_sample n`) classify
every irrep-1 *smush* — a collision of declaration statement fingerprints in the
`196883`-cell space — as **geometric** (the colliding declarations separate once
enough Monster primes are added, i.e. they split at a richer irrep) or
**semantic** (they coincide even at the full fifteen-prime resolution).  The
result is written to `atlas_resladder.json`:

```json
{
  "totalDecls": 120000,
  "baseCells": 82213,
  "smushGroups": 22394,
  "geometricGroups": 20422,
  "semanticGroups": 1972,
  "fullModulus": 1618964990108856390,
  "ladder": [ { "irrep": 192, "modulus": 208311270618, "splits": 20422 }, … ]
}
```

This layer renders **that exact JSON** as a static dashboard: the geometric vs.
semantic split of the smushes, the base-cell occupancy, and the ten-rung ladder
of the heaviest Monster irreps with each rung's modulus and splitting power.

Commands:

* `#resladdercard`           — read the JSON, build the card, report its size.
* `#writeresladder "path"`   — read the JSON, build the card, write SVG to `path`.

The default build reads `atlas_resladder.json` and writes `atlas_resladder.svg`.
-/

open Lean Elab Command SVG

namespace ResolutionLadderSVG

/-! ## §1  The parsed JSON record -/

/-- One rung of the ladder as read from the JSON. -/
structure Rung where
  irrep   : Nat
  modulus : Nat
  splits  : Nat
  deriving Inhabited

/-- The scalar fields plus the ladder array of `atlas_resladder.json`. -/
structure LadderCard where
  totalDecls      : Nat
  baseCells       : Nat
  smushGroups     : Nat
  geometricGroups : Nat
  semanticGroups  : Nat
  fullModulus     : Nat
  ladder          : Array Rung
  deriving Inhabited

/-- Pull a `Nat` field out of a `Json` object, defaulting to `0`. -/
def jNat (j : Json) (k : String) : Nat :=
  match j.getObjVal? k with
  | .ok v => match v.getNat? with
             | .ok n => n
             | .error _ => match v.getInt? with
                           | .ok i => i.toNat
                           | .error _ => 0
  | .error _ => 0

/-- Parse the full JSON text into a `LadderCard`. -/
def parseCard (txt : String) : Except String LadderCard := do
  let j ← Json.parse txt
  let rungs : Array Rung :=
    match j.getObjVal? "ladder" with
    | .ok v => match v.getArr? with
               | .ok a => a.map (fun e =>
                   { irrep := jNat e "irrep", modulus := jNat e "modulus",
                     splits := jNat e "splits" })
               | .error _ => #[]
    | .error _ => #[]
  return {
    totalDecls      := jNat j "totalDecls"
    baseCells       := jNat j "baseCells"
    smushGroups     := jNat j "smushGroups"
    geometricGroups := jNat j "geometricGroups"
    semanticGroups  := jNat j "semanticGroups"
    fullModulus     := jNat j "fullModulus"
    ladder          := rungs }

/-! ## §2  Geometry and helpers -/

def canvasW : Nat := 1480
def canvasH : Nat := 1120

/-- The number of cells in the smallest non-trivial Monster irrep,
`71 × 59 × 47`. -/
def irrep1Cells : Nat := 196883

/-- Insert thousands separators into a `Nat`'s decimal form. -/
def commafy (n : Nat) : String :=
  let ds := (toString n).toList.reverse
  let rec go : List Char → Nat → List Char
    | [], _ => []
    | c :: cs, k =>
      let sep := if k != 0 && k % 3 == 0 then [','] else []
      (sep ++ [c]) ++ go cs (k + 1)
  String.ofList (go ds 0).reverse

/-! ## §3  Drawing primitives -/

/-- A two-segment split bar: `a` (colour `ca`) then `b` (colour `cb`). -/
def splitBar (x y w : Int) (label : String) (a b : Nat) (ca cb : String) : Svg :=
  let h : Int := 34
  let total := a + b
  let aw : Int :=
    if total == 0 then 0
    else (Float.ofNat w.toNat * (Float.ofNat a / Float.ofNat total)).toInt64.toInt
  group
    [ Svg.text [("x", toString x),("y", toString (y - 8)),("font-size","15"),
                ("font-weight","700"),("fill","#cdd6ff")] label,
      rect x y w h "#12183a" "#2a335f" [("rx","6"),("stroke-width","1")],
      rect x y aw h ca "none" [("rx","6"),("opacity","0.92")],
      rect (x + aw) y (w - aw) h cb "none" [("opacity","0.92")],
      Svg.text [("x", toString (x + w + 12)),("y", toString (y + 23)),
                ("font-size","14"),("fill","#9fb0e0")]
        s!"{commafy a} · {commafy b}" ]

/-- A labelled horizontal progress bar: `filled` of `total`. -/
def progressBar (x y w : Int) (label : String) (filled total : Nat)
    (barColor : String) : Svg :=
  let h : Int := 34
  let frac : Float :=
    if total == 0 then 0.0 else min 1.0 (Float.ofNat filled / Float.ofNat total)
  let fw : Int := (Float.ofNat w.toNat * frac).toInt64.toInt
  let pct : Nat := (frac * 1000.0).toInt64.toInt.toNat
  group
    [ Svg.text [("x", toString x),("y", toString (y - 8)),("font-size","15"),
                ("font-weight","700"),("fill","#cdd6ff")] label,
      rect x y w h "#12183a" "#2a335f" [("rx","6"),("stroke-width","1")],
      rect x y fw h barColor "none" [("rx","6"),("opacity","0.92")],
      Svg.text [("x", toString (x + w + 12)),("y", toString (y + 23)),
                ("font-size","14"),("fill","#9fb0e0")]
        s!"{commafy filled} / {commafy total}  ({pct / 10}.{pct % 10}%)" ]

/-- A small stat tile: big number over a caption. -/
def statTile (x y w h : Int) (value caption accent : String) : Svg :=
  group
    [ rect x y w h "#0e1430" "#27305c" [("rx","10"),("stroke-width","1.2")],
      rect x y 6 h accent "none" [("rx","3")],
      Svg.text [("x", toString (x + 20)),("y", toString (y + 40)),
                ("font-size","26"),("font-weight","800"),("fill","#ffd700")]
        value,
      Svg.text [("x", toString (x + 20)),("y", toString (y + 66)),
                ("font-size","13"),("fill","#9fb0e0")] caption ]

/-- One row of the ladder table: rung index, irrep, modulus, and a splitting bar. -/
def rungRow (i : Nat) (r : Rung) (smushGroups : Nat) (x y w : Int) : Svg :=
  let h : Int := 40
  let barW : Int := 360
  let frac : Float :=
    if smushGroups == 0 then 0.0
    else min 1.0 (Float.ofNat r.splits / Float.ofNat smushGroups)
  let fw : Int := (Float.ofNat barW.toNat * frac).toInt64.toInt
  group
    [ rect x y w h "#0c1230" "#222c55" [("rx","8"),("stroke-width","1")],
      Svg.text [("x", toString (x + 16)),("y", toString (y + 26)),
                ("font-size","15"),("font-weight","800"),("fill","#7fe3ff")]
        s!"rung {i + 1}",
      Svg.text [("x", toString (x + 110)),("y", toString (y + 26)),
                ("font-size","15"),("font-weight","700"),("fill","#ffd700")]
        s!"irrep {r.irrep}",
      Svg.text [("x", toString (x + 250)),("y", toString (y + 26)),
                ("font-size","13"),("fill","#cdd6ff")]
        s!"modulus {commafy r.modulus}",
      rect (x + w - barW - 200) (y + 9) barW 22 "#12183a" "#2a335f"
        [("rx","5"),("stroke-width","1")],
      rect (x + w - barW - 200) (y + 9) fw 22 "#ff7f50" "none" [("rx","5"),("opacity","0.92")],
      Svg.text [("x", toString (x + w - 188)),("y", toString (y + 26)),
                ("font-size","13"),("fill","#9fb0e0")]
        s!"splits {commafy r.splits} smushes" ]

/-! ## §4  Definitions and banner -/

def defsRaw : String :=
  "<defs><radialGradient id=\"rbg\" cx=\"42%\" cy=\"24%\" r=\"100%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"rbanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#00c2c2\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#ff7f50\"/></linearGradient></defs>"

def banner (c : LadderCard) : Svg :=
  group
    [ rect 24 20 1432 96 "url(#rbanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","48"),("y","58"),("font-size","26"),("font-weight","800"),
                ("fill","#0b0c18")]
        "RESOLUTION LADDER · SPLITTING IRREP-1 SMUSHES BY ADDING MONSTER PRIMES",
      Svg.text [("x","50"),("y","86"),("font-size","14"),("font-weight","700"),
                ("fill","#1a1f3c")]
        s!"{commafy c.smushGroups} irrep-1 smush groups · {commafy c.geometricGroups} geometric (split) · {commafy c.semanticGroups} semantic (persist) · from atlas_resladder.json",
      Svg.text [("x","50"),("y","106"),("font-size","12"),("font-weight","600"),
                ("fill","#1a1f3c")]
        s!"scanned {commafy c.totalDecls} declarations · base cell = h mod 196883 (= crtTriple) · ladder = the 10 heaviest irreps by p-adic valuation" ]

/-! ## §5  Assembling the card -/

/-- Build the full dashboard SVG from the parsed card. -/
def buildCard (c : LadderCard) : String :=
  let tiles : List Svg :=
    let gx : Int := 40
    let gy : Int := 360
    let tw : Int := 336
    let th : Int := 86
    let gap : Int := 16
    let col := fun (i : Int) => gx + i * (tw + gap)
    [ statTile (col 0) gy tw th (commafy c.smushGroups) "irrep-1 smush groups (≥2 decls)" "#ff7f50",
      statTile (col 1) gy tw th (commafy c.geometricGroups) "geometric — split by the ladder" "#9fe0b0",
      statTile (col 2) gy tw th (commafy c.semanticGroups) "semantic — persist to full address" "#ff3b5c",
      statTile (col 3) gy tw th (commafy c.baseCells) "irrep-1 base cells used" "#9b8cff" ]
  let bars : List Svg :=
    [ progressBar 40 180 980 "irrep-1 base cells used of capacity (71×59×47 = 196883)"
        c.baseCells irrep1Cells "#ffd700",
      splitBar 40 270 980 "geometric (splittable) vs. semantic (persistent) smushes"
        c.geometricGroups c.semanticGroups "#9fe0b0" "#ff3b5c" ]
  let ladderTitle : Svg :=
    Svg.text [("x","40"),("y","520"),("font-size","18"),("font-weight","800"),
              ("fill","#ffd700")]
      "THE TEN-RUNG LADDER — heaviest Monster irreps (192, 174, 180, 101, 102, 139, 122, 123, 124, 132)"
  let rows : List Svg :=
    c.ladder.toList.zipIdx.map (fun (r, i) => rungRow i r c.smushGroups 40 (540 + Int.ofNat i * 48) 1400)
  let note : Svg :=
    Svg.text [("x","40"),("y", toString (Int.ofNat canvasH - 36)),("font-size","13"),
              ("fill","#9fb0e0")]
      s!"semantic smushes agree modulo the full radical {commafy c.fullModulus} = 2·3·5·…·71 ⇒ identical 15-prime address (ResolutionLadder.semantic_smush_is_identical)"
  let doc := document canvasW canvasH
    ([ Svg.raw defsRaw,
       rect 0 0 (Int.ofNat canvasW) (Int.ofNat canvasH) "url(#rbg)" "none" [],
       banner c ]
     ++ bars ++ tiles ++ [ladderTitle] ++ rows ++ [note,
       Svg.text [("x","40"),("y", toString (Int.ofNat canvasH - 14)),
                 ("font-size","11"),("fill","#5a6790")]
         "source: atlas_resladder.json (ResolutionLadder.#resladder) · coarsen: m ∣ M ⇒ collide mod M ⇒ collide mod m · #writeresladder"])
  render doc

/-! ## §6  Commands -/

/-- The JSON file produced by `ResolutionLadder.#resladder`. -/
def jsonPath : String := "atlas_resladder.json"

/-- Read and parse `atlas_resladder.json`. -/
def loadCard : CommandElabM LadderCard := do
  let txt ← IO.FS.readFile jsonPath
  match parseCard txt with
  | .ok c => return c
  | .error e => throwError s!"failed to parse {jsonPath}: {e}"

/-- `#resladdercard` reads the JSON, builds the dashboard, and reports its size. -/
syntax (name := resladdercardCmd) "#resladdercard" : command

@[command_elab resladdercardCmd]
def elabResladdercard : CommandElab := fun _ => do
  let c ← loadCard
  let svg := buildCard c
  logInfo s!"[Resolution Ladder Card] {commafy c.smushGroups} smushes → {commafy c.geometricGroups} geometric / {commafy c.semanticGroups} semantic → {svg.length}-byte SVG."

/-- `#writeresladder "path"` reads the JSON, builds the card, and writes the SVG. -/
syntax (name := writeresladderCmd) "#writeresladder " str : command

@[command_elab writeresladderCmd]
def elabWriteresladder : CommandElab := fun stx => do
  match stx with
  | `(#writeresladder $p:str) => do
    let path := p.getString
    let c ← loadCard
    let svg := buildCard c
    IO.FS.writeFile path svg
    logInfo s!"[Resolution Ladder Card] wrote {svg.length} bytes to {path}"
  | _ => throwError "ill-formed #writeresladder command"

/-! ## §7  Build-time generation -/

#resladdercard

#writeresladder "atlas_resladder.svg"

end ResolutionLadderSVG

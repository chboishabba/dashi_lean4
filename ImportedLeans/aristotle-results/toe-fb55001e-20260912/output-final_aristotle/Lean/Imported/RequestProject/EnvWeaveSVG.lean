import RequestProject.SVG
import Lean

/-!
# EnvWeaveSVG — the corpus scan summary (`atlas_envweave.json`), rendered as an SVG

`EnvWeave.#envweave` streams the *entire* ambient environment (Lean core,
Batteries/Std, Mathlib, and this project) into the `196883`-cell address space of
the smallest non-trivial Monster irrep, and writes a compact JSON summary to
`atlas_envweave.json`:

```json
{
  "totalDecls": 708123,
  "totalNodes": 1950655588,
  "distinctStmtCells": 186387,
  "distinctProofCells": 188142,
  "smushCount": 521736,
  "faithfulCount": 707172,
  "saturationIrrep": 194,
  "saturationModulus": 1,
  "deepestDecl": "SheafOfModules.Presentation.map._proof_6",
  "deepestCount": 68071930,
  "arithmetization": 2994870043851426
}
```

This layer renders **that exact JSON file** as a static infographic dashboard.
At elaboration time the command reads `atlas_envweave.json`, parses it with
`Lean.Json`, and draws:

* a header banner with the corpus headline (declaration / node totals);
* the **statement-cell occupancy bar** — `distinctStmtCells` filled against the
  `196883` capacity of the irrep-1 cell space, with the forced overflow (the
  corpus has more declarations than cells, so the pigeonhole bound applies);
* a **faithful vs. smushed** split bar over all declarations;
* the **proof-cell occupancy bar**;
* a stat grid of every scalar field in the JSON; and
* the deepest declaration callout and the corpus arithmetization.

Everything drawn comes straight from the JSON the scan emitted, so the picture is
faithful to `EnvWeave`'s recorded result.

Commands:

* `#envweavecard`               — read the JSON, build the card, report its size.
* `#writeenvweave "path"`       — read the JSON, build the card, write SVG to `path`.

The default build reads `atlas_envweave.json` and writes `atlas_envweave.svg`.
-/

open Lean Elab Command SVG

namespace EnvWeaveSVG

/-! ## §1  The parsed JSON record -/

/-- The scalar fields of `atlas_envweave.json`. -/
structure EnvStats where
  totalDecls         : Nat
  totalNodes         : Nat
  distinctStmtCells  : Nat
  distinctProofCells : Nat
  smushCount         : Nat
  faithfulCount      : Nat
  saturationIrrep    : Nat
  saturationModulus  : Nat
  deepestDecl        : String
  deepestCount       : Nat
  arithmetization    : Nat
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

/-- Pull a `String` field out of a `Json` object, defaulting to `""`. -/
def jStr (j : Json) (k : String) : String :=
  match j.getObjVal? k with
  | .ok v => match v.getStr? with
             | .ok s => s
             | .error _ => ""
  | .error _ => ""

/-- Parse the full JSON text into an `EnvStats`. -/
def parseStats (txt : String) : Except String EnvStats := do
  let j ← Json.parse txt
  return {
    totalDecls         := jNat j "totalDecls"
    totalNodes         := jNat j "totalNodes"
    distinctStmtCells  := jNat j "distinctStmtCells"
    distinctProofCells := jNat j "distinctProofCells"
    smushCount         := jNat j "smushCount"
    faithfulCount      := jNat j "faithfulCount"
    saturationIrrep    := jNat j "saturationIrrep"
    saturationModulus  := jNat j "saturationModulus"
    deepestDecl        := jStr j "deepestDecl"
    deepestCount       := jNat j "deepestCount"
    arithmetization    := jNat j "arithmetization" }

/-! ## §2  Geometry and helpers -/

def canvasW : Nat := 1480
def canvasH : Nat := 1000

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

/-- A labelled horizontal progress bar: `filled` of `total`, drawn at `(x,y)`
with width `w`.  Returns the bar group plus its caption. -/
def progressBar (x y w : Int) (label : String) (filled total : Nat)
    (barColor : String) : Svg :=
  let h : Int := 30
  let frac : Float :=
    if total == 0 then 0.0 else min 1.0 (Float.ofNat filled / Float.ofNat total)
  let fw : Int := (Float.ofNat w.toNat * frac).toInt64.toInt
  let pct : Nat := (frac * 1000.0).toInt64.toInt.toNat
  group
    [ Svg.text [("x", toString x),("y", toString (y - 8)),("font-size","15"),
                ("font-weight","700"),("fill","#cdd6ff")] label,
      rect x y w h "#12183a" "#2a335f" [("rx","6"),("stroke-width","1")],
      rect x y fw h barColor "none" [("rx","6"),("opacity","0.92")],
      Svg.text [("x", toString (x + w + 12)),("y", toString (y + 21)),
                ("font-size","14"),("fill","#9fb0e0")]
        s!"{commafy filled} / {commafy total}  ({pct / 10}.{pct % 10}%)" ]

/-- A two-segment split bar: `a` (colour `ca`) then `b` (colour `cb`). -/
def splitBar (x y w : Int) (label : String) (a b : Nat) (ca cb : String) : Svg :=
  let h : Int := 30
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
      Svg.text [("x", toString (x + w + 12)),("y", toString (y + 21)),
                ("font-size","14"),("fill","#9fb0e0")]
        s!"{commafy a} · {commafy b}" ]

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

/-! ## §4  Definitions and banner -/

def defsRaw : String :=
  "<defs><radialGradient id=\"ebg\" cx=\"42%\" cy=\"24%\" r=\"100%\">" ++
    "<stop offset=\"0%\" stop-color=\"#141a3a\"/><stop offset=\"100%\" stop-color=\"#05060f\"/></radialGradient>" ++
  "<linearGradient id=\"ebanner\" x1=\"0\" y1=\"0\" x2=\"1\" y2=\"0\">" ++
    "<stop offset=\"0%\" stop-color=\"#2a7fff\"/><stop offset=\"50%\" stop-color=\"#ffd700\"/><stop offset=\"100%\" stop-color=\"#ff3b5c\"/></linearGradient></defs>"

def banner (s : EnvStats) : Svg :=
  group
    [ rect 24 20 1432 96 "url(#ebanner)" "#0b0c18" [("rx","14"),("stroke-width","3")],
      Svg.text [("x","48"),("y","58"),("font-size","27"),("font-weight","800"),
                ("fill","#0b0c18")]
        "ENV WEAVE · WHOLE-ENVIRONMENT SCAN → MONSTER IRREP-1 CELL SPACE (71×59×47 = 196883)",
      Svg.text [("x","50"),("y","86"),("font-size","14"),("font-weight","700"),
                ("fill","#1a1f3c")]
        s!"{commafy s.totalDecls} declarations · {commafy s.totalNodes} AST+payload nodes · rendered from atlas_envweave.json",
      Svg.text [("x","50"),("y","106"),("font-size","12"),("font-weight","600"),
                ("fill","#1a1f3c")]
        "Lean core + Batteries/Std + Mathlib + this project · each declaration → its statement/proof CRT cell" ]

/-! ## §5  Assembling the card -/

/-- Build the full infographic SVG from the parsed stats. -/
def buildCard (s : EnvStats) : String :=
  -- stat grid: 4 columns
  let gx : Int := 40
  let gy : Int := 720
  let tw : Int := 336
  let th : Int := 86
  let gap : Int := 16
  let col := fun (i : Int) => gx + i * (tw + gap)
  let tiles : List Svg :=
    [ statTile (col 0) gy tw th (commafy s.totalDecls) "declarations scanned" "#2a7fff",
      statTile (col 1) gy tw th (commafy s.totalNodes) "AST + payload nodes" "#00c2c2",
      statTile (col 2) gy tw th (commafy s.distinctStmtCells) "distinct statement cells" "#ffd700",
      statTile (col 3) gy tw th (commafy s.distinctProofCells) "distinct proof cells" "#9b8cff",
      statTile (col 0) (gy + th + gap) tw th (commafy s.smushCount) "statement-cell smushes" "#ff3b5c",
      statTile (col 1) (gy + th + gap) tw th (commafy s.faithfulCount) "faithful (< 196883 nodes)" "#9fe0b0",
      statTile (col 2) (gy + th + gap) tw th
        s!"#{s.saturationIrrep} (dim {s.saturationModulus})" "saturation irrep" "#ff9f43",
      statTile (col 3) (gy + th + gap) tw th (commafy s.arithmetization) "corpus arithmetization" "#7fe3ff" ]
  let bars : List Svg :=
    [ progressBar 40 200 980 "statement cells used of irrep-1 capacity (71×59×47)"
        s.distinctStmtCells irrep1Cells "#ffd700",
      progressBar 40 280 980 "proof cells used of irrep-1 capacity"
        s.distinctProofCells irrep1Cells "#9b8cff",
      splitBar 40 360 980 "faithful vs. smushed declarations"
        s.faithfulCount s.smushCount "#9fe0b0" "#ff3b5c" ]
  let deepest : List Svg :=
    [ rect 40 430 1400 120 "#0e1430" "#27305c" [("rx","12"),("stroke-width","1.2")],
      Svg.text [("x","60"),("y","466"),("font-size","16"),("font-weight","800"),
                ("fill","#ffd700")] "DEEPEST DECLARATION",
      Svg.text [("x","60"),("y","498"),("font-size","18"),("font-weight","700"),
                ("fill","#cdd6ff")] (SVG.esc s.deepestDecl),
      Svg.text [("x","60"),("y","528"),("font-size","15"),("fill","#9fb0e0")]
        s!"{commafy s.deepestCount} AST + payload nodes — the largest single weave in the corpus" ]
  let overflow : List Svg :=
    [ Svg.text [("x","40"),("y","600"),("font-size","14"),("font-weight","700"),
                ("fill","#ff9fb0")]
        s!"pigeonhole: {commafy s.totalDecls} declarations into {commafy irrep1Cells} statement cells ⇒ collisions forced (DeclWeave.smush_of_overflow)",
      Svg.text [("x","40"),("y","624"),("font-size","13"),("fill","#9fb0e0")]
        s!"overflow margin = {commafy (s.totalDecls - irrep1Cells)} declarations beyond capacity · {commafy s.smushCount} statement-cell smushes recorded" ]
  let doc := document canvasW canvasH
    ([ Svg.raw defsRaw,
       rect 0 0 (Int.ofNat canvasW) (Int.ofNat canvasH) "url(#ebg)" "none" [],
       banner s ]
     ++ bars ++ deepest ++ overflow ++ tiles ++
     [ Svg.text [("x","40"),("y", toString (Int.ofNat canvasH - 14)),
                 ("font-size","11"),("fill","#5a6790")]
         "source: atlas_envweave.json (EnvWeave.#envweave) · capacity 196883 = Monster irrep-1 (71×59×47) · #writeenvweave" ])
  render doc

/-! ## §6  Commands -/

/-- The JSON file produced by `EnvWeave.#envweave`. -/
def jsonPath : String := "atlas_envweave.json"

/-- Read and parse `atlas_envweave.json`. -/
def loadStats : CommandElabM EnvStats := do
  let txt ← IO.FS.readFile jsonPath
  match parseStats txt with
  | .ok s => return s
  | .error e => throwError s!"failed to parse {jsonPath}: {e}"

/-- `#envweavecard` reads the JSON, builds the infographic, and reports its size. -/
syntax (name := envweavecardCmd) "#envweavecard" : command

@[command_elab envweavecardCmd]
def elabEnvweavecard : CommandElab := fun _ => do
  let s ← loadStats
  let svg := buildCard s
  logInfo s!"[Env Weave Card] {commafy s.totalDecls} declarations · {commafy s.distinctStmtCells} stmt cells → {svg.length}-byte SVG."

/-- `#writeenvweave "path"` reads the JSON, builds the card, and writes the SVG. -/
syntax (name := writeenvweaveCmd) "#writeenvweave " str : command

@[command_elab writeenvweaveCmd]
def elabWriteenvweave : CommandElab := fun stx => do
  match stx with
  | `(#writeenvweave $p:str) => do
    let path := p.getString
    let s ← loadStats
    let svg := buildCard s
    IO.FS.writeFile path svg
    logInfo s!"[Env Weave Card] wrote {svg.length} bytes to {path}"
  | _ => throwError "ill-formed #writeenvweave command"

/-! ## §7  Build-time generation -/

#envweavecard

#writeenvweave "atlas_envweave.svg"

end EnvWeaveSVG

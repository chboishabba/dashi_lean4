import Mathlib
import RequestProject.DualAtlas
import RequestProject.DualAtlasCensus
import RequestProject.SVG
import Lean

/-!
# DualAtlasReports — multi-format dual-atlas census reports across four corpora

This module runs the **dual atlas** (`RequestProject.DualAtlas`) over four
distinct slices of the loaded `Environment` and emits the census results in
**four report formats**:

* **JSON**     — machine-readable, one object per corpus;
* **CSV**      — one row per corpus, ready for spreadsheets;
* **Markdown** — a human-readable table plus per-corpus sections;
* **SVG**      — a grouped bar chart visualising the four corpora side by side.

The four corpora ("run it on …") are:

* **itself**     — this very project (`RequestProject.*`);
* **mathlib**    — the whole of Mathlib (`Mathlib.*`);
* **batteries**  — the Batteries standard library (`Batteries.*`);
* **lean4**      — the Lean 4 core / compiler / std (`Lean.*`, `Init.*`, `Std.*`).

For every corpus we compute, over its declarations only:

* the total number of declarations;
* the dual-coordinate field histograms (`cog`/`triad`/`harm`, see `DualAtlas`);
* how many declarations each field is the better coordinate for, both raw
  (`bestField`) and capacity-normalised (`bestFieldRel`);
* the harmonic-cell label distribution (`{0,5,7,11,13}`).

Commands:

* `#dualreports`            — scan all four corpora and write **all 16** per-corpus
  report files plus **4** combined report files under `reports/`.

## Honest scope

The verified content lives in `DualAtlas`/`DualAtlasCensus` (the `bestField`
argmin algebra and the projection range bounds).  Everything here is an
*empirical readout* of the current environment, faithfully serialised; the small
theorems below only certify structural facts about the report scaffolding
(number of corpora / formats and the CSV header arity).
-/

open Lean Elab Command SVG

namespace DualAtlas

/-! ## §1  Corpus classification -/

/-- The four reported corpora, in fixed order (index = corpus code `0..3`). -/
def corpusLabels : Array String := #["itself", "mathlib", "batteries", "lean4"]

/-- Number of reported corpora. -/
def nCorpus : Nat := corpusLabels.size

/-- Classify a *module name* into a corpus code; `none` means "not one of the four
reported corpora" (e.g. other dependencies). -/
def corpusOfModule (mn : String) : Option Nat :=
  if mn.startsWith "RequestProject" then some 0
  else if mn.startsWith "Mathlib" then some 1
  else if mn.startsWith "Batteries" then some 2
  else if mn.startsWith "Lean" || mn.startsWith "Init" || mn.startsWith "Std" then some 3
  else none

/-! ## §2  Per-corpus statistics -/

/-- The census statistics gathered for a single corpus. -/
structure CorpusStats where
  /-- corpus label. -/
  name         : String
  /-- total number of declarations in the corpus. -/
  total        : Nat
  /-- number of distinct occupied `cog` buckets. -/
  cogBuckets   : Nat
  /-- number of distinct occupied `triad` buckets. -/
  triadBuckets : Nat
  /-- number of distinct occupied `harm` buckets. -/
  harmBuckets  : Nat
  /-- declarations best served (raw) by the cognitive field. -/
  cogWins      : Nat
  /-- declarations best served (raw) by the triad field. -/
  triadWins    : Nat
  /-- declarations best served (raw) by the harmonic field. -/
  harmWins     : Nat
  /-- declarations best served (relative) by the cognitive field. -/
  cogWinsRel   : Nat
  /-- declarations best served (relative) by the triad field. -/
  triadWinsRel : Nat
  /-- declarations best served (relative) by the harmonic field. -/
  harmWinsRel  : Nat
  /-- harmonic label populations for codes `0,5,7,11,13`. -/
  harm0        : Nat
  /-- harmonic code 5 (Muse Cycle) population. -/
  harm5        : Nat
  /-- harmonic code 7 (Heptad) population. -/
  harm7        : Nat
  /-- harmonic code 11 (Hemispheres) population. -/
  harm11       : Nat
  /-- harmonic code 13 (Recursion) population. -/
  harm13       : Nat
deriving Repr, Inhabited

/-! ## §3  Verified scaffolding facts -/

/-- The CSV column header for a `CorpusStats` row. -/
def csvHeader : List String :=
  ["corpus", "total", "cogBuckets", "triadBuckets", "harmBuckets",
   "cogWins", "triadWins", "harmWins", "cogWinsRel", "triadWinsRel", "harmWinsRel",
   "harm0", "harm5", "harm7", "harm11", "harm13"]

/-- The CSV data row for one corpus, in the same order as `csvHeader`. -/
def CorpusStats.csvCells (s : CorpusStats) : List String :=
  [s.name, toString s.total, toString s.cogBuckets, toString s.triadBuckets,
   toString s.harmBuckets, toString s.cogWins, toString s.triadWins,
   toString s.harmWins, toString s.cogWinsRel, toString s.triadWinsRel,
   toString s.harmWinsRel, toString s.harm0, toString s.harm5, toString s.harm7,
   toString s.harm11, toString s.harm13]

/-- There are exactly four reported corpora. -/
theorem nCorpus_eq : nCorpus = 4 := by decide

/-- The CSV header has 16 columns. -/
theorem csvHeader_length : csvHeader.length = 16 := by decide

/-- Every `CorpusStats` row has exactly as many cells as the header has columns,
so the emitted CSV is always rectangular. -/
theorem csvCells_length (s : CorpusStats) : s.csvCells.length = csvHeader.length := by
  simp [CorpusStats.csvCells, csvHeader]

/-! ## §4  Formatters -/

/-- Render one corpus as a JSON object. -/
def CorpusStats.toJson (s : CorpusStats) : String :=
  s!"  \{\n" ++
  s!"    \"corpus\": \"{s.name}\",\n" ++
  s!"    \"total\": {s.total},\n" ++
  s!"    \"cogBuckets\": {s.cogBuckets},\n" ++
  s!"    \"triadBuckets\": {s.triadBuckets},\n" ++
  s!"    \"harmBuckets\": {s.harmBuckets},\n" ++
  s!"    \"cogWins\": {s.cogWins},\n" ++
  s!"    \"triadWins\": {s.triadWins},\n" ++
  s!"    \"harmWins\": {s.harmWins},\n" ++
  s!"    \"cogWinsRel\": {s.cogWinsRel},\n" ++
  s!"    \"triadWinsRel\": {s.triadWinsRel},\n" ++
  s!"    \"harmWinsRel\": {s.harmWinsRel},\n" ++
  s!"    \"harm\": \{\"trivector\": {s.harm0}, \"muse5\": {s.harm5}, \"heptad7\": {s.harm7}, \"hemispheres11\": {s.harm11}, \"recursion13\": {s.harm13}}\n" ++
  s!"  }"

/-- Render a list of corpora as a JSON document (array of objects). -/
def jsonReport (xs : List CorpusStats) : String :=
  "{\n  \"report\": \"dualatlas\",\n  \"corpora\": [\n" ++
  String.intercalate ",\n" (xs.map (·.toJson)) ++
  "\n  ]\n}\n"

/-- Render a list of corpora as a CSV document (header + one row each). -/
def csvReport (xs : List CorpusStats) : String :=
  let line := fun (cs : List String) => String.intercalate "," cs ++ "\n"
  line csvHeader ++ String.join (xs.map (fun s => line s.csvCells))

/-- Render a list of corpora as a Markdown document (summary table + sections). -/
def markdownReport (xs : List CorpusStats) : String := Id.run do
  let mut s := "# Dual-Atlas Census Reports\n\n"
  s := s ++ "Each corpus is swept through the dual atlas (`cog` / `triad` / `harm`).\n\n"
  s := s ++ "| corpus | total | cogWins | triadWins | harmWins | cogWinsRel | triadWinsRel | harmWinsRel |\n"
  s := s ++ "|---|---:|---:|---:|---:|---:|---:|---:|\n"
  for x in xs do
    s := s ++ s!"| {x.name} | {x.total} | {x.cogWins} | {x.triadWins} | {x.harmWins} | {x.cogWinsRel} | {x.triadWinsRel} | {x.harmWinsRel} |\n"
  s := s ++ "\n## Harmonic cell distribution\n\n"
  s := s ++ "| corpus | Trivector | Muse (9^5) | Heptad (6^7) | Hemispheres (2^11) | Recursion (3^13) |\n"
  s := s ++ "|---|---:|---:|---:|---:|---:|\n"
  for x in xs do
    s := s ++ s!"| {x.name} | {x.harm0} | {x.harm5} | {x.harm7} | {x.harm11} | {x.harm13} |\n"
  for x in xs do
    s := s ++ s!"\n## {x.name}\n\n"
    s := s ++ s!"- total declarations: **{x.total}**\n"
    s := s ++ s!"- distinct buckets: cog={x.cogBuckets}, triad={x.triadBuckets}, harm={x.harmBuckets}\n"
    s := s ++ s!"- raw best field wins: cog={x.cogWins}, triad={x.triadWins}, harm={x.harmWins}\n"
    s := s ++ s!"- relative best field wins: cog={x.cogWinsRel}, triad={x.triadWinsRel}, harm={x.harmWinsRel}\n"
  return s

/-- Per-corpus accent colour for the SVG chart. -/
def corpusColor : Nat → String
  | 0 => "#ffd700"  -- itself    → gold
  | 1 => "#8a2be2"  -- mathlib   → violet
  | 2 => "#ff5db1"  -- batteries → pink
  | _ => "#5db1ff"  -- lean4     → blue

/-- Render the four corpora as a grouped bar-chart SVG: for each corpus a bar for
the total declaration count, scaled to the largest corpus. -/
def svgReport (xs : List CorpusStats) : String :=
  let xs := xs.toArray
  let n := xs.size
  let maxTot := (xs.toList.map (·.total)).foldl Nat.max 1
  let w : Nat := 920
  let h : Nat := 120 + n * 70
  let bars : List Svg := (List.range n).map (fun i =>
    let s := xs[i]!
    let y : Int := 110 + Int.ofNat i * 70
    let bw : Int := Int.ofNat s.total * 660 / Int.ofNat maxTot
    let col := corpusColor i
    group
      [ Svg.text [("x", "30"), ("y", toString (y + 26)), ("font-size", "18"),
                  ("font-weight", "700"), ("fill", "#e6ecff")] s.name,
        rect 190 y (max (2 : Int) bw) 40 col "#0b0c18" [("rx", "5")],
        Svg.text [("x", toString (200 + max (2 : Int) bw)), ("y", toString (y + 27)),
                  ("font-size", "15"), ("fill", "#cfd8f5")]
          s!"{s.total} decls" ]
      [])
  let title : Svg :=
    Svg.text [("x", "30"), ("y", "56"), ("font-size", "30"), ("font-weight", "800"),
              ("fill", "#ffd700")] "Aristo · Dual-Atlas Census — four corpora"
  let bg : Svg := rect 0 0 (Int.ofNat w) (Int.ofNat h) "#0b0c18" "none"
  SVG.render (SVG.document w h (bg :: title :: bars))

/-! ## §5  Scan and emit -/

/-- Scan the whole environment and compute `CorpusStats` for each of the four
corpora.  Histograms are built per corpus, then a second pass attributes each
declaration's raw/relative best field within its own corpus. -/
def scanCorpora : CommandElabM (Array CorpusStats) := do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let corpusOf : Name → Option Nat := fun nm =>
    match env.const2ModIdx.get? nm with
    | some i => corpusOfModule moduleNames[i.toNat]!.toString
    | none   => none
  -- per-corpus histograms
  let mut cogHist  : Array (Std.HashMap Nat Nat) := Array.replicate nCorpus {}
  let mut triadHist : Array (Std.HashMap Nat Nat) := Array.replicate nCorpus {}
  let mut harmHist : Array (Std.HashMap Nat Nat) := Array.replicate nCorpus {}
  let mut total : Array Nat := Array.replicate nCorpus 0
  for (name, info) in env.constants.toList do
    match corpusOf name with
    | none => pure ()
    | some k =>
      let hsh := declFingerprint info
      let cg := cogProj hsh
      let tr := triadProj hsh
      let hm := harmCode hsh
      total := total.set! k (total[k]! + 1)
      cogHist := cogHist.set! k ((cogHist[k]!).insert cg ((cogHist[k]!).getD cg 0 + 1))
      triadHist := triadHist.set! k ((triadHist[k]!).insert tr ((triadHist[k]!).getD tr 0 + 1))
      harmHist := harmHist.set! k ((harmHist[k]!).insert hm ((harmHist[k]!).getD hm 0 + 1))
  -- per-corpus win counters
  let mut cogWins   : Array Nat := Array.replicate nCorpus 0
  let mut triadWins : Array Nat := Array.replicate nCorpus 0
  let mut harmWins  : Array Nat := Array.replicate nCorpus 0
  let mut cogWinsR  : Array Nat := Array.replicate nCorpus 0
  let mut triadWinsR : Array Nat := Array.replicate nCorpus 0
  let mut harmWinsR : Array Nat := Array.replicate nCorpus 0
  for (name, info) in env.constants.toList do
    match corpusOf name with
    | none => pure ()
    | some k =>
      let hsh := declFingerprint info
      let a := (cogHist[k]!).getD (cogProj hsh) 0
      let b := (triadHist[k]!).getD (triadProj hsh) 0
      let c := (harmHist[k]!).getD (harmCode hsh) 0
      match bestField a b c with
      | .cog   => cogWins := cogWins.set! k (cogWins[k]! + 1)
      | .triad => triadWins := triadWins.set! k (triadWins[k]! + 1)
      | .harm  => harmWins := harmWins.set! k (harmWins[k]! + 1)
      match bestFieldRel a b c with
      | .cog   => cogWinsR := cogWinsR.set! k (cogWinsR[k]! + 1)
      | .triad => triadWinsR := triadWinsR.set! k (triadWinsR[k]! + 1)
      | .harm  => harmWinsR := harmWinsR.set! k (harmWinsR[k]! + 1)
  -- assemble
  let mut out : Array CorpusStats := #[]
  for k in [0:nCorpus] do
    out := out.push {
      name := corpusLabels[k]!,
      total := total[k]!,
      cogBuckets := (cogHist[k]!).size,
      triadBuckets := (triadHist[k]!).size,
      harmBuckets := (harmHist[k]!).size,
      cogWins := cogWins[k]!, triadWins := triadWins[k]!, harmWins := harmWins[k]!,
      cogWinsRel := cogWinsR[k]!, triadWinsRel := triadWinsR[k]!, harmWinsRel := harmWinsR[k]!,
      harm0 := (harmHist[k]!).getD 0 0,
      harm5 := (harmHist[k]!).getD 5 0,
      harm7 := (harmHist[k]!).getD 7 0,
      harm11 := (harmHist[k]!).getD 11 0,
      harm13 := (harmHist[k]!).getD 13 0 }
  return out

/-- `#dualreports` scans all four corpora and writes every report format:

* per-corpus files `reports/dualatlas_<corpus>.{json,csv,md,svg}` (16 files);
* combined files `reports/dualatlas_all.{json,csv,md,svg}` (4 files).
-/
syntax (name := dualreportsCmd) "#dualreports" : command

@[command_elab dualreportsCmd]
def elabDualreports : CommandElab := fun _ => do
  let stats ← scanCorpora
  let statsList := stats.toList
  -- console summary
  let mut summary := "[Aristo Dual Reports] dual-atlas census across four corpora\n"
  for s in statsList do
    summary := summary ++
      s!"  ├── {s.name}: {s.total} decls — raw(cog/triad/harm)={s.cogWins}/{s.triadWins}/{s.harmWins}, rel={s.cogWinsRel}/{s.triadWinsRel}/{s.harmWinsRel}\n"
  summary := summary ++ "  └── wrote reports/dualatlas_*.{json,csv,md,svg}"
  logInfo summary
  -- write files (best-effort)
  try
    IO.FS.createDirAll "reports"
    -- combined reports
    IO.FS.writeFile "reports/dualatlas_all.json" (jsonReport statsList)
    IO.FS.writeFile "reports/dualatlas_all.csv" (csvReport statsList)
    IO.FS.writeFile "reports/dualatlas_all.md" (markdownReport statsList)
    IO.FS.writeFile "reports/dualatlas_all.svg" (svgReport statsList)
    -- per-corpus reports
    for s in statsList do
      IO.FS.writeFile s!"reports/dualatlas_{s.name}.json" (jsonReport [s])
      IO.FS.writeFile s!"reports/dualatlas_{s.name}.csv" (csvReport [s])
      IO.FS.writeFile s!"reports/dualatlas_{s.name}.md" (markdownReport [s])
      IO.FS.writeFile s!"reports/dualatlas_{s.name}.svg" (svgReport [s])
  catch e =>
    logWarning m!"report writing failed: {e.toMessageData}"

/-! ## §6  Run it -/

#dualreports

end DualAtlas

import Mathlib
import RequestProject.DualAtlas
import RequestProject.DualAtlasReports
import Lean

/-!
# VisionAtlas — emit fine-grained projection rasters for the OpenCV vision pass

The earlier `DualAtlasReports` module reduced each corpus to a handful of summary
counters.  This module instead emits the **full projection rasters** that the
OpenCV vision pass consumes:

* per corpus, the complete `cog` histogram (92 buckets, indices `1 … 92`);
* per corpus, the complete `triad` histogram (20 buckets, indices `0 … 19`);
* per corpus, the `harm` histogram (5 codes `0,5,7,11,13`);
* per corpus, the joint `cog × triad` occupancy matrix (`92 × 20`).

These are the "many views" the user asked to extract from **all repos** (the four
corpora `itself / mathlib / batteries / lean4`) using the projections we already
built (`cogProj`, `triadProj`, `harmCode`).  Each is written as a CSV under
`vision/atlas/` so the Python/OpenCV stage can render it to an image and look for
structure.

## Honest scope

The verified content remains the projection-range algebra in `DualAtlas`
(`cogProj_mem`, `triadProj_le`) and the small structural facts below.  The raster
CSVs are an *empirical readout* of the current environment; the patterns OpenCV
detects in them are separately certified, as literals, in `VisionPatterns`.
-/

open Lean Elab Command

namespace DualAtlas

/-- Number of `cog` buckets used by the raster (`1 … 92`). -/
def visCogBuckets : Nat := 92
/-- Number of `triad` buckets used by the raster (`0 … 19`). -/
def visTriadBuckets : Nat := 20

/-- The five harmonic codes, in fixed raster order. -/
def harmCodesOrder : List Nat := [0, 5, 7, 11, 13]

/-- The raster header order has five harmonic codes. -/
theorem harmCodesOrder_length : harmCodesOrder.length = 5 := by decide

/-- `#visionatlas` sweeps the four corpora and writes the full projection rasters
(`cog` / `triad` / `harm` histograms and the joint `cog × triad` matrix) to
`vision/atlas/`. -/
syntax (name := visionatlasCmd) "#visionatlas" : command

@[command_elab visionatlasCmd]
def elabVisionatlas : CommandElab := fun _ => do
  let env ← getEnv
  let moduleNames := env.header.moduleNames
  let corpusOf : Name → Option Nat := fun nm =>
    match env.const2ModIdx.get? nm with
    | some i => corpusOfModule moduleNames[i.toNat]!.toString
    | none   => none
  -- per-corpus rasters: cog (92), triad (20), joint (92*20 flattened row-major: cog index * 20 + triad)
  let nC := nCorpus
  let mut cogRas   : Array (Array Nat) := Array.replicate nC (Array.replicate visCogBuckets 0)
  let mut triadRas : Array (Array Nat) := Array.replicate nC (Array.replicate visTriadBuckets 0)
  let mut harmRas  : Array (Array Nat) := Array.replicate nC (Array.replicate 5 0)
  let mut jointRas : Array (Array Nat) := Array.replicate nC (Array.replicate (visCogBuckets * visTriadBuckets) 0)
  let mut total    : Array Nat := Array.replicate nC 0
  for (name, info) in env.constants.toList do
    match corpusOf name with
    | none => pure ()
    | some k =>
      let hsh := declFingerprint info
      let cg := cogProj hsh        -- 1 … 92
      let tr := triadProj hsh      -- 0 … 19
      let hm := harmCode hsh       -- in {0,5,7,11,13}
      let ci := cg - 1             -- 0 … 91
      total := total.set! k (total[k]! + 1)
      let cr := cogRas[k]!
      cogRas := cogRas.set! k (cr.set! ci (cr[ci]! + 1))
      let trr := triadRas[k]!
      triadRas := triadRas.set! k (trr.set! tr (trr[tr]! + 1))
      let hi := match hm with | 0 => 0 | 5 => 1 | 7 => 2 | 11 => 3 | _ => 4
      let hr := harmRas[k]!
      harmRas := harmRas.set! k (hr.set! hi (hr[hi]! + 1))
      let jr := jointRas[k]!
      let ji := ci * visTriadBuckets + tr
      jointRas := jointRas.set! k (jr.set! ji (jr[ji]! + 1))
  -- emit
  try
    IO.FS.createDirAll "vision/atlas"
    let csvRow := fun (a : Array Nat) => String.intercalate "," (a.toList.map toString) ++ "\n"
    let mut summary := "{\n  \"report\": \"visionatlas\",\n  \"corpora\": [\n"
    let mut first := true
    for k in [0:nC] do
      let nm := corpusLabels[k]!
      IO.FS.writeFile s!"vision/atlas/{nm}_cog.csv" (csvRow cogRas[k]!)
      IO.FS.writeFile s!"vision/atlas/{nm}_triad.csv" (csvRow triadRas[k]!)
      IO.FS.writeFile s!"vision/atlas/{nm}_harm.csv" (csvRow harmRas[k]!)
      -- joint as 92 rows x 20 cols
      let mut jtxt := ""
      for ci in [0:visCogBuckets] do
        let row := (List.range visTriadBuckets).map (fun tr => toString (jointRas[k]!)[ci * visTriadBuckets + tr]!)
        jtxt := jtxt ++ String.intercalate "," row ++ "\n"
      IO.FS.writeFile s!"vision/atlas/{nm}_joint.csv" jtxt
      let sep := if first then "" else ",\n"
      summary := summary ++ sep ++
        s!"    \{\"corpus\": \"{nm}\", \"total\": {total[k]!}, " ++
        s!"\"cog\": [{String.intercalate ", " (cogRas[k]!.toList.map toString)}], " ++
        s!"\"triad\": [{String.intercalate ", " (triadRas[k]!.toList.map toString)}], " ++
        s!"\"harm\": [{String.intercalate ", " (harmRas[k]!.toList.map toString)}]}"
      first := false
    summary := summary ++ "\n  ]\n}\n"
    IO.FS.writeFile "vision/atlas/summary.json" summary
    logInfo s!"[Aristo VisionAtlas] wrote vision/atlas/ rasters for {nC} corpora"
  catch e =>
    logWarning m!"vision raster writing failed: {e.toMessageData}"

#visionatlas

end DualAtlas

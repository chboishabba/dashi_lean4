import RequestProject.DualAtlas
import Lean

/-!
# DualAtlasCensus — sweeping **all ~700k declarations** through the dual atlas and
deciding *which dual field is the better coordinate* for each declaration.

The dual atlas (`RequestProject.DualAtlas`) gives every declaration a
`DualCoordinate` with three fields:

* `cog`   — the `46×2` cognitive grid index (`cogProj`, `1 ≤ cog ≤ 92`, **92** buckets);
* `triad` — the `20×3` semantic triad index (`triadProj`, `triad ≤ 19`, **20** buckets);
* `harm`  — the harmonic cell code (`harmCode`, value in `{0,5,7,11,13}`, **5** buckets).

A field is **better** for a declaration when its value-bucket is the *most
discriminating* one for that declaration — i.e. the bucket that holds the fewest
declarations of the whole environment.  Intuitively, if a declaration shares its
`cog` value with very few others, then `cog` pins it down better than `triad` or
`harm` do.  Ties are broken `cog > triad > harm` (finer grid first).

This module contributes:

* `DualField` — a name for each of the three coordinate fields, with `popOf`
  selecting that field's bucket population.
* `bestField` — the most-discriminating field given the three bucket populations.
* `bestField_is_min`, `bestField_le_cog/triad/harm` — **verified** facts that the
  chosen field always realises the minimum population (so the choice is honest).
* `#dualcensus` — reflect the **entire loaded environment** (Lean 4 core +
  mathlib + this project), build the three field histograms, and report how many
  declarations each field is best for, plus the result for a few featured decls.
  A JSON artifact `atlas_dualcensus.json` is written for inspection.
* `#whichfield f` — for a single declaration, recompute the histograms over the
  whole environment and report which field is best for `f`.

## Honest scope

The "population" of a bucket is the empirical count of declarations whose
fingerprint (`Expr.hash` of type XOR value, O(1) per declaration) lands in that
bucket.  Nothing here claims a mathematical relationship between the Monster
group and the declarations; the verified content is precisely the
`bestField`/`popOf` argmin algebra.  The census numbers are an empirical readout
of the current environment.
-/

open Lean Meta Elab Command

namespace DualAtlas

/-! ## §1  Naming the three fields and their populations -/

/-- The three coordinate fields of a `DualCoordinate`. -/
inductive DualField
  | cog | triad | harm
deriving DecidableEq, Repr

/-- Human-readable name of a field. -/
def DualField.label : DualField → String
  | .cog   => "Cognitive (46×2)"
  | .triad => "Semantic Triad (20×3)"
  | .harm  => "Harmonic Cell"

/-- The bucket population attached to a field, given the three candidate
populations `a` (cog), `b` (triad), `c` (harm). -/
def popOf : DualField → Nat → Nat → Nat → Nat
  | .cog,   a, _, _ => a
  | .triad, _, b, _ => b
  | .harm,  _, _, c => c

/-- The **better** field is the one whose value-bucket holds the fewest
declarations; ties are broken `cog > triad > harm`. -/
def bestField (a b c : Nat) : DualField :=
  if a ≤ b then (if a ≤ c then .cog else .harm)
  else (if b ≤ c then .triad else .harm)

/-! ## §2  Correctness of the selection -/

/-- **The chosen field realises the minimum population** — the census selection is
honest: it never reports a field that is not actually the smallest bucket. -/
theorem bestField_is_min (a b c : Nat) :
    popOf (bestField a b c) a b c = min a (min b c) := by
  unfold bestField
  split_ifs <;> simp only [popOf] <;> omega

/-- The best field's population is no larger than `cog`'s. -/
theorem bestField_le_cog (a b c : Nat) : popOf (bestField a b c) a b c ≤ a := by
  rw [bestField_is_min]; omega

/-- The best field's population is no larger than `triad`'s. -/
theorem bestField_le_triad (a b c : Nat) : popOf (bestField a b c) a b c ≤ b := by
  rw [bestField_is_min]; omega

/-- The best field's population is no larger than `harm`'s. -/
theorem bestField_le_harm (a b c : Nat) : popOf (bestField a b c) a b c ≤ c := by
  rw [bestField_is_min]; omega

/-! ## §2b  Capacity-normalised (relative) discrimination

The raw `bestField` always favours `cog`, because the `46×2` grid is simply the
finest partition (92 buckets), so its buckets are smallest on average.  To ask
*which field places a declaration in an unusually rare bucket for that field*, we
normalise each population by the field's capacity (number of buckets): a bucket
of population `p` in a field with `n` buckets is rarer-than-average exactly when
`p · n` is small (since the average bucket holds `total / n`).  `bestFieldRel`
picks the field minimising `p · n`, which genuinely varies across declarations. -/

/-- Number of buckets of each field: `cog` has `92`, `triad` has `20`, `harm` has `5`. -/
def cogBucketCount : Nat := 92
/-- Number of `triad` buckets (`20×3` recursion exposes the 20-index). -/
def triadBucketCount : Nat := 20
/-- Number of `harm` buckets (`{0,5,7,11,13}`). -/
def harmBucketCount : Nat := 5

/-- The capacity-normalised best field: minimise `population · bucketCount`. -/
def bestFieldRel (a b c : Nat) : DualField :=
  bestField (a * cogBucketCount) (b * triadBucketCount) (c * harmBucketCount)

/-- **The relative selection also realises a genuine minimum** — it is the argmin
of the capacity-weighted populations. -/
theorem bestFieldRel_is_min (a b c : Nat) :
    popOf (bestFieldRel a b c) (a * cogBucketCount) (b * triadBucketCount)
        (c * harmBucketCount)
      = min (a * cogBucketCount) (min (b * triadBucketCount) (c * harmBucketCount)) := by
  unfold bestFieldRel
  exact bestField_is_min _ _ _

/-! ## §3  Fingerprint and reflection front-end -/

/-- The fingerprint of a declaration from its cached `Expr.hash` (O(1)): the XOR
of the type's hash and the value's hash (`0` when there is no value). -/
def declFingerprint (info : ConstantInfo) : Nat :=
  let vh := match info.value? with | some v => v.hash.toNat | none => 0
  info.type.hash.toNat ^^^ vh

/-- `#dualcensus` sweeps the **entire loaded environment**, builds the three field
histograms over all declarations, and reports how many declarations each field is
the better (most discriminating) coordinate for, plus the verdict for a few
featured declarations.  Writes `atlas_dualcensus.json`. -/
syntax (name := dualcensusCmd) "#dualcensus" : command

@[command_elab dualcensusCmd]
def elabDualcensus : CommandElab := fun _ => do
  let env ← getEnv
  -- pass 1: build the three field histograms
  let mut cogHist : Std.HashMap Nat Nat := {}
  let mut triadHist : Std.HashMap Nat Nat := {}
  let mut harmHist : Std.HashMap Nat Nat := {}
  let mut total := 0
  for (_, info) in env.constants.toList do
    total := total + 1
    let h := declFingerprint info
    let cg := cogProj h
    let tr := triadProj h
    let hm := harmCode h
    cogHist := cogHist.insert cg (cogHist.getD cg 0 + 1)
    triadHist := triadHist.insert tr (triadHist.getD tr 0 + 1)
    harmHist := harmHist.insert hm (harmHist.getD hm 0 + 1)
  -- pass 2: count, for every declaration, which field is best (raw + relative)
  let mut cogWins := 0
  let mut triadWins := 0
  let mut harmWins := 0
  let mut cogWinsRel := 0
  let mut triadWinsRel := 0
  let mut harmWinsRel := 0
  for (_, info) in env.constants.toList do
    let h := declFingerprint info
    let a := cogHist.getD (cogProj h) 0
    let b := triadHist.getD (triadProj h) 0
    let c := harmHist.getD (harmCode h) 0
    match bestField a b c with
    | .cog   => cogWins := cogWins + 1
    | .triad => triadWins := triadWins + 1
    | .harm  => harmWins := harmWins + 1
    match bestFieldRel a b c with
    | .cog   => cogWinsRel := cogWinsRel + 1
    | .triad => triadWinsRel := triadWinsRel + 1
    | .harm  => harmWinsRel := harmWinsRel + 1
  -- featured declarations
  let featured := [`Nat.add, `List.map, `Prod.fst]
  let mut featuredLines : String := ""
  let mut featuredJson : String := ""
  let mut first := true
  for nm in featured do
    match env.find? nm with
    | some info =>
      let h := declFingerprint info
      let a := cogHist.getD (cogProj h) 0
      let b := triadHist.getD (triadProj h) 0
      let c := harmHist.getD (harmCode h) 0
      let bf := bestField a b c
      let bfr := bestFieldRel a b c
      featuredLines := featuredLines ++
        s!"  ├── {nm}: raw best = {bf.label}, relative best = {bfr.label} (cogPop={a}, triadPop={b}, harmPop={c})\n"
      let sep := if first then "" else ",\n"
      featuredJson := featuredJson ++ sep ++
        s!"    \{\"decl\": \"{nm}\", \"rawBest\": \"{bf.label}\", \"relBest\": \"{bfr.label}\", \"cogPop\": {a}, \"triadPop\": {b}, \"harmPop\": {c}}"
      first := false
    | none => pure ()
  let report :=
    s!"[Aristo Dual Census] swept the full environment through the dual atlas\n" ++
    s!"  ├── total declarations               = {total}\n" ++
    s!"  ├── distinct cog buckets (≤ 92)      = {cogHist.size}\n" ++
    s!"  ├── distinct triad buckets (≤ 20)    = {triadHist.size}\n" ++
    s!"  ├── distinct harm buckets (≤ 5)      = {harmHist.size}\n" ++
    s!"  ├── [raw] decls best served by Cognitive = {cogWins}\n" ++
    s!"  ├── [raw] decls best served by Triad     = {triadWins}\n" ++
    s!"  ├── [raw] decls best served by Harmonic  = {harmWins}\n" ++
    s!"  ├── [rel] decls best served by Cognitive = {cogWinsRel}\n" ++
    s!"  ├── [rel] decls best served by Triad     = {triadWinsRel}\n" ++
    s!"  ├── [rel] decls best served by Harmonic  = {harmWinsRel}\n" ++
    s!"  └── featured declarations:\n" ++ featuredLines
  logInfo report
  -- best-effort JSON artifact
  try
    let json :=
      s!"\{\n" ++
      s!"  \"totalDeclarations\": {total},\n" ++
      s!"  \"cogBuckets\": {cogHist.size},\n" ++
      s!"  \"triadBuckets\": {triadHist.size},\n" ++
      s!"  \"harmBuckets\": {harmHist.size},\n" ++
      s!"  \"cogWins\": {cogWins},\n" ++
      s!"  \"triadWins\": {triadWins},\n" ++
      s!"  \"harmWins\": {harmWins},\n" ++
      s!"  \"cogWinsRel\": {cogWinsRel},\n" ++
      s!"  \"triadWinsRel\": {triadWinsRel},\n" ++
      s!"  \"harmWinsRel\": {harmWinsRel},\n" ++
      s!"  \"featured\": [\n" ++ featuredJson ++ "\n  ]\n" ++
      s!"}\n"
    IO.FS.writeFile "atlas_dualcensus.json" json
  catch _ => pure ()

/-- `#whichfield f` reports which dual field is best for a single declaration `f`,
computing the field histograms over the whole environment. -/
syntax (name := whichfieldCmd) "#whichfield " ident : command

@[command_elab whichfieldCmd]
def elabWhichfield : CommandElab := fun stx => do
  match stx with
  | `(#whichfield $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info =>
      let mut cogHist : Std.HashMap Nat Nat := {}
      let mut triadHist : Std.HashMap Nat Nat := {}
      let mut harmHist : Std.HashMap Nat Nat := {}
      for (_, i) in env.constants.toList do
        let h := declFingerprint i
        cogHist := cogHist.insert (cogProj h) (cogHist.getD (cogProj h) 0 + 1)
        triadHist := triadHist.insert (triadProj h) (triadHist.getD (triadProj h) 0 + 1)
        harmHist := harmHist.insert (harmCode h) (harmHist.getD (harmCode h) 0 + 1)
      let h := declFingerprint info
      let a := cogHist.getD (cogProj h) 0
      let b := triadHist.getD (triadProj h) 0
      let c := harmHist.getD (harmCode h) 0
      let bf := bestField a b c
      let bfr := bestFieldRel a b c
      logInfo s!"[Aristo Which Field] {name}\n  ├── cog={cogProj h} (pop {a})\n  ├── triad={triadProj h} (pop {b})\n  ├── harm={harmCode h} (pop {c})\n  ├── raw best field      = {bf.label}\n  └── relative best field = {bfr.label}"
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #whichfield command"

/-! ## §4  Test suite -/

#dualcensus

#whichfield Nat.add
#whichfield List.map
#whichfield Prod.fst

end DualAtlas

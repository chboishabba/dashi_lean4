import RequestProject.ResolutionLadder

/-!
# DuplicateGlossary — a glossary of the persistent smushes, syntax × proof-semantics

`ResolutionLadder` / `QExpansionLadder` end with a striking endpoint: the
**persistent (semantic) smushes** — the irrep-1 collisions that survive the full
fifteen-prime resolution `fullModulus` and *every* one of the 100 McKay–Thompson
q-expansions — are exactly the declaration groups whose statement fingerprints are
**literally identical** (`QExpansionLadder.unbreakable_iff_equal_hash`).  They are
not address artefacts; they are genuine *duplicates* of statement shape inside the
Mathlib corpus.

This module reframes those persistent smushes from noise into signal by building a
**glossary of duplicates**.  Each glossary group is the set of declarations sharing
one statement fingerprint `info.type.hash`, and every entry pairs two faces:

* the **syntax face** — how the declarations differ in *name / namespace / spelling*
  even though their statement fingerprints coincide, together with the
  pretty-printed statement(s) and whether those strings are byte-identical or only
  hash-identical (a real *syntax delta*);
* the **proof-semantics face** — *how* the duplicates got there, classified by
  inspecting the stored proof terms:
    - `alias`        — all members carry the **literally identical** proof term
      (one is a copy/alias of another);
    - `rfl-variant`  — at least one member's proof is a reflexivity/triviality
      term (`Eq.refl`, `rfl`, `Iff.refl`, `of_eq_true`, `trivial`, …);
    - `independent`  — all members have proof terms but they are **distinct**
      (genuinely independent derivations of the same statement shape);
    - `deprecated`   — at least one member is tagged `@[deprecated]`;
    - `unknown`      — at least one member exposes no proof value (axiom / opaque /
      structural), so the derivation is not available at fingerprint time.
  (Priority, when several apply: `deprecated` > `alias` > `rfl-variant` >
  `independent` > `unknown`.)

## Honest scope

As everywhere in this atlas, a "duplicate" is a collision of the *structural
statement hash* `info.type.hash`.  Two members of a group always share that
fingerprint; we additionally record whether their **types are structurally equal**
(`Expr` BEq) so that a rare hash-collision of genuinely different statements is
visible rather than silently asserted to be a duplicate.  None of this claims the
declarations are mathematically interchangeable beyond what the proof-semantics tag
literally inspects.

Grouping by the exact fingerprint is *finer* than `ResolutionLadder`'s base-cell
tally of "persistent smushes": a single irrep-1 cell `h % 196883` can host several
distinct-hash duplicate groups at once, in which case the ladder marks that cell
*geometric* and never counts the duplicates living inside it.  So on the same
120,000-declaration sample where the ladder reports about 1,969 persistent cells,
the strict-fingerprint glossary finds more groups (3,436) — it recovers exactly the
duplicates the coarse cell view discards.

## Output

* `atlas_duplicates.json` — one machine-readable object per duplicate group.
* `DuplicateGlossary.md`  — the human-readable glossary, one section per group.

## Commands

* `#dupglossary`          — full environment scan; build the glossary; write both files.
* `#dupglossary_sample n` — the same over the first `n` declarations (fast demo).
-/

open Lean Meta Elab Command

namespace DuplicateGlossary

open ResolutionLadder

/-! ## §1  Proof-term "triviality" heads

A member counts as a `rfl`-variant when its proof term's head is one of the
canonical reflexivity / triviality constants. -/

/-- Head constants whose application is a reflexivity / triviality proof. -/
def trivialHeads : List Name :=
  [``Eq.refl, ``rfl, ``Iff.refl, ``Iff.rfl, ``HEq.refl, ``of_eq_true,
   ``trivial, ``True.intro, ``id]

/-! ## §2  Per-member and per-group data -/

/-- One member of a duplicate group: its name split into a namespace face, plus the
proof-semantics flags and pretty-printed statement. -/
structure GlossaryMember where
  name          : Name
  namespacePart : String   -- the dotted prefix, or "" for a root-level name
  baseName      : String   -- the final component
  hasValue      : Bool     -- a proof term is available
  isRfl         : Bool     -- the proof term is a reflexivity/triviality term
  deprecated    : Bool     -- tagged `@[deprecated]`
  ppType        : String   -- pretty-printed statement
  deriving Inhabited

/-- One glossary entry: a group of declarations sharing a statement fingerprint. -/
structure GlossaryEntry where
  groupId           : Nat
  fingerprint       : Nat
  members           : Array GlossaryMember
  structurallyEqual : Bool   -- all member types are `Expr`-equal (not just hash-equal)
  syntaxIdentical   : Bool   -- all pretty-printed statements are byte-identical
  proofTag          : String -- alias / rfl-variant / independent / deprecated / unknown
  deriving Inhabited

/-! ## §3  Grouping the corpus by statement fingerprint -/

/-- Group `(name, info)` pairs by statement fingerprint `info.type.hash`, keep the
groups holding `≥ 2` declarations, and return them sorted by fingerprint so that
group ids are stable across runs. -/
def groupByFingerprint (pairs : List (Name × ConstantInfo)) : Array (Nat × Array Name) :=
  Id.run do
    let mut m : Std.HashMap Nat (Array Name) := {}
    for (n, info) in pairs do
      let fp := info.type.hash.toNat
      m := m.insert fp ((m[fp]?.getD #[]).push n)
    let groups := m.toList.filter (fun kv => kv.2.size ≥ 2)
    let sorted := groups.toArray.qsort (fun a b => a.1 < b.1)
    return sorted

/-! ## §4  Classifying a single group (needs `MetaM` for pretty-printing) -/

/-- Pretty-print an expression, falling back to its raw `toString` if the
pretty-printer throws. -/
def ppType (e : Expr) : MetaM String := do
  try return (← PrettyPrinter.ppExpr e).pretty
  catch _ => return toString e

/-- The namespace / base split of a name. -/
def splitName (n : Name) : String × String :=
  let comps := n.components
  match comps.reverse with
  | [] => ("", toString n)
  | last :: restRev =>
      let nsParts := restRev.reverse
      let ns := String.intercalate "." (nsParts.map toString)
      (ns, toString last)

/-- Build the glossary entry for one fingerprint group. -/
def classifyGroup (env : Environment) (gid fp : Nat) (names : Array Name) :
    MetaM GlossaryEntry := do
  let mut members : Array GlossaryMember := #[]
  let mut types   : Array Expr := #[]
  let mut values  : Array (Option Expr) := #[]
  for n in names do
    let some ci := env.find? n | continue
    let pp ← ppType ci.type
    let dep := (Lean.Linter.deprecatedAttr.getParam? env n).isSome
    let isRfl :=
      match ci.value? with
      | some v => match v.getAppFn.constName? with
                  | some c => trivialHeads.contains c
                  | none   => false
      | none => false
    let (ns, base) := splitName n
    members := members.push {
      name := n, namespacePart := ns, baseName := base,
      hasValue := ci.value?.isSome, isRfl := isRfl,
      deprecated := dep, ppType := pp }
    types  := types.push ci.type
    values := values.push ci.value?
  -- aggregate the two faces
  let structurallyEqual :=
    match types[0]? with
    | none => true
    | some t0 => types.all (fun t => t == t0)
  let syntaxIdentical :=
    match members[0]? with
    | none => true
    | some m0 => members.all (fun m => m.ppType == m0.ppType)
  let anyDep   := members.any (·.deprecated)
  let anyRfl   := members.any (·.isRfl)
  let allValue := values.all (·.isSome)
  let allValEq :=
    allValue &&
    (match values[0]? with
     | some (some v0) => values.all (fun ov => match ov with
                                               | some v => v == v0
                                               | none   => false)
     | _ => true)
  let proofTag :=
    if anyDep then "deprecated"
    else if allValEq then "alias"
    else if anyRfl then "rfl-variant"
    else if allValue then "independent"
    else "unknown"
  return {
    groupId := gid, fingerprint := fp, members := members,
    structurallyEqual := structurallyEqual,
    syntaxIdentical := syntaxIdentical, proofTag := proofTag }

/-- Build all glossary entries for a corpus. -/
def buildGlossary (env : Environment) (pairs : List (Name × ConstantInfo)) :
    MetaM (Array GlossaryEntry) := do
  let groups := groupByFingerprint pairs
  let mut entries : Array GlossaryEntry := #[]
  for h : i in [0:groups.size] do
    let (fp, names) := groups[i]
    entries := entries.push (← classifyGroup env i fp names)
  return entries

/-! ## §5  Aggregate statistics over the glossary -/

/-- Tally proof-semantics tags and syntax/structure faces across all entries. -/
structure GlossaryStats where
  totalDecls   : Nat
  groups       : Nat
  aliasCnt     : Nat
  rflCnt       : Nat
  independent  : Nat
  deprecatedC  : Nat
  unknownCnt   : Nat
  syntaxIdent  : Nat   -- groups whose statements are byte-identical
  syntaxDelta  : Nat   -- groups with a genuine pretty-print delta
  hashOnly     : Nat   -- groups that are only hash-equal, not structurally equal
  deriving Inhabited

/-- Compute the aggregate statistics. -/
def tally (totalDecls : Nat) (es : Array GlossaryEntry) : GlossaryStats := Id.run do
  let mut s : GlossaryStats :=
    { totalDecls := totalDecls, groups := es.size, aliasCnt := 0, rflCnt := 0,
      independent := 0, deprecatedC := 0, unknownCnt := 0, syntaxIdent := 0,
      syntaxDelta := 0, hashOnly := 0 }
  for e in es do
    match e.proofTag with
    | "alias"       => s := { s with aliasCnt := s.aliasCnt + 1 }
    | "rfl-variant" => s := { s with rflCnt := s.rflCnt + 1 }
    | "independent" => s := { s with independent := s.independent + 1 }
    | "deprecated"  => s := { s with deprecatedC := s.deprecatedC + 1 }
    | _             => s := { s with unknownCnt := s.unknownCnt + 1 }
    if e.syntaxIdentical then s := { s with syntaxIdent := s.syntaxIdent + 1 }
    else s := { s with syntaxDelta := s.syntaxDelta + 1 }
    if !e.structurallyEqual then s := { s with hashOnly := s.hashOnly + 1 }
  return s

/-! ## §6  Rendering: JSON and Markdown -/

/-- A single glossary entry as a `Lean.Json` object. -/
def entryJson (e : GlossaryEntry) : Json :=
  let memberJson (m : GlossaryMember) : Json :=
    Json.mkObj [
      ("name", Json.str (toString m.name)),
      ("namespace", Json.str m.namespacePart),
      ("baseName", Json.str m.baseName),
      ("hasValue", Json.bool m.hasValue),
      ("isRfl", Json.bool m.isRfl),
      ("deprecated", Json.bool m.deprecated),
      ("statement", Json.str m.ppType) ]
  Json.mkObj [
    ("groupId", Json.num e.groupId),
    ("fingerprint", Json.num e.fingerprint),
    ("size", Json.num e.members.size),
    ("proofTag", Json.str e.proofTag),
    ("syntaxIdentical", Json.bool e.syntaxIdentical),
    ("structurallyEqual", Json.bool e.structurallyEqual),
    ("members", Json.arr (e.members.map memberJson)) ]

/-- The whole glossary as a JSON document. -/
def glossaryJson (st : GlossaryStats) (es : Array GlossaryEntry) : String :=
  let doc := Json.mkObj [
    ("totalDecls", Json.num st.totalDecls),
    ("groups", Json.num st.groups),
    ("byProofSemantics", Json.mkObj [
      ("alias", Json.num st.aliasCnt),
      ("rflVariant", Json.num st.rflCnt),
      ("independent", Json.num st.independent),
      ("deprecated", Json.num st.deprecatedC),
      ("unknown", Json.num st.unknownCnt) ]),
    ("bySyntax", Json.mkObj [
      ("identical", Json.num st.syntaxIdent),
      ("delta", Json.num st.syntaxDelta),
      ("hashOnly", Json.num st.hashOnly) ]),
    ("fullModulus", Json.num fullModulus),
    ("entries", Json.arr (es.map entryJson)) ]
  doc.pretty ++ "\n"

/-- One Markdown section for a glossary entry. -/
def entryMd (e : GlossaryEntry) : String :=
  let header := s!"## Group {e.groupId} — fingerprint `{e.fingerprint}` ({e.members.size} members)\n"
  let syntaxFace := if e.syntaxIdentical then "identical statements" else "syntax delta (pretty-prints differ)"
  let structFace := if e.structurallyEqual then "equal" else "hash-only collision"
  let faces :=
    s!"- **Proof semantics:** `{e.proofTag}`\n" ++
    s!"- **Syntax:** {syntaxFace}\n" ++
    s!"- **Structural type equality:** {structFace}\n"
  let stmt :=
    if e.syntaxIdentical then
      match e.members[0]? with
      | some m => s!"- **Statement:** `{m.ppType}`\n"
      | none   => ""
    else "- **Statements (per member, below)**\n"
  let memberLines := String.intercalate "\n" (e.members.toList.map (fun m =>
    let ns := if m.namespacePart == "" then "_root_" else m.namespacePart
    let tags :=
      (if m.deprecated then " ⟨deprecated⟩" else "") ++
      (if m.isRfl then " ⟨rfl⟩" else "") ++
      (if !m.hasValue then " ⟨no-value⟩" else "")
    let stmtSuffix := if e.syntaxIdentical then "" else s!" — `{m.ppType}`"
    s!"  - `{m.name}` (namespace `{ns}`, base `{m.baseName}`){tags}{stmtSuffix}"))
  header ++ faces ++ stmt ++ "- **Members:**\n" ++ memberLines ++ "\n"

/-- The full Markdown glossary. -/
def glossaryMd (st : GlossaryStats) (es : Array GlossaryEntry) : String :=
  let head :=
    "# Duplicate Glossary\n\n" ++
    "Persistent smushes of the Monster atlas, reframed as a glossary of genuine " ++
    "statement-fingerprint duplicates.  Each group pairs its **syntax face** " ++
    "(name/namespace divergence and pretty-print delta) with its **proof-semantics " ++
    "face** (how the duplicate arose).\n\n" ++
    s!"- Declarations scanned: **{st.totalDecls}**\n" ++
    s!"- Duplicate groups (≥ 2 members, shared fingerprint): **{st.groups}**\n\n" ++
    "**By proof semantics:** " ++
    s!"alias **{st.aliasCnt}**, rfl-variant **{st.rflCnt}**, independent **{st.independent}**, " ++
    s!"deprecated **{st.deprecatedC}**, unknown **{st.unknownCnt}**.\n\n" ++
    "**By syntax:** " ++
    s!"identical **{st.syntaxIdent}**, syntax-delta **{st.syntaxDelta}** " ++
    s!"(of which hash-only collisions **{st.hashOnly}**).\n\n---\n\n"
  head ++ String.intercalate "\n" (es.toList.map entryMd)

/-- The console summary. -/
def glossaryReport (st : GlossaryStats) : String :=
  s!"[Aristo Duplicate Glossary] persistent smushes as a glossary of duplicates\n" ++
  s!"  ├── declarations scanned   : {st.totalDecls}\n" ++
  s!"  ├── duplicate groups (≥2)  : {st.groups}\n" ++
  s!"  ├── proof semantics        : alias {st.aliasCnt}, rfl-variant {st.rflCnt}, " ++
       s!"independent {st.independent}, deprecated {st.deprecatedC}, unknown {st.unknownCnt}\n" ++
  s!"  └── syntax                 : identical {st.syntaxIdent}, delta {st.syntaxDelta} " ++
       s!"(hash-only {st.hashOnly})"

/-! ## §7  Driver -/

/-- Build the glossary over `pairs`, log the report, and write both atlas files. -/
def runGlossary (pairs : List (Name × ConstantInfo)) : CommandElabM Unit := do
  let env ← getEnv
  let es ← liftTermElabM <| Meta.MetaM.run' (buildGlossary env pairs)
  let st := tally pairs.length es
  logInfo (glossaryReport st)
  IO.FS.writeFile "atlas_duplicates.json" (glossaryJson st es)
  IO.FS.writeFile "DuplicateGlossary.md" (glossaryMd st es)

/-! ## §8  Commands -/

/-- `#dupglossary` scans the whole environment, builds the duplicate glossary, logs
the report, and writes `atlas_duplicates.json` + `DuplicateGlossary.md`. -/
syntax (name := dupglossaryCmd) "#dupglossary" : command

@[command_elab dupglossaryCmd]
def elabDupglossary : CommandElab := fun _ => do
  let env ← getEnv
  runGlossary env.constants.toList

/-- `#dupglossary_sample n` runs the same over the first `n` declarations. -/
syntax (name := dupglossarySampleCmd) "#dupglossary_sample " num : command

@[command_elab dupglossarySampleCmd]
def elabDupglossarySample : CommandElab := fun stx => do
  match stx with
  | `(#dupglossary_sample $n:num) => do
      let env ← getEnv
      runGlossary (env.constants.toList.take n.getNat)
  | _ => throwError "ill-formed #dupglossary_sample command"

/-! ## §9  Build-time generation

Like `ResolutionLadder` / `QExpansionLadder`, the glossary builder runs in the
elaborator (interpreted), so the full-corpus `#dupglossary` is slow; the default
build drives the same bounded sample (`120000`, matching the ladders) and writes
both atlas files.  The full scan stays available on demand. -/

#dupglossary_sample 120000

-- Full-corpus glossary (slow under the interpreter); run on demand:
-- #dupglossary

end DuplicateGlossary

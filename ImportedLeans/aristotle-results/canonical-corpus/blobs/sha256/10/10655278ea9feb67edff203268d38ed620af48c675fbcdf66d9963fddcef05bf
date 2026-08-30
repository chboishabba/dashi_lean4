import RequestProject.Introspect
import Lean

/-!
# Anatomy: how much of the Lean 4 language composes each item, and its depth

The atlas layers say *where* a declaration lands.  This layer says *what it is
made of*: it dissects the reflected `Expr` value of every project declaration and
measures, concretely,

* **how much of the Lean 4 term language** is used to compose it — i.e. which of
  the twelve `Expr` constructors (`bvar`, `fvar`, `mvar`, `sort`, `const`, `app`,
  `lam`, `forallE`, `letE`, `lit`, `mdata`, `proj`) appear, and how often; and
* **the depth** — the maximum nesting depth of the term's abstract syntax tree.

Everything here is computed by reflection on the kernel's own `Expr`
representation (the same value `#stratify`/`#dualstratify` hash), so the numbers
are exactly what Lean stores, not an approximation.

## API

* `LangProfile` — the per-declaration anatomy record.
* `analyzeExpr` — dissect one `Expr`.
* `analyzeDecl` — reflect a declaration into its `LangProfile`.
* `#anatomy f`  — print the language profile + depth of `f`.
* `#anatomymap` — profile *every* project declaration and print a table.
* `projectAnatomy` — the reusable enumerator used by the animation layer.
-/

open Lean Meta Elab Command

namespace Anatomy

open Introspect

/-- The twelve term-language constructors of `Expr`, the alphabet a declaration is
written in. -/
inductive Kind where
  | bvar | fvar | mvar | sort | const | app
  | lam | forallE | letE | lit | mdata | proj
deriving DecidableEq, Repr

/-- All kinds, in display order. -/
def Kind.all : List Kind :=
  [.bvar, .fvar, .mvar, .sort, .const, .app, .lam, .forallE, .letE, .lit, .mdata, .proj]

/-- Short human label for a `Kind`. -/
def Kind.label : Kind → String
  | .bvar => "bvar"    | .fvar => "fvar"   | .mvar => "mvar"
  | .sort => "sort"    | .const => "const" | .app => "app"
  | .lam => "lam"      | .forallE => "∀/→" | .letE => "let"
  | .lit => "lit"      | .mdata => "mdata" | .proj => "proj"

/-- The anatomy of a declaration's term: per-constructor counts, total size, AST
depth, distinct-constant breadth, and the number of distinct constructors used. -/
structure LangProfile where
  counts   : List (Kind × Nat)   -- per-constructor occurrence counts
  size     : Nat                 -- total number of `Expr` nodes
  depth    : Nat                 -- maximum AST depth
  consts   : Nat                 -- number of *distinct* constants referenced
  features : Nat                 -- distinct constructors used (0..12): "how much of the language"
deriving Repr, Inhabited

/-- Maximum AST depth of an `Expr`. -/
partial def exprDepth : Expr → Nat
  | .app f a         => 1 + max (exprDepth f) (exprDepth a)
  | .lam _ t b _     => 1 + max (exprDepth t) (exprDepth b)
  | .forallE _ t b _ => 1 + max (exprDepth t) (exprDepth b)
  | .letE _ t v b _  => 1 + max (exprDepth t) (max (exprDepth v) (exprDepth b))
  | .mdata _ e       => 1 + exprDepth e
  | .proj _ _ e      => 1 + exprDepth e
  | _                => 1

/-- A flat array of twelve counters, one per `Kind` (same order as `Kind.all`). -/
abbrev Tally := Array Nat

/-- Index of a `Kind` in `Kind.all`. -/
def Kind.idx : Kind → Nat
  | .bvar => 0 | .fvar => 1 | .mvar => 2 | .sort => 3 | .const => 4 | .app => 5
  | .lam => 6  | .forallE => 7 | .letE => 8 | .lit => 9 | .mdata => 10 | .proj => 11

/-- Bump the counter for one kind. -/
def Tally.bump (t : Tally) (k : Kind) : Tally :=
  t.set! k.idx (t[k.idx]! + 1)

/-- Accumulate per-constructor counts over an `Expr`. -/
partial def tally : Expr → Tally → Tally
  | .bvar _,          t => t.bump .bvar
  | .fvar _,          t => t.bump .fvar
  | .mvar _,          t => t.bump .mvar
  | .sort _,          t => t.bump .sort
  | .const _ _,       t => t.bump .const
  | .lit _,           t => t.bump .lit
  | .app f a,         t => tally a (tally f (t.bump .app))
  | .lam _ ty b _,    t => tally b (tally ty (t.bump .lam))
  | .forallE _ ty b _,t => tally b (tally ty (t.bump .forallE))
  | .letE _ ty v b _, t => tally b (tally v (tally ty (t.bump .letE)))
  | .mdata _ e,       t => tally e (t.bump .mdata)
  | .proj _ _ e,      t => tally e (t.bump .proj)

/-- Dissect an `Expr` into a `LangProfile`. -/
def analyzeExpr (e : Expr) : LangProfile :=
  let t := tally e (Array.replicate 12 0)
  let counts := Kind.all.map (fun k => (k, t[k.idx]!))
  let size := t.foldl (· + ·) 0
  let features := (counts.filter (fun (_, n) => n > 0)).length
  { counts := counts
    size := size
    depth := exprDepth e
    consts := e.getUsedConstants.toList.eraseDups.length
    features := features }

/-- Reflect a declaration into its `LangProfile`. -/
def analyzeDecl (decl : Name) : MetaM LangProfile := do
  let env ← getEnv
  match env.find? decl with
  | some info =>
    match info.value? with
    | some e => return analyzeExpr e
    | none   => throwError "declaration {decl} has no value to analyse"
  | none => throwError "unknown declaration {decl}"

/-- One named profile (used by the animation layer). -/
structure NamedProfile where
  name    : Name
  profile : LangProfile
deriving Inhabited

/-- Enumerate and analyse every project declaration, sorted by descending size. -/
def projectAnatomy : CommandElabM (List NamedProfile) := do
  let env ← getEnv
  let mut out : List NamedProfile := []
  for (name, info) in env.constants.toList do
    if isProjectDecl name.toString then
      if let some e := info.value? then
        out := { name := name, profile := analyzeExpr e } :: out
  return out.toArray.qsort (fun a b =>
    if a.profile.size ≠ b.profile.size then a.profile.size > b.profile.size
    else a.name.toString < b.name.toString) |>.toList

/-- A compact one-line rendering of the nonzero constructor counts. -/
def renderCounts (p : LangProfile) : String :=
  String.intercalate "  "
    ((p.counts.filter (fun (_, n) => n > 0)).map (fun (k, n) => s!"{k.label}:{n}"))

/-! ## Commands -/

/-- `#anatomy f` prints how much of the Lean 4 language composes `f`, and its depth. -/
syntax (name := anatomyCmd) "#anatomy " ident : command

@[command_elab anatomyCmd]
def elabAnatomy : CommandElab := fun stx => do
  match stx with
  | `(#anatomy $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let p ← liftTermElabM <| Meta.MetaM.run' (analyzeDecl name)
    logInfo s!"[Anatomy] {name}\n  depth:    {p.depth}\n  size:     {p.size} nodes\n  consts:   {p.consts} distinct\n  language: {p.features}/12 Expr constructors used\n  makeup:   {renderCounts p}"
  | _ => throwError "ill-formed #anatomy command"

/-- `#anatomymap` profiles every project declaration and prints a table. -/
syntax (name := anatomymapCmd) "#anatomymap" : command

@[command_elab anatomymapCmd]
def elabAnatomymap : CommandElab := fun _ => do
  let profs ← projectAnatomy
  let mut out := s!"[Anatomy Map]  {profs.length} declarations  (sorted by size)\n"
  out := out ++ "  depth  size  consts  lang   declaration\n"
  for np in profs do
    let p := np.profile
    let pad (n w : Nat) : String :=
      let s := toString n
      "".pushn ' ' (w - min w s.length) ++ s
    out := out ++ s!"  {pad p.depth 5}  {pad p.size 4}  {pad p.consts 6}  {pad p.features 2}/12  {np.name}\n"
  logInfo out

/-! ## Test suite -/

#anatomy Nat.add
#anatomy List.map
#anatomy Prod.fst

#anatomymap

end Anatomy

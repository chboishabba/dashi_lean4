import RequestProject.DeclWeave
import RequestProject.Irrep170
import Mathlib
import Lean

/-!
# EnvWeave — atom payload arrows and the full system-environment scan

`DeclWeave` embeds a *single* declaration's AST graph into the irrep-1 CRT
address space (`196883 = 71 · 59 · 47` cells), with structural arrows between
`Expr` nodes.  Two things were still missing, and this module supplies them:

1. **Atom payload arrows.**  The leaf constructors `bvar`, `fvar`, `mvar`,
   `sort`, `const`, `lit` carry *arithmetic content* but have no `Expr`
   children, so the structural recursion alone treats them as bare leaves.  Here
   each atom is given typed **payload arrows** to the data it carries (a de
   Bruijn index, a name/string hash, a universe depth, the universe instances of
   a `const`, or the literal value itself).  With these arrows the full graph is
   denser than the structural recursion captures: atoms become *internal* nodes.

2. **The full system-environment scan.**  Instead of weaving one declaration,
   `#envweave` streams over *every* constant in the ambient `Environment` — Lean
   4 core, Batteries/Std, and Mathlib — fingerprinting each declaration's
   statement and proof term, computing its CRT cell, and accumulating corpus
   statistics (total declarations, total AST + payload nodes, distinct cells,
   smush count, faithful count, deepest declaration, and the corpus
   arithmetization number).

## Honest scope

This addressing is **purely combinatorial / structural**.  In particular:

* Cell collision is *not* claimed to entail any semantic equivalence of
  declarations.
* The arithmetization `Nat` is a structural hash of the whole corpus, not a
  mathematical invariant of Lean + Mathlib.
* `saturationIrrep` is a computational fact about how fingerprints distribute
  across the Monster irrep dimensions, not a theorem about mathematical content.

The one genuinely content-level statement is the *literal invariant*: an
arithmetic literal is addressed by its own value, so e.g. `payloadFingerprint`
of the literal `71` is `71` and is `≡ 0 (mod 71)`.  Arithmetic content is
substrate-independent because arithmetic is arithmetic.

The single mathematical theorem worth proving is `arithmetize_comm`: the corpus
arithmetization does not depend on the order declarations are fed into the
grinder, because `Nat` addition is commutative.

Commands:

* `#envweave`        — scan the *entire* ambient environment and report the
  corpus statistics; also writes a compact summary to `atlas_envweave.json`.
* `#envweave_sample n` — the same scan restricted to the first `n` declarations
  (a fast, bounded demonstration of the streaming machinery).
-/

open Lean Meta Elab Command

namespace EnvWeave

open ExprAddress DeclWeave

/-! ## §1  Extended atom arrows — the payload nodes of leaf constructors -/

/-- A universe level, collapsed to a `Nat` by its nesting depth. -/
def levelToNat (l : Level) : Nat := l.depth

/-- The arithmetic payload carried by an atom constructor.  These are the targets
of an atom's **payload arrows**: the content that the structural recursion does
not reach because atoms have no `Expr` children. -/
inductive PayloadNode
  | nat   (v : Nat)   -- literal natural number / de Bruijn index
  | str   (h : Nat)   -- string-literal hash
  | name  (h : Nat)   -- name hash (fvar / mvar / const head)
  | level (n : Nat)   -- universe level (collapsed to its depth)
  | univ  (h : Nat)   -- a universe instance of a `const`
  deriving Repr, DecidableEq

/-- The payload arrows of a single `Expr` node.  Composite nodes (`app`, `lam`,
…) carry no payload (their content lives in their `Expr` children); the six atom
constructors each get one or more payload arrows. -/
def atomPayloads : Expr → List PayloadNode
  | .bvar i          => [.nat i]
  | .fvar id         => [.name id.name.toString.hash.toNat]
  | .mvar id         => [.name id.name.toString.hash.toNat]
  | .sort lvl        => [.level (levelToNat lvl)]
  | .const n us      => .name n.toString.hash.toNat ::
                          us.map (fun u => .univ (levelToNat u))
  | .lit (.natVal v) => [.nat v]
  | .lit (.strVal s) => [.str s.hash.toNat]
  | _                => []

/-- The fingerprint of a payload node: its underlying `Nat`.  A literal natural
number is its own fingerprint — *arithmetic is its own address*. -/
def payloadFingerprint : PayloadNode → Nat
  | .nat v   => v
  | .str h   => h
  | .name h  => h
  | .level n => n
  | .univ h  => h

/-- The number of payload arrows emitted by a single node. -/
def atomPayloadCount : Expr → Nat
  | .bvar _          => 1
  | .fvar _          => 1
  | .mvar _          => 1
  | .sort _          => 1
  | .const _ us      => 1 + us.length
  | .lit (.natVal _) => 1
  | .lit (.strVal _) => 1
  | _                => 0

/-- `atomPayloadCount` counts exactly the payload arrows of `atomPayloads`. -/
theorem atomPayloadCount_eq (e : Expr) :
    atomPayloadCount e = (atomPayloads e).length := by
  cases e with
  | lit l => cases l <;> simp [atomPayloadCount, atomPayloads]
  | const n us => simp [atomPayloadCount, atomPayloads, Nat.add_comm]
  | _ => simp [atomPayloadCount, atomPayloads]

/-- The **full node count**: structural nodes plus payload nodes, in a single
pass.  Every atom now contributes its payload arrows on top of itself, so the
full graph is strictly larger than the structural tree wherever atoms occur. -/
def fullNodeCount : Expr → Nat
  | e@(.app f a)         => 1 + atomPayloadCount e + fullNodeCount f + fullNodeCount a
  | e@(.lam _ t b _)     => 1 + atomPayloadCount e + fullNodeCount t + fullNodeCount b
  | e@(.forallE _ t b _) => 1 + atomPayloadCount e + fullNodeCount t + fullNodeCount b
  | e@(.letE _ t v b _)  =>
      1 + atomPayloadCount e + fullNodeCount t + fullNodeCount v + fullNodeCount b
  | e@(.mdata _ x)       => 1 + atomPayloadCount e + fullNodeCount x
  | e@(.proj _ _ x)      => 1 + atomPayloadCount e + fullNodeCount x
  | e                    => 1 + atomPayloadCount e

/-- The full graph always has at least as many nodes as the structural tree. -/
theorem exprNodeCount_le_fullNodeCount (e : Expr) :
    exprNodeCount e ≤ fullNodeCount e := by
  induction e with
  | app f a ihf iha => simp only [exprNodeCount, fullNodeCount]; omega
  | lam _ t b _ iht ihb => simp only [exprNodeCount, fullNodeCount]; omega
  | forallE _ t b _ iht ihb => simp only [exprNodeCount, fullNodeCount]; omega
  | letE _ t v b _ iht ihv ihb => simp only [exprNodeCount, fullNodeCount]; omega
  | mdata _ x ih => simp only [exprNodeCount, fullNodeCount]; omega
  | proj _ _ x ih => simp only [exprNodeCount, fullNodeCount]; omega
  | _ => simp [exprNodeCount, fullNodeCount, atomPayloadCount]

/-! ### The literal invariant (the strongest honest claim) -/

/-- A `natVal` literal's single payload is the literal value itself. -/
theorem atomPayloads_natVal (v : Nat) :
    atomPayloads (.lit (.natVal v)) = [PayloadNode.nat v] := rfl

/-- The fingerprint of the literal `v`'s payload is `v` — its own address. -/
theorem payloadFingerprint_natVal (v : Nat) :
    payloadFingerprint (PayloadNode.nat v) = v := rfl

/-- **The literal-71 invariant.**  The arithmetic content `71` is addressed by
itself, hence vanishes modulo `71`.  Arithmetic content is substrate-independent. -/
theorem lit_71_invariant :
    payloadFingerprint (PayloadNode.nat 71) % 71 = 0 := by decide

/-! ## §2  Declaration fingerprints and the full environment scan -/

/-- The fingerprint of an expression: its cached structural hash. -/
def nodeFingerprint (e : Expr) : Nat := e.hash.toNat

/-- A per-declaration summary record. -/
structure DeclSummary where
  name      : Name
  stmtFP    : Nat                -- statement (type) fingerprint
  proofFP   : Nat                -- proof (value) fingerprint, `0` if none
  nodeCount : Nat                -- structural AST nodes of the statement
  fullNodes : Nat               -- AST + payload nodes of the statement
  stmtCell  : Nat × Nat × Nat    -- CRT address of the statement fingerprint
  proofCell : Nat × Nat × Nat    -- CRT address of the proof fingerprint
  faithful  : Bool               -- `fullNodes < 196883`
  deriving Inhabited

/-- Summarise one declaration. -/
def summariseDecl (name : Name) (info : ConstantInfo) : DeclSummary :=
  let stmtFP := nodeFingerprint info.type
  let proofFP := match info.value? with
    | some v => nodeFingerprint v
    | none   => 0
  let nc := exprNodeCount info.type
  let fn := fullNodeCount info.type
  { name      := name
    stmtFP    := stmtFP
    proofFP   := proofFP
    nodeCount := nc
    fullNodes := fn
    stmtCell  := crtTriple stmtFP
    proofCell := crtTriple proofFP
    faithful  := fn < 196883 }

/-- Scan the ambient environment into an array of declaration summaries.

This materialises one record per constant; on the full Lean + Mathlib
environment that is hundreds of thousands of records, so the `#envweave`
command below uses an equivalent *streaming* fold that never holds more than the
running statistics.  This function is the reference API and is best used on a
bounded environment slice. -/
def scanEnv : MetaM (Array DeclSummary) := do
  let env ← getEnv
  let mut results : Array DeclSummary := #[]
  for (name, info) in env.constants.toList do
    results := results.push (summariseDecl name info)
  return results

/-! ## §3  Corpus statistics -/

/-- Aggregate statistics over a corpus of declaration summaries. -/
structure CorpusStats where
  totalDecls         : Nat
  totalNodes         : Nat       -- Σ fullNodes
  distinctStmtCells  : Nat       -- distinct statement CRT cells
  distinctProofCells : Nat       -- distinct proof CRT cells
  smushCount         : Nat       -- declarations sharing a statement cell
  faithfulCount      : Nat       -- declarations with fullNodes < 196883
  deepestDecl        : Name      -- declaration with the most full nodes
  deepestCount       : Nat
  deriving Inhabited

/-- Fold a corpus of summaries into its aggregate statistics. -/
def corpusStats (decls : Array DeclSummary) : CorpusStats := Id.run do
  let mut total : Nat := 0
  let mut stmtCells : Std.HashSet Nat := {}
  let mut proofCells : Std.HashSet Nat := {}
  let mut faithful : Nat := 0
  let mut deepName : Name := .anonymous
  let mut deepCnt : Nat := 0
  for d in decls do
    total := total + d.fullNodes
    let (a, b, c) := d.stmtCell
    stmtCells := stmtCells.insert (cellCode (a * 2773 + b * 47 + c))
    let (pa, pb, pc) := d.proofCell
    proofCells := proofCells.insert (cellCode (pa * 2773 + pb * 47 + pc))
    if d.faithful then faithful := faithful + 1
    if d.fullNodes > deepCnt then
      deepCnt := d.fullNodes
      deepName := d.name
  return {
    totalDecls         := decls.size
    totalNodes         := total
    distinctStmtCells  := stmtCells.size
    distinctProofCells := proofCells.size
    smushCount         := decls.size - stmtCells.size
    faithfulCount      := faithful
    deepestDecl        := deepName
    deepestCount       := deepCnt }

/-! ## §4  The saturation irrep (computational) -/

/-- The `i`-th Monster irrep dimension, used as a CRT modulus (`1` past the
table). -/
def irrepModulus (i : Nat) : Nat := (Irrep170.monsterIrrepDegrees[i]?).getD 1

/-- `true` iff the fingerprints have pairwise-distinct residues modulo `m`. -/
def distinctMod (fps : Array Nat) (m : Nat) : Bool := Id.run do
  let mut seen : Std.HashSet Nat := {}
  for f in fps do
    let r := f % m
    if seen.contains r then
      return false
    seen := seen.insert r
  return true

/-- The smallest irrep index at which the statement fingerprints all have
distinct CRT residues (i.e. the corpus stops smushing).  Searches the `194`
Monster irrep dimensions; returns `194` if none suffices.

This is a *computational* fact about fingerprint distribution, not a theorem
about mathematical content.  Note that any corpus with more than `196883`
declarations *must* overflow irrep 1 (pigeonhole), so saturation then happens at
the next large enough irrep. -/
def saturationIrrep (fps : Array Nat) : Nat :=
  match (List.range 194).find? (fun i => distinctMod fps (irrepModulus i)) with
  | some i => i
  | none   => 194

/-! ## §5  The arithmetization -/

/-- The single `Nat` representing the entire corpus: the sum over all
declarations of (statement fingerprint + proof fingerprint).  The Fleischwolf
output — the whole library ground into one number. -/
def arithmetize (decls : Array DeclSummary) : Nat :=
  decls.foldl (fun acc d => acc + d.stmtFP + d.proofFP) 0

/-! ## §6  The one theorem worth proving -/

/-- **The corpus arithmetization is invariant under declaration reordering.**
The Monster's name for Mathlib does not depend on the order you feed
declarations into the grinder, because `Nat` addition is commutative.  The
Fleischwolf is commutative. -/
theorem arithmetize_comm (decls : Array DeclSummary) :
    arithmetize decls = arithmetize decls.reverse := by
  unfold arithmetize
  rw [← Array.foldl_toList, ← Array.foldl_toList, Array.toList_reverse]
  have h : ∀ (l : List DeclSummary) (a : Nat),
      l.foldl (fun acc d => acc + d.stmtFP + d.proofFP) a
        = a + (l.map (fun d => d.stmtFP + d.proofFP)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons x xs ih => intro a; simp [ih]; ring
  rw [h, h]
  simp [List.sum_reverse]

/-! ## §7  Streaming scan and report -/

/-- A streaming corpus scan over a list of `(name, info)` pairs.  Returns the
aggregate statistics together with the array of statement fingerprints (for the
saturation computation) and the corpus arithmetization, without ever holding the
full per-declaration array. -/
def streamScan (pairs : List (Name × ConstantInfo)) :
    CorpusStats × Array Nat × Nat := Id.run do
  let mut total : Nat := 0
  let mut count : Nat := 0
  let mut stmtCells : Std.HashSet Nat := {}
  let mut proofCells : Std.HashSet Nat := {}
  let mut faithful : Nat := 0
  let mut deepName : Name := .anonymous
  let mut deepCnt : Nat := 0
  let mut fps : Array Nat := #[]
  let mut arith : Nat := 0
  for (name, info) in pairs do
    let d := summariseDecl name info
    count := count + 1
    total := total + d.fullNodes
    arith := arith + d.stmtFP + d.proofFP
    fps := fps.push d.stmtFP
    let (a, b, c) := d.stmtCell
    stmtCells := stmtCells.insert (cellCode (a * 2773 + b * 47 + c))
    let (pa, pb, pc) := d.proofCell
    proofCells := proofCells.insert (cellCode (pa * 2773 + pb * 47 + pc))
    if d.faithful then faithful := faithful + 1
    if d.fullNodes > deepCnt then
      deepCnt := d.fullNodes
      deepName := name
  let stats : CorpusStats := {
    totalDecls         := count
    totalNodes         := total
    distinctStmtCells  := stmtCells.size
    distinctProofCells := proofCells.size
    smushCount         := count - stmtCells.size
    faithfulCount      := faithful
    deepestDecl        := deepName
    deepestCount       := deepCnt }
  return (stats, fps, arith)

/-- Render the corpus report. -/
def corpusReport (stats : CorpusStats) (satIrrep arith : Nat) : String :=
  s!"[Aristo Env Weave] full system-environment scan\n" ++
  s!"  ├── total declarations     : {stats.totalDecls}\n" ++
  s!"  ├── total AST+payload nodes : {stats.totalNodes}\n" ++
  s!"  ├── distinct stmt cells    : {stats.distinctStmtCells}\n" ++
  s!"  ├── distinct proof cells   : {stats.distinctProofCells}\n" ++
  s!"  ├── smushed (stmt) decls   : {stats.smushCount}\n" ++
  s!"  ├── faithful decls         : {stats.faithfulCount}\n" ++
  s!"  ├── saturation irrep       : {satIrrep} (dim {irrepModulus satIrrep})\n" ++
  s!"  ├── deepest declaration    : {stats.deepestDecl} ({stats.deepestCount} nodes)\n" ++
  s!"  └── corpus arithmetization : {arith}"

/-- The compact summary JSON for `atlas_envweave.json`. -/
def corpusJson (stats : CorpusStats) (satIrrep arith : Nat) : String :=
  "{\n" ++
  s!"  \"totalDecls\": {stats.totalDecls},\n" ++
  s!"  \"totalNodes\": {stats.totalNodes},\n" ++
  s!"  \"distinctStmtCells\": {stats.distinctStmtCells},\n" ++
  s!"  \"distinctProofCells\": {stats.distinctProofCells},\n" ++
  s!"  \"smushCount\": {stats.smushCount},\n" ++
  s!"  \"faithfulCount\": {stats.faithfulCount},\n" ++
  s!"  \"saturationIrrep\": {satIrrep},\n" ++
  s!"  \"saturationModulus\": {irrepModulus satIrrep},\n" ++
  s!"  \"deepestDecl\": \"{stats.deepestDecl}\",\n" ++
  s!"  \"deepestCount\": {stats.deepestCount},\n" ++
  s!"  \"arithmetization\": {arith}\n" ++
  "}\n"

/-! ## §8  Commands -/

/-- `#envweave` scans the *entire* ambient environment (Lean core, Batteries/Std,
Mathlib, and this project), streams the corpus statistics, computes the
saturation irrep and arithmetization, logs the report, and writes a compact
summary to `atlas_envweave.json`. -/
syntax (name := envweaveCmd) "#envweave" : command

@[command_elab envweaveCmd]
def elabEnvweave : CommandElab := fun _ => do
  let env ← getEnv
  let (stats, fps, arith) := streamScan env.constants.toList
  let satIrrep := saturationIrrep fps
  logInfo (corpusReport stats satIrrep arith)
  IO.FS.writeFile "atlas_envweave.json" (corpusJson stats satIrrep arith)

/-- `#envweave_sample n` runs the same streaming scan over the first `n`
declarations of the ambient environment — a fast, bounded demonstration. -/
syntax (name := envweaveSampleCmd) "#envweave_sample " num : command

@[command_elab envweaveSampleCmd]
def elabEnvweaveSample : CommandElab := fun stx => do
  match stx with
  | `(#envweave_sample $n:num) => do
    let env ← getEnv
    let pairs := env.constants.toList.take n.getNat
    let (stats, fps, arith) := streamScan pairs
    let satIrrep := saturationIrrep fps
    logInfo (corpusReport stats satIrrep arith)
  | _ => throwError "ill-formed #envweave_sample command"

/-! ## §9  Test suite -/

#envweave_sample 2000

-- The full scan over Lean core + Batteries/Std + Mathlib + this project.
#envweave

end EnvWeave

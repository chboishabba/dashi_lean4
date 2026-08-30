import RequestProject.MonsterBitmapSVG
import Lean

/-!
# ExprAddress — structural-sum addressing of declarations into the Monster bitmap

This layer realises the requested addressing scheme: instead of feeding an
*arbitrary* number `N` into the Monster–Moonshine bitmap pipeline
(`RequestProject.MonsterBitmap`), each **declaration** is given an *intrinsic*
integer `k` computed from the shape of its own expression tree, and that `k` is
then used as the bitmap input.

## The structural fingerprint `k`

Every `Lean.Expr` node carries a constructor.  We assign each of the twelve
constructors a fixed numeric code (the order in which they are declared):

| code | constructor | code | constructor |
|------|-------------|------|-------------|
| 0    | `bvar`      | 6    | `app`       |
| 1    | `fvar`      | 7    | `lam`       |
| 2    | `mvar`      | 8    | `forallE`   |
| 3    | `sort`      | 9    | `letE`      |
| 4    | `const`     | 10   | `mdata`     |
| 5    | `lit`       | 11   | `proj`      |

The fingerprint `k = exprStructuralSum e` is the sum of these codes over **every
node** of the tree, recursing through application heads/arguments, binder
domains/bodies, `let` types/values/bodies, `mdata` payloads and projections.  A
declaration's fingerprint `declStructuralSum` sums the fingerprints of both its
**type** and its **value**.  This makes `k` an intrinsic structural hash:
deeper, branchier declarations get larger `k`; structurally identical
declarations get the same `k` (a visible collision in the bitmap).

## CRT addressing

The smallest non-trivial Monster irrep has dimension
`196883 = 47 · 59 · 71`, and the first non-trivial `j`-coefficient is one step
past it: `196884 = 196883 + 1`, so `196884 ≡ 1 (mod 47), (mod 59), (mod 71)`.
By the Chinese Remainder Theorem the triple `(k % 71, k % 59, k % 47)` is a
**unique** address for every `k` in `[0, 196883)` (`crtTriple_inj`); declaration
`196883` wraps back to the same triple as `0` (`crtTriple_wraparound`),
distinguishable only by the larger irreps.

## Honest accounting

The addressing is **purely combinatorial**.  Nothing here asserts a
mathematical connection between the Monster group and the content of the
addressed declarations: the bitmap simply records where each declaration's
structural fingerprint lands in the irrep / CRT coordinate space.

Commands:

* `#exprstratify f`  — print the structural fingerprint, CRT triple, and bitmap
  brightness of declaration `f`.
* `#exprsweep`       — sweep this project's declarations, printing their
  fingerprints, CRT triples, and any wraparound collisions.
-/

open Lean Meta Elab Command

namespace ExprAddress

/-! ## §1  Structural fingerprint of an expression tree -/

/-- The constructor code of an `Expr` node (its declaration order, `0 … 11`). -/
def exprCtorCode : Expr → Nat
  | .bvar _        => 0
  | .fvar _        => 1
  | .mvar _        => 2
  | .sort _        => 3
  | .const _ _     => 4
  | .lit _         => 5
  | .app _ _       => 6
  | .lam _ _ _ _   => 7
  | .forallE _ _ _ _ => 8
  | .letE _ _ _ _ _  => 9
  | .mdata _ _     => 10
  | .proj _ _ _    => 11

/-- The structural fingerprint of an expression: the sum of every node's
constructor code over the whole tree. -/
partial def exprStructuralSum : Expr → Nat
  | e@(.app f a)         => exprCtorCode e + exprStructuralSum f + exprStructuralSum a
  | e@(.lam _ t b _)     => exprCtorCode e + exprStructuralSum t + exprStructuralSum b
  | e@(.forallE _ t b _) => exprCtorCode e + exprStructuralSum t + exprStructuralSum b
  | e@(.letE _ t v b _)  => exprCtorCode e + exprStructuralSum t + exprStructuralSum v + exprStructuralSum b
  | e@(.mdata _ x)       => exprCtorCode e + exprStructuralSum x
  | e@(.proj _ _ x)      => exprCtorCode e + exprStructuralSum x
  | e                    => exprCtorCode e

/-- The structural fingerprint of a declaration: the sum of the fingerprints of
its type and (if present) its value. -/
def declStructuralSum (decl : Name) : MetaM Nat := do
  let env ← getEnv
  match env.find? decl with
  | some info =>
    let tSum := exprStructuralSum info.type
    let vSum := match info.value? with
      | some v => exprStructuralSum v
      | none   => 0
    return tSum + vSum
  | none => throwError "unknown declaration {decl}"

/-! ## §2  CRT addressing via the first irrep's prime factorisation -/

/-- The three supersingular primes whose product is the smallest non-trivial
Monster irrep dimension `196883 = 47 · 59 · 71`. -/
def crtPrimes : List Nat := [71, 59, 47]

/-- The CRT address of `k`: its residues modulo the three primes `71, 59, 47`. -/
def crtTriple (k : Nat) : Nat × Nat × Nat := (k % 71, k % 59, k % 47)

/-- `196883 = 47 · 59 · 71`, the smallest non-trivial Monster irrep dimension. -/
theorem crt_modulus : 71 * 59 * 47 = 196883 := by decide

/-- The first non-trivial `j`-coefficient is one past the first irrep dimension. -/
theorem head_identity : (196884 : Nat) = 71 * 59 * 47 + 1 := by decide

/-- Declaration index `196884` has CRT address `(1, 1, 1)` — the identity shift. -/
theorem crtTriple_head : crtTriple 196884 = (1, 1, 1) := by decide

/-- `196884` wraps back to the same CRT address as declaration `1`. -/
theorem crtTriple_wraparound : crtTriple 196884 = crtTriple 1 := by decide

/-- **CRT addressing is injective on `[0, 196883)`.**  Two declarations whose
structural fingerprints are below `196883` and share a CRT triple are equal:
the triple `(k % 71, k % 59, k % 47)` uniquely addresses every `k` in that
range. -/
theorem crtTriple_inj {a b : Nat} (ha : a < 196883) (hb : b < 196883)
    (h : crtTriple a = crtTriple b) : a = b := by
  simp only [crtTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  have e1 : a ≡ b [MOD 71] := h1
  have e2 : a ≡ b [MOD 59] := h2
  have e3 : a ≡ b [MOD 47] := h3
  have e12 : a ≡ b [MOD 71 * 59] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e1, e2⟩
  have e123 : a ≡ b [MOD 71 * 59 * 47] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (by decide)).mp ⟨e12, e3⟩
  have hmod : a ≡ b [MOD 196883] := by norm_num at e123 ⊢; exact e123
  unfold Nat.ModEq at hmod
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hmod

/-! ## §3  Feeding the fingerprint into the bitmap pipeline -/

/-- The number of visibly-lit bitmap cells for declaration-fingerprint `k`
(reuses `MonsterBitmapSVG.litCountOf`: cells whose normalized intensity is
`≥ 32 / 255`). -/
def litCount (k : Nat) : Nat := MonsterBitmapSVG.litCountOf k

/-- A textual report of where fingerprint `k` lands. -/
def reportOf (decl : Name) (k : Nat) : String :=
  let (a, b, c) := crtTriple k
  s!"[Aristo Structural Address] {decl}\n  ├── Structural fingerprint k = {k}\n  ├── CRT triple (mod 71,59,47) = ({a}, {b}, {c})\n  ├── First-irrep slot = {k % 196883}{if k ≥ 196883 then s!" (wrapped, {k / 196883}× past 196883)" else ""}\n  └── Bitmap brightness = {litCount k} cells lit (intensity ≥ 32)"

/-! ## §4  Commands -/

/-- `#exprstratify f` prints the structural fingerprint, CRT triple, and bitmap
brightness of declaration `f`. -/
syntax (name := exprstratifyCmd) "#exprstratify " ident : command

@[command_elab exprstratifyCmd]
def elabExprstratify : CommandElab := fun stx => do
  match stx with
  | `(#exprstratify $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let k ← liftTermElabM <| Meta.MetaM.run' (declStructuralSum name)
    logInfo (reportOf name k)
  | _ => throwError "ill-formed #exprstratify command"

/-- Is `s` a project-source declaration name (in one of our namespaces and not an
auto-generated internal helper)? -/
def isProjectDecl (s : String) : Bool :=
  let inProject :=
    s.startsWith "Holograms." || s.startsWith "AristoTask." ||
    s.startsWith "DualAtlas." || s.startsWith "MonsterAddress." ||
    s.startsWith "MonsterBitmap." || s.startsWith "ExprAddress."
  let internal := (s.splitOn "._").length > 1 || (s.splitOn "match_").length > 1
  inProject && !internal

/-- `#exprsweep` sweeps the project's declarations: it prints each declaration's
structural fingerprint and CRT triple, and reports how many distinct CRT
addresses are realised (i.e. detects wraparound / structural collisions). -/
syntax (name := exprsweepCmd) "#exprsweep" : command

@[command_elab exprsweepCmd]
def elabExprsweep : CommandElab := fun _ => do
  let env ← getEnv
  let mut rows : Array (Name × Nat) := #[]
  for (name, info) in env.constants.toList do
    if isProjectDecl name.toString then
      let tSum := exprStructuralSum info.type
      let vSum := match info.value? with
        | some v => exprStructuralSum v
        | none   => 0
      rows := rows.push (name, tSum + vSum)
  let sorted := rows.qsort (fun a b => a.2 < b.2)
  let mut triples : Std.HashSet (Nat × Nat × Nat) := {}
  for (_, k) in sorted do
    triples := triples.insert (crtTriple k)
  let mut out := s!"[Structural Address Sweep] {sorted.size} declarations · {triples.size} distinct CRT addresses\n"
  for (name, k) in sorted do
    let (a, b, c) := crtTriple k
    out := out ++ s!"  k={k}  ({a},{b},{c})  {name}\n"
  logInfo out

/-! ## §5  Test suite -/

#exprstratify Nat.add
#exprstratify List.map
#exprstratify Prod.fst

#exprsweep

end ExprAddress

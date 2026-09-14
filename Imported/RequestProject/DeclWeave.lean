import RequestProject.ExprAddress
import Lean

/-!
# DeclWeave — faithful embedding of AST graphs into the Monster irrep address space

`ExprAddress` gives every *declaration* a single structural fingerprint `k` and a
CRT address `crtTriple k = (k % 71, k % 59, k % 47)` in the `196883`-cell space of
the smallest non-trivial Monster irrep (`196883 = 71 · 59 · 47`).  This layer
zooms *inside* a declaration: it treats the declaration's expression as a directed
graph — **nodes** are `Lean.Expr` constructors, **arrows** are the structural edges
(`app → head`, `app → arg`, `lam → domain`, `lam → body`, `forallE → …`,
`letE → …`, `mdata → payload`, `proj → expr`) — and embeds that graph into the
irrep-1 address space.

## The node address carries content, not just shape

Each AST node is mapped to a cell by `nodeContent`:

| node                | address (`nodeContent`)         |
|---------------------|---------------------------------|
| `lit (natVal v)`    | `v` — *the number is its address*|
| `lit (strVal s)`    | `s.hash`                        |
| `bvar i`            | `i` — the de Bruijn index       |
| `fvar id` / `mvar id`| `id.name.hash`                 |
| `sort u`            | `u.depth`                       |
| `const n _`         | `n.hash`                        |
| `app/lam/…` (composite) | its constructor code        |

So a literal `71` lands at `crtTriple 71 = (0, 12, 24)`; the head dimension
`196883` lands at the origin `(0, 0, 0)`; `196884` lands at `(1, 1, 1)`.  The
address space is *semantically loaded*: equal-valued literals share a cell.

## Faithful vs. smushed

The embedding `node ↦ crtTriple (nodeContent node)` is **faithful** on a
declaration when distinct nodes land on distinct cells (`isFaithful`).  A *smush*
is a collision: two distinct nodes share a cell, so the weave cannot tell them
apart.  Two structural facts pin down the geometry of faithfulness:

* `faithful_of_small_distinct` — if a declaration's node addresses are pairwise
  distinct and all below `196883`, the embedding is faithful (no smush).  This is
  exactly CRT injectivity (`ExprAddress.crtTriple_inj`) lifted to the node list.
* `smush_of_overflow` — if a declaration has **more than `196883` nodes**, it
  *must* smush, by pigeonhole: irrep 1 only has `196883` cells.  This is the
  precise content of "irrep 1 has `71·59·47` cells to spread the data into".

## The Yoneda reading (honest scope)

A node is determined, *within the `[0, 196883)` window*, by its cell:
`nodeContent_crt_inj` says two nodes with equal cells and addresses below the
irrep dimension have equal addresses.  This is the constructive Yoneda content of
the embedding — a node is recovered from how it sits in the irrep-1 coordinate
space.  It is **not** claimed that equal cells imply isomorphic subtrees, nor that
the Monster group acts on the embedded declarations; the addressing is purely
combinatorial.

Commands:

* `#declweave f`  — print `f`'s node count, arrow count, faithfulness, smush count,
  and the cells of its first few nodes.
-/

open Lean Meta Elab Command

namespace DeclWeave

open ExprAddress

/-! ## §1  AST node enumeration -/

/-- The immediate structural children of an `Expr` node (the targets of its
arrows). -/
def exprChildren : Expr → List Expr
  | .app f a         => [f, a]
  | .lam _ t b _     => [t, b]
  | .forallE _ t b _ => [t, b]
  | .letE _ t v b _  => [t, v, b]
  | .mdata _ x       => [x]
  | .proj _ _ x      => [x]
  | _                => []

/-- All nodes of an expression tree, in DFS pre-order (root first). -/
def exprNodes : Expr → List Expr
  | e@(.app f a)         => e :: (exprNodes f ++ exprNodes a)
  | e@(.lam _ t b _)     => e :: (exprNodes t ++ exprNodes b)
  | e@(.forallE _ t b _) => e :: (exprNodes t ++ exprNodes b)
  | e@(.letE _ t v b _)  => e :: (exprNodes t ++ exprNodes v ++ exprNodes b)
  | e@(.mdata _ x)       => e :: exprNodes x
  | e@(.proj _ _ x)      => e :: exprNodes x
  | e                    => [e]

/-- The number of nodes in an expression tree. -/
def exprNodeCount : Expr → Nat
  | .app f a         => 1 + exprNodeCount f + exprNodeCount a
  | .lam _ t b _     => 1 + exprNodeCount t + exprNodeCount b
  | .forallE _ t b _ => 1 + exprNodeCount t + exprNodeCount b
  | .letE _ t v b _  => 1 + exprNodeCount t + exprNodeCount v + exprNodeCount b
  | .mdata _ x       => 1 + exprNodeCount x
  | .proj _ _ x      => 1 + exprNodeCount x
  | _                => 1

/-- `exprNodes` enumerates exactly `exprNodeCount` nodes. -/
theorem exprNodes_length_eq_count (e : Expr) :
    (exprNodes e).length = exprNodeCount e := by
  induction e with
  | app f a ihf iha => simp [exprNodes, exprNodeCount, ihf, iha]; omega
  | lam _ t b _ iht ihb => simp [exprNodes, exprNodeCount, iht, ihb]; omega
  | forallE _ t b _ iht ihb => simp [exprNodes, exprNodeCount, iht, ihb]; omega
  | letE _ t v b _ iht ihv ihb => simp [exprNodes, exprNodeCount, iht, ihv, ihb]; omega
  | mdata _ x ih => simp [exprNodes, exprNodeCount, ih]; omega
  | proj _ _ x ih => simp [exprNodes, exprNodeCount, ih]; omega
  | _ => rfl

/-- Every expression has at least one node (itself). -/
theorem exprNodeCount_pos (e : Expr) : 1 ≤ exprNodeCount e := by
  cases e <;> simp [exprNodeCount] <;> omega

/-- The arrows of an expression tree, as `(parent index, child index)` pairs in the
DFS pre-order numbering, where the root is assigned index `base`. -/
def exprArrowsFrom (base : Nat) : Expr → List (Nat × Nat)
  | .app f a =>
      let bf := base + 1
      let ba := bf + exprNodeCount f
      (base, bf) :: (base, ba) :: (exprArrowsFrom bf f ++ exprArrowsFrom ba a)
  | .lam _ t b _ =>
      let bt := base + 1
      let bb := bt + exprNodeCount t
      (base, bt) :: (base, bb) :: (exprArrowsFrom bt t ++ exprArrowsFrom bb b)
  | .forallE _ t b _ =>
      let bt := base + 1
      let bb := bt + exprNodeCount t
      (base, bt) :: (base, bb) :: (exprArrowsFrom bt t ++ exprArrowsFrom bb b)
  | .letE _ t v b _ =>
      let bt := base + 1
      let bv := bt + exprNodeCount t
      let bb := bv + exprNodeCount v
      (base, bt) :: (base, bv) :: (base, bb) ::
        (exprArrowsFrom bt t ++ exprArrowsFrom bv v ++ exprArrowsFrom bb b)
  | .mdata _ x => (base, base + 1) :: exprArrowsFrom (base + 1) x
  | .proj _ _ x => (base, base + 1) :: exprArrowsFrom (base + 1) x
  | _ => []

/-- The arrows of an expression tree (root indexed `0`). -/
def exprArrows (e : Expr) : List (Nat × Nat) := exprArrowsFrom 0 e

/-- Every arrow endpoint of `exprArrowsFrom base e` lies in the index window
`[base, base + exprNodeCount e)`. -/
theorem exprArrowsFrom_mem_window (e : Expr) (base : Nat) :
    ∀ p ∈ exprArrowsFrom base e,
      base ≤ p.1 ∧ p.1 < base + exprNodeCount e ∧
      base ≤ p.2 ∧ p.2 < base + exprNodeCount e := by
  induction e generalizing base with
  | app f a ihf iha =>
    intro p hp
    have pf := exprNodeCount_pos f
    have pa := exprNodeCount_pos a
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons, List.mem_append] at hp ⊢
    rcases hp with h | h | h | h
    · subst h; simp; omega
    · subst h; simp; omega
    · have := ihf (base+1) p h; omega
    · have := iha (base+1+exprNodeCount f) p h; omega
  | lam _ t b _ iht ihb =>
    intro p hp
    have pt := exprNodeCount_pos t
    have pb := exprNodeCount_pos b
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons, List.mem_append] at hp ⊢
    rcases hp with h | h | h | h
    · subst h; simp; omega
    · subst h; simp; omega
    · have := iht (base+1) p h; omega
    · have := ihb (base+1+exprNodeCount t) p h; omega
  | forallE _ t b _ iht ihb =>
    intro p hp
    have pt := exprNodeCount_pos t
    have pb := exprNodeCount_pos b
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons, List.mem_append] at hp ⊢
    rcases hp with h | h | h | h
    · subst h; simp; omega
    · subst h; simp; omega
    · have := iht (base+1) p h; omega
    · have := ihb (base+1+exprNodeCount t) p h; omega
  | letE _ t v b _ iht ihv ihb =>
    intro p hp
    have pt := exprNodeCount_pos t
    have pv := exprNodeCount_pos v
    have pb := exprNodeCount_pos b
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons, List.mem_append] at hp ⊢
    rcases hp with h | h | h | ((h | h) | h)
    · subst h; simp; omega
    · subst h; simp; omega
    · subst h; simp; omega
    · have := iht (base+1) p h; omega
    · have := ihv (base+1+exprNodeCount t) p h; omega
    · have := ihb (base+1+exprNodeCount t+exprNodeCount v) p h; omega
  | mdata _ x ih =>
    intro p hp
    have px := exprNodeCount_pos x
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons] at hp ⊢
    rcases hp with h | h
    · subst h; simp; omega
    · have := ih (base+1) p h; omega
  | proj _ _ x ih =>
    intro p hp
    have px := exprNodeCount_pos x
    simp only [exprArrowsFrom, exprNodeCount, List.mem_cons] at hp ⊢
    rcases hp with h | h
    · subst h; simp; omega
    · have := ih (base+1) p h; omega
  | _ => intro p hp; simp [exprArrowsFrom] at hp

/-- **Arrows are valid.**  Every arrow of `e` references node indices below the
node count. -/
theorem exprArrows_valid (e : Expr) :
    ∀ p ∈ exprArrows e, p.1 < exprNodeCount e ∧ p.2 < exprNodeCount e := by
  intro p hp
  have := exprArrowsFrom_mem_window e 0 p hp
  omega

/-! ## §2  The node address (content-aware) and its CRT cell -/

/-- The address of a single AST node.  Leaf nodes contribute their *content* (the
literal value, the de Bruijn index, the name/string hash, the universe depth);
composite nodes contribute their constructor code. -/
def nodeContent : Expr → Nat
  | .bvar i            => i
  | .fvar id           => id.name.hash.toNat
  | .mvar id           => id.name.hash.toNat
  | .sort u            => u.depth
  | .const n _         => n.hash.toNat
  | .lit (.natVal v)   => v
  | .lit (.strVal s)   => s.hash.toNat
  | e                  => exprCtorCode e

/-- The CRT cell of a node: `crtTriple` of its content. -/
def nodeCell (nd : Expr) : Nat × Nat × Nat := crtTriple (nodeContent nd)

/-- A natural-number code for the cell `(k%71, k%59, k%47)` as a mixed-radix digit
string; an injective `[0,196883)`-valued packing of the CRT triple. -/
def cellCode (k : Nat) : Nat := (k % 71) * 2773 + (k % 59) * 47 + (k % 47)
-- note: 2773 = 59 · 47, the radix for the top CRT digit `k % 71`

/-- The cell codes of all nodes of `e`, in DFS order. -/
def nodeCellCodes (e : Expr) : List Nat :=
  (exprNodes e).map (fun nd => cellCode (nodeContent nd))

/-- The embedding is **faithful** when no two nodes share a cell. -/
def isFaithful (e : Expr) : Bool := decide (nodeCellCodes e).Nodup

/-- The number of smushed nodes: how many nodes collide onto an already-used cell. -/
def smushCount (e : Expr) : Nat :=
  (nodeCellCodes e).length - (nodeCellCodes e).dedup.length

/-! ### Worked addresses (the address space carries arithmetic) -/

/-- A `natVal` literal is addressed by its own value. -/
theorem nodeContent_lit_natVal (v : Nat) : nodeContent (.lit (.natVal v)) = v := rfl

/-- A bound variable is addressed by its de Bruijn index. -/
theorem nodeContent_bvar (i : Nat) : nodeContent (.bvar i) = i := rfl

/-- The literal `71` lands at CRT cell `(0, 12, 24)`. -/
theorem cell_lit_71 : nodeCell (.lit (.natVal 71)) = (0, 12, 24) := by decide

/-- The head dimension `196883` lands at the origin of irrep 1. -/
theorem crtTriple_dim : crtTriple 196883 = (0, 0, 0) := by decide

/-- The first `j`-coefficient `196884` lands at the identity shift `(1,1,1)`. -/
theorem crtTriple_jhead : crtTriple 196884 = (1, 1, 1) := by decide

/-! ## §3  Geometry of the irrep-1 cell space -/

/-- Every cell code is a genuine address in irrep 1: `cellCode k < 196883`. -/
theorem cellCode_lt (k : Nat) : cellCode k < 196883 := by
  have h71 : k % 71 < 71 := Nat.mod_lt _ (by decide)
  have h59 : k % 59 < 59 := Nat.mod_lt _ (by decide)
  have h47 : k % 47 < 47 := Nat.mod_lt _ (by decide)
  unfold cellCode
  omega

set_option maxHeartbeats 1000000 in
/-- The cell packing is injective on `[0, 196883)`: two addresses below the irrep
dimension with the same cell code are equal. -/
theorem cellCode_inj {a b : Nat} (ha : a < 196883) (hb : b < 196883)
    (h : cellCode a = cellCode b) : a = b := by
  have h71a : a % 71 < 71 := Nat.mod_lt _ (by decide)
  have h59a : a % 59 < 59 := Nat.mod_lt _ (by decide)
  have h47a : a % 47 < 47 := Nat.mod_lt _ (by decide)
  have h71b : b % 71 < 71 := Nat.mod_lt _ (by decide)
  have h59b : b % 59 < 59 := Nat.mod_lt _ (by decide)
  have h47b : b % 47 < 47 := Nat.mod_lt _ (by decide)
  unfold cellCode at h
  have e1 : a % 71 = b % 71 := by omega
  have e2 : a % 59 = b % 59 := by omega
  have e3 : a % 47 = b % 47 := by omega
  apply crtTriple_inj ha hb
  unfold crtTriple
  rw [e1, e2, e3]

/-- **Node CRT injectivity (Yoneda content).**  Two nodes whose addresses are both
below the irrep dimension and which land on the same CRT cell have equal address. -/
theorem nodeContent_crt_inj {a b : Expr}
    (ha : nodeContent a < 196883) (hb : nodeContent b < 196883)
    (h : crtTriple (nodeContent a) = crtTriple (nodeContent b)) :
    nodeContent a = nodeContent b :=
  crtTriple_inj ha hb h

/-! ## §4  Faithfulness theorems -/

/-- **Faithful embedding from distinct small addresses.**  If a declaration's node
addresses are pairwise distinct and all below `196883`, then its nodes occupy
distinct cells — the embedding is faithful (no smush). -/
theorem faithful_of_small_distinct (e : Expr)
    (hsmall : ∀ nd ∈ exprNodes e, nodeContent nd < 196883)
    (hnd : ((exprNodes e).map nodeContent).Nodup) :
    (nodeCellCodes e).Nodup := by
  have hrw : nodeCellCodes e = ((exprNodes e).map nodeContent).map cellCode := by
    unfold nodeCellCodes; rw [List.map_map]; rfl
  rw [hrw]
  apply List.Nodup.map_on _ hnd
  intro x hx y hy hxy
  rw [List.mem_map] at hx hy
  obtain ⟨ndx, hndx, rfl⟩ := hx
  obtain ⟨ndy, hndy, rfl⟩ := hy
  exact cellCode_inj (hsmall _ hndx) (hsmall _ hndy) hxy

/-- **Pigeonhole: overflow forces a smush.**  Irrep 1 has only `196883` cells, so
any declaration with more than `196883` nodes must collide. -/
theorem smush_of_overflow (e : Expr) (h : 196883 < (exprNodes e).length) :
    ¬ (nodeCellCodes e).Nodup := by
  intro hnd
  have hlen : (nodeCellCodes e).length = (exprNodes e).length := by
    unfold nodeCellCodes; rw [List.length_map]
  have hb : ∀ x ∈ nodeCellCodes e, x < 196883 := by
    intro x hx
    unfold nodeCellCodes at hx
    rw [List.mem_map] at hx
    obtain ⟨nd, _, rfl⟩ := hx
    exact cellCode_lt _
  have hsub : (nodeCellCodes e).toFinset ⊆ Finset.range 196883 := by
    intro x hx
    rw [List.mem_toFinset] at hx
    rw [Finset.mem_range]
    exact hb x hx
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hcard
  omega

/-- A faithful declaration has at most `196883` nodes (contrapositive of the
pigeonhole bound). -/
theorem nodeCount_le_of_faithful (e : Expr) (h : (nodeCellCodes e).Nodup) :
    (exprNodes e).length ≤ 196883 := by
  by_contra hc
  push_neg at hc
  exact smush_of_overflow e hc h

/-! ## §5  Command -/

/-- Build the per-declaration weave report. -/
def weaveReport (decl : Name) (e : Expr) : String :=
  let nodes := exprNodes e
  let arrows := exprArrows e
  let cells := nodeCellCodes e
  let faithful := isFaithful e
  let smush := smushCount e
  let sample := (nodes.take 6).map (fun nd =>
    let (a, b, c) := nodeCell nd
    s!"({a},{b},{c})")
  s!"[Aristo Decl Weave] {decl}\n" ++
  s!"  ├── AST nodes              : {nodes.length}\n" ++
  s!"  ├── AST arrows             : {arrows.length}\n" ++
  s!"  ├── distinct cells         : {cells.dedup.length}\n" ++
  s!"  ├── smushed nodes          : {smush}\n" ++
  s!"  ├── faithful (no smush)    : {faithful}\n" ++
  s!"  └── first node cells       : {String.intercalate " " sample}"

/-- `#declweave f` prints the AST node/arrow counts of declaration `f`, whether its
embedding into the irrep-1 cell space is faithful, its smush count, and the cells
of its first few nodes. -/
syntax (name := declweaveCmd) "#declweave " ident : command

@[command_elab declweaveCmd]
def elabDeclweave : CommandElab := fun stx => do
  match stx with
  | `(#declweave $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let env ← getEnv
    match env.find? name with
    | some info =>
      let e := match info.value? with
        | some v => v
        | none   => info.type
      logInfo (weaveReport name e)
    | none => throwError "unknown declaration {name}"
  | _ => throwError "ill-formed #declweave command"

/-! ## §6  Test suite -/

#declweave Nat.add
#declweave List.map
#declweave Prod.fst

end DeclWeave

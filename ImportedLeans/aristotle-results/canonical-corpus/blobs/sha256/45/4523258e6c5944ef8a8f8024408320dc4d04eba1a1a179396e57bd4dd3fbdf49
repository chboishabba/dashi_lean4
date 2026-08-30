import Mathlib
import RequestProject.ExprAddress
import Lean

/-!
# SemanticPerturbation — every Lean 4 declaration has `2 ^ n` semantics-preserving
forms that all resolve to the same semantics.

This module formalises the claim:

> *each Lean 4 decl can be perturbed into `2 ^ n` different forms that retain its
> semantics, and those should resolve to the same semantics.*

The argument has two halves, an **abstract combinatorial core** and a **concrete
realisation on `Lean.Expr`**, plus a **reflection front-end** that exhibits the
`2 ^ n` forms of a real declaration and checks (via the elaborator's
`Meta.isDefEq`) that they are all definitionally equal.

## §1  Abstract core: `n` independent semantics-preserving toggles ⇒ `2 ^ n` forms

A *perturbation family* is a finite list of `n` maps `step i : α → α`, each of
which preserves a chosen semantics `sem : α → β` (`PerturbFamily.preserves`).
For any bit-mask `b : Fin n → Bool` we apply exactly the chosen steps
(`applyMask`).  Two facts:

* **All forms resolve to the same semantics** (`applyMask_preserves`): for *every*
  mask `b`, `sem (applyMask steps b a) = sem a`.  No independence hypothesis is
  needed — preservation composes.
* **There are `2 ^ n` masks** (`card_masks`): `Fintype.card (Fin n → Bool) = 2 ^ n`.

So a declaration `a` is carried to `2 ^ n` forms (one per mask), each with the
same semantics.

## §2  Concrete realisation on `Lean.Expr`

The cleanest *genuine* semantics-preserving perturbation in Lean's kernel is an
**`mdata` annotation**: the kernel ignores `Expr.mdata`, so `e` and
`.mdata d e` are definitionally equal and `consumeMData` erases the annotation.
`perturb m e` tags `e` with the natural number `m`; then

* **semantics preserved** (`perturb_consumeMData`): `(perturb m e).consumeMData =
  e.consumeMData` — the annotation vanishes under the kernel's `mdata` erasure;
* **the forms are genuinely distinct** (`perturb_injective`): `m ↦ perturb m e`
  is injective, so the `2 ^ n` masks `m ∈ [0, 2 ^ n)` give `2 ^ n` *distinct*
  expressions (`perturb_card`), all with the same `consumeMData`.

This is honest about scope: the formally verified invariant is `consumeMData`
(the kernel's annotation erasure); the stronger statement that the perturbed
forms are *definitionally equal to the original* is exhibited operationally by
the `#perturb` command below using `Meta.isDefEq`.

## §3  Reflection front-end

`#perturb f` (optionally `#perturb f n`) takes the value of declaration `f`,
builds its `2 ^ n` `mdata`-perturbed forms, confirms they are pairwise distinct
as expressions yet all definitionally equal to the original, and reports.
-/

open Lean Meta Elab Command

namespace SemanticPerturbation

/-! ## §1  Abstract core -/

section Abstract

variable {α : Type*} {β : Type*} {n : ℕ}

/-- Apply, in order, the steps selected by `b` over a list of indices. -/
def applyOver (steps : Fin n → α → α) (b : Fin n → Bool) : List (Fin n) → α → α
  | [], a => a
  | i :: l, a => bif b i then steps i (applyOver steps b l a) else applyOver steps b l a

/-- Apply exactly the steps selected by the bit-mask `b` (over all `n` indices). -/
def applyMask (steps : Fin n → α → α) (b : Fin n → Bool) (a : α) : α :=
  applyOver steps b (List.finRange n) a

/-- **Composed preservation over a list.**  If every step preserves `sem`, then
applying any selection of them preserves `sem`. -/
theorem applyOver_preserves (sem : α → β) (steps : Fin n → α → α)
    (h : ∀ i a, sem (steps i a) = sem a) (b : Fin n → Bool) (l : List (Fin n)) (a : α) :
    sem (applyOver steps b l a) = sem a := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      simp only [applyOver]
      cases hb : b i with
      | false => simpa using ih
      | true => simp only [cond_true]; rw [h]; exact ih

/-- **All `2 ^ n` forms resolve to the same semantics.**  For *every* mask `b`,
applying the selected perturbations to `a` leaves `sem a` unchanged. -/
theorem applyMask_preserves (sem : α → β) (steps : Fin n → α → α)
    (h : ∀ i a, sem (steps i a) = sem a) (b : Fin n → Bool) (a : α) :
    sem (applyMask steps b a) = sem a :=
  applyOver_preserves sem steps h b _ a

/-- **There are exactly `2 ^ n` masks**, hence at most `2 ^ n` perturbed forms. -/
theorem card_masks (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

end Abstract

/-! ## §2  Concrete realisation on `Lean.Expr` -/

attribute [local instance] Classical.propDecidable

/-- The metadata key under which a perturbation index is recorded. -/
def perturbKey : Name := `RequestProject.semanticPerturb

/-- The `m`-th semantics-preserving perturbation of an expression: tag `e` with
an `mdata` annotation carrying the natural number `m`.  The kernel ignores
`mdata`, so this changes the expression structurally without changing its
denotation. -/
def perturb (m : Nat) (e : Expr) : Expr :=
  .mdata (⟨[(perturbKey, DataValue.ofNat m)]⟩ : KVMap) e

/-- **Semantics preserved.**  Every perturbed form erases (via the kernel's
`mdata` erasure `consumeMData`) to the *same* expression as the original. -/
theorem perturb_consumeMData (m : Nat) (e : Expr) :
    (perturb m e).consumeMData = e.consumeMData := rfl

/-- **The perturbed forms are genuinely distinct.**  Tagging with distinct
indices yields distinct expressions: `m ↦ perturb m e` is injective. -/
theorem perturb_injective (e : Expr) : Function.Injective (fun m => perturb m e) := by
  intro a b h
  simp only [perturb, Expr.mdata.injEq, KVMap.mk.injEq, List.cons.injEq,
    Prod.mk.injEq, DataValue.ofNat.injEq] at h
  tauto

/-- **`2 ^ n` distinct forms, one per mask, all with the same semantics.**  The
`2 ^ n` indices `m ∈ [0, 2 ^ n)` give `2 ^ n` pairwise-distinct perturbed
expressions of `e` (and, by `perturb_consumeMData`, every one of them erases to
`e.consumeMData`). -/
theorem perturb_card (e : Expr) (n : ℕ) :
    ((Finset.range (2 ^ n)).image (fun m => perturb m e)).card = 2 ^ n := by
  rw [Finset.card_image_of_injective _ (perturb_injective e), Finset.card_range]

/-- The set of all `2 ^ n` perturbed forms of `e`. -/
def perturbForms (n : Nat) (e : Expr) : List Expr :=
  (List.range (2 ^ n)).map (fun m => perturb m e)

/-! ## §3  Reflection front-end -/

/-- Build the `2 ^ n` perturbed forms of declaration `decl`'s value, check that
they are pairwise distinct as expressions yet all definitionally equal to the
original, and produce a report. -/
def perturbReport (decl : Name) (n : Nat) : MetaM String := do
  let env ← getEnv
  match env.find? decl with
  | none => throwError "unknown declaration {decl}"
  | some info =>
    let some e := info.value?
      | throwError "declaration {decl} has no value to perturb"
    let forms := perturbForms n e
    -- all forms are definitionally equal to the original
    let mut allDefEq := true
    for f in forms do
      let eq ← Meta.isDefEq f e
      unless eq do
        allDefEq := false
    -- the forms are pairwise distinct as expressions
    let distinct := forms.eraseDups.length == forms.length
    let semHash := (Expr.consumeMData (perturb 0 e)).hash.toNat
    let origHash := (Expr.consumeMData e).hash.toNat
    let report :=
      s!"[Aristo Semantic Perturbation] {decl}\n" ++
      s!"  ├── n = {n}  ⇒  2^n = {2 ^ n} perturbation masks\n" ++
      s!"  ├── distinct perturbed forms      = {forms.length} (all different = {distinct})\n" ++
      s!"  ├── all definitionally equal      = {allDefEq} (Meta.isDefEq vs. original)\n" ++
      s!"  ├── semantic core hash (perturbed)= {semHash}\n" ++
      s!"  └── semantic core hash (original) = {origHash}  (equal = {semHash == origHash})"
    return report

/-- `#perturb f` exhibits the `2 ^ 3 = 8` semantics-preserving forms of `f`.
`#perturb f n` uses `2 ^ n` forms. -/
syntax (name := perturbCmd) "#perturb " ident (num)? : command

@[command_elab perturbCmd]
def elabPerturb : CommandElab := fun stx => do
  match stx with
  | `(#perturb $id:ident $[$nstx?]?) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadCore id.getId
    let n := match nstx? with | some s => s.getNat | none => 3
    let report ← liftTermElabM <| Meta.MetaM.run' (perturbReport name n)
    logInfo report
  | _ => throwError "ill-formed #perturb command"

/-! ## §4  Test suite -/

#perturb Nat.add
#perturb List.map 4
#perturb Prod.fst

end SemanticPerturbation

import Integration.Kernel.Quotient

/-!
# A finite algorithmic instance: the three-vertex frontier

`Agda/DASHI/Computation/SSSPThreeFrontierLinearExtensionQuotientBidiExact.agda`
and `…/SSSPThreeFrontierBinaryTernaryFactorExact.agda` build, by hand, a
six-element carrier of linear extensions of a three-vertex frontier, an exact
`3 × 2` chart for it, and a consumer that reads only the minimum.  Those Agda
modules are genuine definitions with `refl`-checked equations, but the
"consumer quotient" claim there is a list of pointwise equalities and a
`Bool`-valued boundary record.  Here the same carrier is built in Lean and the
claim is stated and proved as an instance of `Integration.Kernel.Quotient`.

## What is proved

* `orderEquiv : Order3 ≃ Vertex × Bool` — the **exact factorisation**: the six
  linear extensions are, canonically, a ternary *minimum class* together with a
  binary *tail orientation*, and the equivalence is literally
  `Quotient.pair minVertex tail` (`orderEquiv_apply`, `pair_bijective`).
* `card_order3` — the carrier has six elements, `3 * 2`.
* `min_collides`, `tail_separates` — the shortest-path consumer, which needs
  only the minimum, identifies two distinct linear extensions; the full pairwise
  relation sheet still separates them (`sheet_injective`).
* **`tail_does_not_descend`** — the discarded orientation is not a function of
  what the consumer keeps.  Discarding it is a *quotient*, not a derivation.
* `minVertex_descends_through_sheet` — conversely the consumer coordinate does
  descend through the full sheet, so the compression is sound.
* `fibre_card` — every consumer class has exactly two elements: the retained
  residual fibre is a genuine binary fibre, uniformly across the three classes.
* `tail_refines_strictly` and `min_still_correct_after_refinement` — a later
  query that does need the tail order **refines** the earlier quotient: the
  coarse reading remains a correct function of the finer one, so nothing that
  was reported before is retracted.

**Claim boundary.** `Order3` is a six-element enumeration and `Vertex` a
three-element one.  No shortest-path algorithm, no complexity claim, and no
sorting-barrier result is stated or used here; what is formalised is only the
consumer-quotient/residual-fibre structure of the finite example.
-/

namespace Integration.Kernel.Instances.SSSP

open Integration.Kernel.Quotient

/-! ## §1 The carrier -/

/-- Three frontier vertices. -/
inductive Vertex
  /-- First vertex. -/
  | a
  /-- Second vertex. -/
  | b
  /-- Third vertex. -/
  | c
  deriving DecidableEq, Fintype, Repr

/-- The six linear extensions of the frontier, named by their orders. -/
inductive Order3
  /-- `a < b < c`. -/
  | abc
  /-- `a < c < b`. -/
  | acb
  /-- `b < a < c`. -/
  | bac
  /-- `b < c < a`. -/
  | bca
  /-- `c < a < b`. -/
  | cab
  /-- `c < b < a`. -/
  | cba
  deriving DecidableEq, Fintype, Repr

open Vertex Order3

instance : Nonempty Vertex := ⟨Vertex.a⟩

/-- The position of a vertex in a linear extension. -/
def rank : Order3 → Vertex → ℕ
  | abc, a => 0 | abc, b => 1 | abc, c => 2
  | acb, a => 0 | acb, c => 1 | acb, b => 2
  | bac, b => 0 | bac, a => 1 | bac, c => 2
  | bca, b => 0 | bca, c => 1 | bca, a => 2
  | cab, c => 0 | cab, a => 1 | cab, b => 2
  | cba, c => 0 | cba, b => 1 | cba, a => 2

theorem card_order3 : Fintype.card Order3 = 3 * 2 := by decide

/-! ## §2 The three observations -/

/-- The full pairwise relation sheet: every ordered pair compared. -/
def sheet (o : Order3) : Vertex → Vertex → Ordering :=
  fun x y => compare (rank o x) (rank o y)

/-- The consumer coordinate: which vertex is the minimum. -/
def minVertex : Order3 → Vertex
  | abc | acb => a
  | bac | bca => b
  | cab | cba => c

/-- The two vertices other than `v`, listed in the fixed name order `a, b, c`. -/
def others : Vertex → Vertex × Vertex
  | a => (b, c)
  | b => (a, c)
  | c => (a, b)

/-- The residual coordinate: the orientation of the two non-minimal vertices,
relative to the fixed name order. -/
def tail (o : Order3) : Bool :=
  decide (rank o (others (minVertex o)).1 < rank o (others (minVertex o)).2)

/-! ## §3 The exact `3 × 2` factorisation -/

/-- Decoding a minimum class and a tail orientation back to a linear extension. -/
def decode : Vertex × Bool → Order3
  | (a, true) => abc
  | (a, false) => acb
  | (b, true) => bac
  | (b, false) => bca
  | (c, true) => cab
  | (c, false) => cba

/-- **The complete state is the consumer quotient together with the retained
residual fibre**, exactly: the six linear extensions are the product of the
ternary minimum class with the binary tail orientation. -/
def orderEquiv : Order3 ≃ Vertex × Bool where
  toFun := pair minVertex tail
  invFun := decode
  left_inv := by decide
  right_inv := by decide

theorem orderEquiv_apply (o : Order3) : orderEquiv o = (minVertex o, tail o) := rfl

theorem pair_bijective : Function.Bijective (pair minVertex tail) :=
  orderEquiv.bijective

/-! ## §4 The consumer quotient, and what it discards -/

theorem abc_ne_acb : abc ≠ acb := by decide

/-- The consumer identifies two distinct linear extensions. -/
theorem min_collides : minVertex abc = minVertex acb := rfl

/-- The full sheet still separates them. -/
theorem tail_separates : tail abc ≠ tail acb := by decide

theorem sheet_ne : sheet abc ≠ sheet acb := by decide

theorem sheet_injective : Function.Injective sheet := by decide

/-- **The discarded orientation is not recoverable from what the consumer
keeps.**  This is `Quotient.not_descendsThrough_of_collision` on the frontier. -/
theorem tail_does_not_descend : ¬ DescendsThrough tail minVertex :=
  not_descendsThrough_of_collision min_collides tail_separates

/-- The consumer coordinate *does* descend through the full relation sheet, so
reading only the minimum is a sound compression of the sheet. -/
theorem minVertex_descends_through_sheet : DescendsThrough minVertex sheet := by
  rw [descendsThrough_iff_refinedBy]
  intro x y h
  exact congrArg minVertex (sheet_injective h)

/-- Every consumer class is a two-element residual fibre. -/
theorem fibre_card (o : Order3) :
    (Finset.univ.filter fun o' => minVertex o' = minVertex o).card = 2 := by
  cases o <;> decide

/-! ## §5 A later query refines the quotient — it does not refute it -/

/-- Asking for the tail order strictly refines the minimum-only quotient. -/
theorem tail_refines_strictly : StrictlyRefines minVertex (pair minVertex tail) :=
  strictlyRefines_pair_of_separates minVertex tail min_collides tail_separates

/-- After the refinement the coarse reading is still a correct function of the
finer one: the earlier report was a quotient, not a mistake. -/
theorem min_still_correct_after_refinement :
    DescendsThrough minVertex (pair minVertex tail) :=
  refinement_is_not_refutation minVertex tail

/-- The refined observation is separating, so the refinement terminates the
question: after it, nothing on this carrier is left undetermined. -/
theorem refined_observation_separates {o o' : Order3}
    (h : pair minVertex tail o = pair minVertex tail o') : o = o' :=
  pair_bijective.injective h

end Integration.Kernel.Instances.SSSP

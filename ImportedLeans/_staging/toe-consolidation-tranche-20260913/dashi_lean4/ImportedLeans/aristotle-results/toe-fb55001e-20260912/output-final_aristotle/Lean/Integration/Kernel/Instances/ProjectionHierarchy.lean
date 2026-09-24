import Integration.Kernel.Quotient

/-!
# A projection hierarchy: one-way margins < pairwise tables < the full joint

`Integration.SourceExactWelds` already owns
`marginals_do_not_determine_interaction` and `interaction_zero_iff_separable`
for a **two**-variable table, and `Integration.Marginalisation` owns the
weighting side of the same fact.  So "margins do not determine the interaction"
is already a Lean theorem here, and this file does not restate it.

What is not yet owned is the **hierarchy**.  With three variables there are
three levels of summary, and each step loses something the next one keeps:

```
one-way margins   <   the three pairwise tables   <   the full joint cube
```

This file is the thin instance that separates all three levels, as consumer
quotients of one state space (the cube) in the sense of
`Integration.Kernel.Quotient`.

## What is proved

* **`oneWay_descends_through_pairwise`** — the upper step is genuine descent:
  the one-way margins are computable from the pairwise tables, so the coarse
  reading is a correct function of the finer one (refinement, not refutation).
* **`pairwise_does_not_descend_through_oneWay`** — but not conversely.  Witness:
  `indepCube` and `corrCube`, two cubes with *identical* one-way margins whose
  pairwise tables differ.
* **`cube_does_not_descend_through_pairwise`** — and the second step is lost
  too.  Witness: `evenCube` and `oddCube`, the two parity cubes, which agree on
  **all three** pairwise tables (and hence on all one-way margins) and differ
  everywhere pointwise.
* `hierarchy_is_strict` collects the two strictness statements, and
  `parity_cubes_agree_on_every_pairwise_table` /
  `contrast_cubes_agree_on_every_margin` are the explicit fixtures.

**Claim boundary.**  A "cube" here is a function `Bool → Bool → Bool → ℕ`; the
margins are sums of its values.  No probabilistic interpretation is used or
needed, and nothing is claimed about any dataset.
-/

namespace Integration.Kernel.Instances.ProjectionHierarchy

open Integration.Kernel.Quotient

/-! ## §1 The three levels -/

/-- A three-variable table of counts. -/
abbrev Cube : Type := Bool → Bool → Bool → ℕ

/-- The `(1,2)` pairwise table: sum out the third variable. -/
def p12 (f : Cube) (a b : Bool) : ℕ := f a b false + f a b true

/-- The `(1,3)` pairwise table: sum out the second variable. -/
def p13 (f : Cube) (a c : Bool) : ℕ := f a false c + f a true c

/-- The `(2,3)` pairwise table: sum out the first variable. -/
def p23 (f : Cube) (b c : Bool) : ℕ := f false b c + f true b c

/-- The first one-way margin. -/
def m1 (f : Cube) (a : Bool) : ℕ := p12 f a false + p12 f a true

/-- The second one-way margin. -/
def m2 (f : Cube) (b : Bool) : ℕ := p12 f false b + p12 f true b

/-- The third one-way margin. -/
def m3 (f : Cube) (c : Bool) : ℕ := p13 f false c + p13 f true c

/-- The one-way summary: six numbers. -/
def oneWayAll (f : Cube) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (m1 f false, m1 f true, m2 f false, m2 f true, m3 f false, m3 f true)

/-- The pairwise summary: twelve numbers. -/
def pairAll (f : Cube) : (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
  ((p12 f false false, p12 f false true, p12 f true false, p12 f true true),
   (p13 f false false, p13 f false true, p13 f true false, p13 f true true),
   (p23 f false false, p23 f false true, p23 f true false, p23 f true true))

/-! ## §2 The upper step is descent -/

/-- Every distinction the one-way summary makes is made by the pairwise
summary. -/
theorem oneWay_refined_by_pairwise : RefinedBy oneWayAll pairAll := by
  intro x y h
  simp only [pairAll, Prod.mk.injEq] at h
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨h5, h6, h7, h8⟩, -⟩ := h
  simp only [oneWayAll, m1, m2, m3, Prod.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- **The one-way margins descend through the pairwise tables.**  The coarse
reading survives as a correct function of the finer one. -/
theorem oneWay_descends_through_pairwise : DescendsThrough oneWayAll pairAll :=
  (descendsThrough_iff_refinedBy oneWayAll pairAll).mpr oneWay_refined_by_pairwise

/-- And the pairwise tables descend through the cube, trivially: they are
computed from it. -/
theorem pairwise_descends_through_cube : DescendsThrough pairAll (id : Cube → Cube) :=
  ⟨pairAll, fun _ => rfl⟩

/-! ## §3 Neither step is reversible

Level one: two cubes with the same one-way margins and different pairwise
tables. -/

/-- The flat cube: every cell `1`. -/
def indepCube : Cube := fun _ _ _ => 1

/-- A cube concentrated where the first two variables agree. -/
def corrCube : Cube := fun a b _ => if a = b then 2 else 0

theorem contrast_cubes_agree_on_every_margin : oneWayAll indepCube = oneWayAll corrCube := by
  decide

theorem contrast_cubes_differ_on_pairwise : pairAll indepCube ≠ pairAll corrCube := by decide

/-- **The pairwise tables are not a function of the one-way margins.** -/
theorem pairwise_does_not_descend_through_oneWay :
    ¬ DescendsThrough pairAll oneWayAll :=
  not_descendsThrough_of_collision contrast_cubes_agree_on_every_margin
    contrast_cubes_differ_on_pairwise

/-! Level two: the two parity cubes, which agree on all three pairwise tables. -/

/-- The even-parity cube. -/
def evenCube : Cube := fun a b c => if xor a (xor b c) then 0 else 1

/-- The odd-parity cube. -/
def oddCube : Cube := fun a b c => if xor a (xor b c) then 1 else 0

theorem parity_cubes_agree_on_every_pairwise_table : pairAll evenCube = pairAll oddCube := by
  decide

theorem parity_cubes_agree_on_every_margin : oneWayAll evenCube = oneWayAll oddCube :=
  oneWay_refined_by_pairwise _ _ parity_cubes_agree_on_every_pairwise_table

theorem parity_cubes_differ : evenCube ≠ oddCube := by
  intro h
  have : evenCube false false false = oddCube false false false := by rw [h]
  exact absurd this (by decide)

/-- **The joint cube is not a function of its pairwise tables.**  Two cubes can
agree on every pairwise table — and so on every one-way margin — and still be
different everywhere: third-order structure is invisible to second-order
summaries. -/
theorem cube_does_not_descend_through_pairwise :
    ¬ DescendsThrough (id : Cube → Cube) pairAll :=
  not_descendsThrough_of_collision parity_cubes_agree_on_every_pairwise_table parity_cubes_differ

/-- The hierarchy, collected: both steps lose information, and neither loss is
recoverable from the coarser level. -/
theorem hierarchy_is_strict :
    DescendsThrough oneWayAll pairAll ∧
      ¬ DescendsThrough pairAll oneWayAll ∧
        ¬ DescendsThrough (id : Cube → Cube) pairAll :=
  ⟨oneWay_descends_through_pairwise, pairwise_does_not_descend_through_oneWay,
    cube_does_not_descend_through_pairwise⟩

/-- The fibre statement of the same thing: the parity cube's pairwise class
contains a different cube, so the pairwise reading never point-identifies the
joint. -/
theorem pairwise_fibre_is_not_a_singleton :
    oddCube ∈ fibre pairAll evenCube ∧ oddCube ≠ evenCube :=
  ⟨parity_cubes_agree_on_every_pairwise_table.symm, fun h => parity_cubes_differ h.symm⟩

end Integration.Kernel.Instances.ProjectionHierarchy

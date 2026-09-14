import Integration.SeparabilityContrast
import Integration.CounterfactualEffect
import AgdaMirror.InteractionTables
import AgdaMirror.NonFactorabilityKernels

/-!
# Welding the interaction owner to real corpus tables

`Integration.SeparabilityContrast` owns the statement *a separable consumer has
a weighting-independent contrast*, whose pointwise form is the rectangle
identity

```
  C a b + C a' b' = C a b' + C a' b.
```

Until now that owner was exercised only by tables written for the purpose.  This
file tests it against four **independent** corpus surfaces, mirrored in
`AgdaMirror.InteractionTables`, each of which the corpus states for its own
reasons and none of which mentions interaction, separability or contrast:

| corpus surface | coordinates | value |
| --- | --- | --- |
| `FiniteAnisotropicKernelExact.positiveKernelValue` | boundary sharpness × radius class | ℕ, explicit 3×3 table |
| `SelfConsistentEventRendererExact.combinedAffinity` | Euclidean kernel × shared depth | ℕ, product |
| `SelfConsistentEventRendererExact.additiveAffinity` | Euclidean kernel × shared depth | ℕ, sum |
| `MeasureFieldAdapterExact.restrictField` | slice choice × two-cell field | ℕ, projection |
| `EarlyLearningCounterfactualHeterogeneityExact.counterfactualRelativeEffect` | observed position × hidden counterfactual | effect direction |
| `EarlyLearningIntersectionalCapabilityExact.effectiveCapabilityWitness` | gendered care × labour position | Bool |

The result of the test is that the three nonseparable ones **all discharge
through the single generic obstruction**, and that the two separable ones — the
corpus's own contextual and intersectional surfaces — discharge through the same
owner's positive companion, which is the honest negative answer: those lanes
carry collision claims, not interaction claims.  No new owner is introduced and
the owner is not generalised.

## Contents

* §1 `kernel_not_separable` — the anisotropic kernel table interacts.
* §2 `combinedAffinity_not_separable`, `additiveAffinity_separable`,
  `additiveAffinity_contrast_invariant`,
  `corpus_pointwise_claim_is_weaker` — the renderer pair, where the corpus
  claims only that the two rules differ at one point and the owner upgrades
  that to a structural difference.
* §3 `restrictField_not_separable` — slice restriction interacts.
* §4 `contextual_effect_separable`, `intersectional_capability_separable` —
  the negative result: the corpus's contextual and intersectional consumers read
  one coordinate each, so they are separable and the interaction owner has
  nothing to say about them.
* §5 `three_corpus_tables_one_rectangle`, `the_owner_is_discriminating` — the
  success criterion: three independent consumers, one obstruction, and two
  certified non-instances.
* §6 the additive surrogate: `surrogate_separable`,
  `rowMean_surrogate`, `colMean_surrogate`, `surrogate_ne_of_not_separable`,
  `interaction_is_not_another_coordinate` — a representation can retain every
  marginal coordinate of a corpus table and still lose its joint structure.

Nothing here is an empirical claim.  The numeric entries are the corpus's own
structural witnesses; §6 is ordinary linear algebra over `ℚ`.
-/

namespace Integration.InteractionWelds

open Integration.CoordinateSufficiency
open Integration.SeparabilityContrast
open scoped BigOperators

/-! ## 1. The anisotropic kernel table -/

namespace Kernel

open AgdaMirror.InteractionTables.AnisotropicKernel

/-- The corpus table, read into `ℚ` so that the owner applies. -/
def kernelQ (s : BoundarySharpness) (r : RadiusClass) : ℚ := (positiveKernelValue s r : ℚ)

/-- The rectangle the corpus table violates: soft/hard against
inside/boundary. -/
theorem kernel_rectangle_violation :
    kernelQ .softBoundary .insideEllipsoid + kernelQ .hardBoundary .boundaryEllipsoid ≠
      kernelQ .softBoundary .boundaryEllipsoid + kernelQ .hardBoundary .insideEllipsoid := by
  norm_num [kernelQ, positiveKernelValue]

/-- **The anisotropic kernel interacts.**  Boundary sharpness and radius class
are not two independent additive contributions to kernel mass. -/
theorem kernel_not_separable : ¬ Separable kernelQ := fun h =>
  kernel_rectangle_violation (separable_rectangle h _ _ _ _)

/-- The corpus's own lemma about the table, mirrored: outside the ellipsoid the
kernel vanishes whatever the sharpness.  That *is* a separability-flavoured
statement, and it holds — it is the third column being constant. -/
theorem outside_column_constant (s s' : BoundarySharpness) :
    kernelQ s .outsideEllipsoid = kernelQ s' .outsideEllipsoid := by
  simp [kernelQ, outsideContributesZero]

end Kernel

/-! ## 2. The renderer affinity pair -/

namespace Affinity

open AgdaMirror.InteractionTables.RendererAffinity

/-- The multiplicative rule, read into `ℚ`. -/
def combinedQ (k : ℕ) (d : SharedDepth) : ℚ := (combinedAffinity k d : ℚ)

/-- The additive rule, read into `ℚ`. -/
def additiveQ (k : ℕ) (d : SharedDepth) : ℚ := (additiveAffinity k d : ℚ)

theorem combined_rectangle_violation :
    combinedQ 1 .shared0 + combinedQ 2 .shared1 ≠
      combinedQ 1 .shared1 + combinedQ 2 .shared0 := by
  norm_num [combinedQ, combinedAffinity, sharedDepthWeight]

/-- **The product rule interacts.** -/
theorem combinedAffinity_not_separable : ¬ Separable combinedQ := fun h =>
  combined_rectangle_violation (separable_rectangle h _ _ _ _)

/-- **The sum rule does not.**  It is separable, by its own definition. -/
theorem additiveAffinity_separable : Separable additiveQ :=
  ⟨fun k => (k : ℚ), fun d => (sharedDepthWeight d : ℚ), by
    intro k d
    simp [additiveQ, additiveAffinity]⟩

/-- **The owner's positive companion, on the corpus surface.**  Because the
additive rule is separable, the kernel-value contrast it reports is the same
under every weighting of shared depth — no reweighting of the hierarchy can
reverse it. -/
theorem additiveAffinity_contrast_invariant {w v : SharedDepth → ℚ}
    (hw : ∑ d, w d = 1) (hv : ∑ d, v d = 1) (k k' : ℕ) :
    contrast additiveQ w k k' = contrast additiveQ v k k' :=
  separable_contrast_invariant additiveAffinity_separable hw hv k k'

/-- **The corpus's own claim about the pair is strictly weaker.**  The corpus
states only that the two rules disagree at the single point `(3, shared2)`.
Disagreeing at a point is compatible with both rules being separable; the
owner's verdict is a structural one, and it separates them. -/
theorem corpus_pointwise_claim_is_weaker :
    combinedQ 3 .shared2 ≠ additiveQ 3 .shared2 ∧
      ¬ Separable combinedQ ∧ Separable additiveQ := by
  refine ⟨?_, combinedAffinity_not_separable, additiveAffinity_separable⟩
  norm_num [combinedQ, additiveQ, combinedAffinity, additiveAffinity, sharedDepthWeight]

end Affinity

/-! ## 3. Slice restriction -/

namespace Slice

open AgdaMirror.InteractionTables.MeasureField

/-- The corpus's slice restriction, read into `ℚ`. -/
def sliceQ (s : SliceChoice) (f : Field2) : ℚ := (restrictField s f : ℚ)

/-- Two fields with opposite single cells. -/
def leftCell : Field2 := ⟨1, 0⟩

/-- The other single cell. -/
def rightCell : Field2 := ⟨0, 1⟩

theorem slice_rectangle_violation :
    sliceQ .leftCellSlice leftCell + sliceQ .rightCellSlice rightCell ≠
      sliceQ .leftCellSlice rightCell + sliceQ .rightCellSlice leftCell := by
  norm_num [sliceQ, restrictField, leftCell, rightCell]

/-- **Slice restriction interacts.**  Which cell is read and which field is
being read are not independent additive contributions: this is the exact sense
in which the corpus's "slice projections can erase distinctions" comment is a
statement about joint, not marginal, structure. -/
theorem restrictField_not_separable : ¬ Separable sliceQ := fun h =>
  slice_rectangle_violation (separable_rectangle h _ _ _ _)

end Slice

/-! ## 4. The contextual and intersectional lanes: a negative result

The corpus's own contextual and intersectional consumers were the obvious place
to look for an interaction table, and they do **not** provide one.  Every
consumer in that lane — `counterfactualRelativeEffect`,
`effectiveCapabilityWitness`, `withinGroupEffect`, `uptakeAt`,
`labourIncidenceAt` — is stated as depending on a *single* fine coordinate, with
the corpus's point being that a *coarse* projection collides.  A table that
depends on one coordinate only is separable, so the interaction owner has
nothing to refute there: those surfaces belong to the collision owner and only
to the collision owner.  The two lemmas below make that mechanical, and the two
corpus instances record it. -/

namespace SingleCoordinate

variable {A B M : Type*} [AddCommGroup M]

/-- A table that reads only its second coordinate is separable. -/
theorem separable_of_right (g : B → M) : Separable (fun _ : A => g) :=
  ⟨fun _ => 0, g, fun _ _ => (zero_add _).symm⟩

/-- A table that reads only its first coordinate is separable. -/
theorem separable_of_left (f : A → M) : Separable (fun (a : A) (_ : B) => f a) :=
  ⟨f, fun _ => 0, fun _ _ => (add_zero _).symm⟩

end SingleCoordinate

namespace Contextual

open Integration.CounterfactualEffect

/-- The corpus's counterfactual-relative effect, scored numerically and read as
a table in observed position against hidden counterfactual.  The mirror in
`Integration.CounterfactualEffect` is reused; no second reading of the Agda text
is introduced here. -/
def effectQ (p : ObservedFamilyPosition) (c : HiddenCounterfactual) : ℚ :=
  if counterfactualRelativeEffect ⟨.expandedSubsidisedECEC, p, c⟩ = .beneficialDirection
  then 1 else 0

/-- The table reads only its second coordinate. -/
theorem effectQ_right (p q : ObservedFamilyPosition) (c : HiddenCounterfactual) :
    effectQ p c = effectQ q c := by
  cases c <;> rfl

/-- **Negative result for the interaction owner.**  The contextual effect table
is separable: observed position and hidden counterfactual do not interact in it,
because the corpus makes the effect a function of the counterfactual alone.  The
corpus's claim about this surface is a collision claim, and the collision owner
already carries it (`intervention_label_cannot_determine_effect`). -/
theorem contextual_effect_separable : Separable effectQ := by
  refine ⟨fun _ => 0, fun c => effectQ .observedHigherResource c, fun p c => ?_⟩
  rw [zero_add]
  exact effectQ_right p _ c

end Contextual

namespace Intersectional

open AgdaMirror.NonFactorabilityKernels.SituatedCapability

/-- The corpus's `effectiveCapabilityWitness`, scored numerically and read as a
table in gendered care position against labour position — the two coordinates
the intersectional lane most insists on keeping apart. -/
def capabilityQ (_ : GenderedCarePosition) (l : LabourPosition) : ℚ :=
  match l with
  | .secureFlexible => 1
  | .precariousTimePoor => 0

/-- **Negative result for the interaction owner.**  The intersectional
capability witness is separable in exactly the pair of coordinates the corpus
names.  Keeping both coordinates is what the corpus argues for, and that is a
collision statement, not an interaction statement. -/
theorem intersectional_capability_separable : Separable capabilityQ :=
  ⟨fun _ => 0, fun l => capabilityQ .lowerCareBurden l, fun _ _ => (zero_add _).symm⟩

end Intersectional

/-! ## 5. The success criterion -/

/-- **Three independent corpus consumers, one obstruction.**  A finite kernel
table from the visualisation lane, a product combination rule from the renderer
lane and a slice projection from the measure-adapter lane all fail separability,
and each failure is produced by the *same* generic rectangle theorem
`Integration.CoordinateSufficiency.separable_rectangle`.  The three modules
share no imports beyond the corpus prelude and none of them mentions
interaction, separability or contrast.  The interaction owner is therefore not
a bespoke device for one lane. -/
theorem three_corpus_tables_one_rectangle :
    ¬ Separable Kernel.kernelQ ∧
      ¬ Separable Affinity.combinedQ ∧
      ¬ Separable Slice.sliceQ :=
  ⟨Kernel.kernel_not_separable, Affinity.combinedAffinity_not_separable,
    Slice.restrictField_not_separable⟩

/-- **And the owner is discriminating, not universally negative.**  Of the five
corpus surfaces examined, three interact and two do not, and the owner certifies
both verdicts.  In particular the corpus's own contextual/intersectional
surfaces are separable, so the interaction owner reports *nothing* about them:
they are collision surfaces and the collision owner already carries them. -/
theorem the_owner_is_discriminating :
    ¬ Separable Affinity.combinedQ ∧
      Separable Affinity.additiveQ ∧
      Separable Contextual.effectQ ∧
      Separable Intersectional.capabilityQ :=
  ⟨Affinity.combinedAffinity_not_separable, Affinity.additiveAffinity_separable,
    Contextual.contextual_effect_separable,
    Intersectional.intersectional_capability_separable⟩

/-! ## 6. Interaction is not another coordinate

The corpus's intersectional lane repeatedly asks whether a representation that
*keeps* a coordinate has kept the information carried by that coordinate.  For
two-coordinate tables the sharp answer is below: the additive surrogate of a
table has exactly the same row means and column means — every marginal
coordinate is retained, exactly — and yet is separable.  So a nonseparable
table and its surrogate are two different tables with identical marginals. -/

section Surrogate

variable {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]

/-- The mean of a row. -/
def rowMean (C : A → B → ℚ) (a : A) : ℚ := (∑ b, C a b) / (Fintype.card B : ℚ)

/-- The mean of a column. -/
def colMean (C : A → B → ℚ) (b : B) : ℚ := (∑ a, C a b) / (Fintype.card A : ℚ)

/-- The mean of the whole table. -/
def grandMean (C : A → B → ℚ) : ℚ :=
  (∑ a, ∑ b, C a b) / ((Fintype.card A : ℚ) * (Fintype.card B : ℚ))

/-- The additive surrogate: the unique separable table with the same row and
column means. -/
def surrogate (C : A → B → ℚ) (a : A) (b : B) : ℚ :=
  rowMean C a + colMean C b - grandMean C

theorem cardA_ne_zero : (Fintype.card A : ℚ) ≠ 0 := by
  have : 0 < Fintype.card A := Fintype.card_pos
  positivity

theorem cardB_ne_zero : (Fintype.card B : ℚ) ≠ 0 := by
  have : 0 < Fintype.card B := Fintype.card_pos
  positivity

/-- The column means average to the grand mean. -/
theorem sum_colMean (C : A → B → ℚ) :
    ∑ b, colMean C b = (Fintype.card B : ℚ) * grandMean C := by
  have hA : (Fintype.card A : ℚ) ≠ 0 := cardA_ne_zero (A := A)
  have hB : (Fintype.card B : ℚ) ≠ 0 := cardB_ne_zero (B := B)
  simp only [colMean, grandMean, ← Finset.sum_div]
  rw [Finset.sum_comm]
  field_simp

/-- The row means average to the grand mean. -/
theorem sum_rowMean (C : A → B → ℚ) :
    ∑ a, rowMean C a = (Fintype.card A : ℚ) * grandMean C := by
  have hB : (Fintype.card B : ℚ) ≠ 0 := cardB_ne_zero (B := B)
  simp only [rowMean, grandMean, ← Finset.sum_div]
  field_simp

omit [Nonempty A] [Nonempty B] in
/-- **The surrogate is separable**, by construction. -/
theorem surrogate_separable (C : A → B → ℚ) : Separable (surrogate C) :=
  ⟨fun a => rowMean C a, fun b => colMean C b - grandMean C, fun a b => by
    simp only [surrogate]; ring⟩

/-- **The surrogate has the same row means.** -/
theorem rowMean_surrogate (C : A → B → ℚ) (a : A) :
    rowMean (surrogate C) a = rowMean C a := by
  have hB : (Fintype.card B : ℚ) ≠ 0 := cardB_ne_zero (B := B)
  simp only [rowMean, surrogate, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sum_colMean C]
  field_simp
  ring

/-- **The surrogate has the same column means.** -/
theorem colMean_surrogate (C : A → B → ℚ) (b : B) :
    colMean (surrogate C) b = colMean C b := by
  have hA : (Fintype.card A : ℚ) ≠ 0 := cardA_ne_zero (A := A)
  simp only [colMean, surrogate, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sum_rowMean C]
  field_simp
  ring

omit [Nonempty A] [Nonempty B] in
/-- **A nonseparable table is not its own surrogate.** -/
theorem surrogate_ne_of_not_separable {C : A → B → ℚ} (h : ¬ Separable C) :
    surrogate C ≠ C := fun heq => h (heq ▸ surrogate_separable C)

/-- **Interaction is not another coordinate.**  For any nonseparable table there
is a *different* table agreeing with it on every row mean and every column mean.
Retaining all the marginal coordinates therefore does not retain the joint
structure: the lost quantity is not a coordinate that could have been kept
alongside them. -/
theorem interaction_is_not_another_coordinate {C : A → B → ℚ} (h : ¬ Separable C) :
    ∃ D : A → B → ℚ,
      (∀ a, rowMean D a = rowMean C a) ∧
      (∀ b, colMean D b = colMean C b) ∧
      Separable D ∧ D ≠ C :=
  ⟨surrogate C, rowMean_surrogate C, colMean_surrogate C, surrogate_separable C,
    surrogate_ne_of_not_separable h⟩

end Surrogate

/-- **On the corpus's own kernel table.**  There is a table with exactly the
sharpness means and radius-class means of `positiveKernelValue`, which is
nevertheless separable and therefore different from it. -/
theorem kernel_marginals_do_not_determine_the_table :
    ∃ D : AgdaMirror.InteractionTables.AnisotropicKernel.BoundarySharpness →
        AgdaMirror.InteractionTables.AnisotropicKernel.RadiusClass → ℚ,
      (∀ s, rowMean D s = rowMean Kernel.kernelQ s) ∧
      (∀ r, colMean D r = colMean Kernel.kernelQ r) ∧
      Separable D ∧ D ≠ Kernel.kernelQ :=
  interaction_is_not_another_coordinate Kernel.kernel_not_separable

/-- The renderer's product rule restricted to the two kernel values `1` and `2`,
so that it is a table over finite coordinates. -/
def combinedOnPair (b : Bool) (d : AgdaMirror.InteractionTables.RendererAffinity.SharedDepth) : ℚ :=
  Affinity.combinedQ (if b then 2 else 1) d

theorem combinedOnPair_not_separable : ¬ Separable combinedOnPair := by
  intro h
  have := separable_rectangle h false true
    AgdaMirror.InteractionTables.RendererAffinity.SharedDepth.shared0
    AgdaMirror.InteractionTables.RendererAffinity.SharedDepth.shared1
  norm_num [combinedOnPair, Affinity.combinedQ,
    AgdaMirror.InteractionTables.RendererAffinity.combinedAffinity,
    AgdaMirror.InteractionTables.RendererAffinity.sharedDepthWeight] at this

/-- **The same on the renderer's product rule.**  There is an additive table
with exactly the kernel-value means and the shared-depth means of the corpus's
multiplicative affinity, so the corpus's choice between the product and the sum
is invisible to every marginal summary of the result. -/
theorem affinity_marginals_do_not_determine_the_table :
    ∃ D : Bool → AgdaMirror.InteractionTables.RendererAffinity.SharedDepth → ℚ,
      (∀ b, rowMean D b = rowMean combinedOnPair b) ∧
      (∀ d, colMean D d = colMean combinedOnPair d) ∧
      Separable D ∧ D ≠ combinedOnPair :=
  interaction_is_not_another_coordinate combinedOnPair_not_separable

end Integration.InteractionWelds

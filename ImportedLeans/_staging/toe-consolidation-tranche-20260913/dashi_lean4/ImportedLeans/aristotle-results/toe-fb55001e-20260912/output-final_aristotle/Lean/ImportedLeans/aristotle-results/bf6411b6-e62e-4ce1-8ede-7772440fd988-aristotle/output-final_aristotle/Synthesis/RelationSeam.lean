import Mathlib
import AgdaMirror.LoomRelationAlgebra
import AgdaMirror.StageQuotient
import Synthesis.DialecticTone

/-!
# Synthesis layer 1': relation classifiers and the seam of the fourfold tone

Two pieces of supplied material that had not yet been connected to the spine are
treated here, both instances of one shared primitive: **when does one classifier
factor through another?**

* `AgdaMirror.Loom` (mirror of `LoomRelationAlgebra.agda`) supplies a finite
  relation-type enumeration with two total classifiers, `relationRootFor` (coarse
  root) and `bucketFor` (display bucket), a typed-relation record whose declared
  root and bucket are *proved* to be the derived ones, and a Boolean flag
  `separatesRelationFromPromotion` asserting that promotion is not implied by
  bucket assignment.
* `AgdaMirror.StageQuotient` (mirror of `DASHI/Algebra/StageQuotient.agda`)
  supplies the tone quotient `stageTone : Stage → TriTruth` together with a
  single concrete failure of rotation equivariance at `overflow`.

What is proved here (all new):

* **Shared primitive.** `factors_through_iff`: a map `f` factors through a map
  `g` on the same source exactly when `g` separates no less than `f` does.  This
  is the criterion both layers below are read through.
* **The bucket display refines the root.**  `relationRootFor` factors through
  `bucketFor` by an explicit table, and the converse fails: two relation types
  with root `supports` have different buckets.  So the classifier pair is a
  genuine two-step refinement, not two independent labels.
* **The typed-relation record is a fibre.**  Its proof fields carry no
  information: `LoomTypedRelation` is equivalent to
  `type × evidence × promotion × note`.  Consequently the promotion state is
  *unconstrained* by the relation type, the root, the bucket and the evidence
  status — the Boolean honesty flag of the source becomes a theorem
  (`promotion_not_determined_by_bucket`), not a flag.
* **The seam is unavoidable but minimal.**  For any `f : Stage → TriTruth` the
  seam set (stages where equivariance fails) is nonempty, and the supplied
  `stageTone` attains the minimum: its seam is exactly `{overflow}`.  Over the
  sixfold carrier the corresponding seam of `stage6Tone` is empty.  This is the
  quantitative form of the layer-1 obstruction `3 ∤ 4`, `3 ∣ 6`.

Boundary: everything here is about finite classifiers and finite carriers.  No
legal, semantic or physical reading of "relation", "promotion" or "dialectic" is
asserted; the names are the source material's.
-/

namespace Synthesis.RelationSeam

open AgdaMirror.Base369
open AgdaMirror.DASHIAlgebra (Stage6 next6)
open AgdaMirror.LogicTlurey (Stage next stageTone)
open AgdaMirror.Loom
open Synthesis.DialecticTone

/-! ## The shared primitive: factorisation of one classifier through another -/

/-- **Factorisation criterion.**  A classifier `f : A → C` factors through
`g : A → B` exactly when `g` never identifies two points that `f` separates. -/
theorem factors_through_iff {A B C : Type*} [Nonempty C] (f : A → C) (g : A → B) :
    (∃ h : B → C, ∀ a, f a = h (g a)) ↔ ∀ a₁ a₂, g a₁ = g a₂ → f a₁ = f a₂ := by
  classical
  constructor
  · rintro ⟨h, hh⟩ a₁ a₂ hg
    rw [hh a₁, hh a₂, hg]
  · intro hsep
    refine ⟨fun b => if hb : ∃ a, g a = b then f hb.choose else Classical.arbitrary C, ?_⟩
    intro a
    have hb : ∃ a', g a' = g a := ⟨a, rfl⟩
    show f a = if hb' : ∃ a', g a' = g a then f hb'.choose else Classical.arbitrary C
    rw [dif_pos hb]
    exact hsep a hb.choose hb.choose_spec.symm

/-! ## The Loom relation algebra: bucket refines root -/

/-- The display bucket determines the coarse root, by this explicit table. -/
def rootOfBucket : LoomBucket → LoomRelationRoot
  | .supportedBucket => .supports
  | .disputedBucket => .invalidates
  | .partialSupportBucket => .supports
  | .adjacentEventBucket => .nonResolving
  | .substitutionBucket => .nonResolving
  | .nonSubstantiveResponseBucket => .nonResolving
  | .missingBucket => .unanswered

/-- **The root classifier factors through the bucket classifier.** -/
theorem relationRootFor_eq_rootOfBucket (t : LoomRelationType) :
    relationRootFor t = rootOfBucket (bucketFor t) := by
  cases t <;> rfl

/-- Factorisation in the form of the shared criterion. -/
theorem root_factors_through_bucket :
    ∃ h : LoomBucket → LoomRelationRoot, ∀ t, relationRootFor t = h (bucketFor t) :=
  ⟨rootOfBucket, relationRootFor_eq_rootOfBucket⟩

instance : Nonempty LoomRelationRoot := ⟨.supports⟩
instance : Nonempty LoomBucket := ⟨.supportedBucket⟩

/-- Equivalently: the bucket separates at least as finely as the root. -/
theorem bucket_separates_root (t₁ t₂ : LoomRelationType) :
    bucketFor t₁ = bucketFor t₂ → relationRootFor t₁ = relationRootFor t₂ :=
  ((factors_through_iff relationRootFor bucketFor).1 root_factors_through_bucket) t₁ t₂

/-- **The refinement is strict**: the bucket does *not* factor through the root,
because `exactSupport` and `partialOverlap` share the root `supports` while
landing in different buckets. -/
theorem bucket_not_factor_through_root :
    ¬ ∃ h : LoomRelationRoot → LoomBucket, ∀ t, bucketFor t = h (relationRootFor t) := by
  rintro ⟨h, hh⟩
  have h1 : LoomBucket.supportedBucket = h .supports := hh .exactSupport
  have h2 : LoomBucket.partialSupportBucket = h .supports := hh .partialOverlap
  rw [← h1] at h2
  exact absurd h2 (by decide)

instance : Fintype LoomRelationType :=
  ⟨{.exactSupport, .equivalentSupport, .explicitDispute, .implicitDispute,
    .partialOverlap, .adjacentEvent, .substitution, .proceduralNonanswer, .unrelated},
   fun t => by cases t <;> decide⟩

/-- The fibres of the root classifier: three relation types support, two
invalidate, three are non-resolving and one is unanswered. -/
theorem root_fibre_cards :
    (Finset.univ.filter (fun t => relationRootFor t = .supports)).card = 3 ∧
    (Finset.univ.filter (fun t => relationRootFor t = .invalidates)).card = 2 ∧
    (Finset.univ.filter (fun t => relationRootFor t = .nonResolving)).card = 3 ∧
    (Finset.univ.filter (fun t => relationRootFor t = .unanswered)).card = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-! ## The typed-relation record is a fibre over the relation type -/

/-- **The proof fields carry no information.**  A `LoomTypedRelation` is exactly a
relation type together with an evidence status, a promotion state and a note; its
root and bucket are forced. -/
def typedRelationEquiv :
    LoomTypedRelation ≃
      (LoomRelationType × LoomEvidenceStatus × LoomPromotionState × String) where
  toFun R := (R.relationType, R.evidenceStatus, R.promotionState, R.relationNote)
  invFun x :=
    { relationType := x.1
      relationRoot := relationRootFor x.1
      relationRootIsDerived := rfl
      bucket := bucketFor x.1
      bucketIsDerived := rfl
      evidenceStatus := x.2.1
      promotionState := x.2.2.1
      relationNote := x.2.2.2 }
  left_inv := by
    rintro ⟨t, r, hr, b, hb, e, p, n⟩
    subst hr; subst hb; rfl
  right_inv _ := rfl

/-- Every combination of relation type, evidence status and promotion state is
realised by some typed relation. -/
theorem promotion_unconstrained (t : LoomRelationType) (e : LoomEvidenceStatus)
    (p : LoomPromotionState) :
    ∃ R : LoomTypedRelation,
      R.relationType = t ∧ R.evidenceStatus = e ∧ R.promotionState = p :=
  ⟨typedRelationEquiv.symm (t, e, p, ""), rfl, rfl, rfl⟩

/-- **The honesty flag becomes a theorem.**  No function of the display bucket
determines the promotion state: bucket assignment never implies promotion. -/
theorem promotion_not_determined_by_bucket :
    ¬ ∃ h : LoomBucket → LoomPromotionState,
      ∀ R : LoomTypedRelation, R.promotionState = h R.bucket := by
  rintro ⟨h, hh⟩
  obtain ⟨R₁, _, _, hp₁⟩ :=
    promotion_unconstrained .exactSupport .witnessed .promotionFalse
  obtain ⟨R₂, ht₂, _, hp₂⟩ :=
    promotion_unconstrained .exactSupport .witnessed .promotedBySeparateContract
  have hb₁ : R₁.bucket = bucketFor .exactSupport := by
    rw [R₁.bucketIsDerived]; congr 1
  have hb₂ : R₂.bucket = bucketFor .exactSupport := by
    rw [R₂.bucketIsDerived, ht₂]
  have : LoomPromotionState.promotionFalse = .promotedBySeparateContract := by
    rw [← hp₁, ← hp₂, hh R₁, hh R₂, hb₁, hb₂]
  exact absurd this (by decide)

/-- Likewise no function of the relation type determines promotion, so the
separation of relation typing from promotion is complete. -/
theorem promotion_not_determined_by_type :
    ¬ ∃ h : LoomRelationType → LoomPromotionState,
      ∀ R : LoomTypedRelation, R.promotionState = h R.relationType := by
  rintro ⟨h, hh⟩
  obtain ⟨R₁, ht₁, _, hp₁⟩ :=
    promotion_unconstrained .exactSupport .witnessed .promotionFalse
  obtain ⟨R₂, ht₂, _, hp₂⟩ :=
    promotion_unconstrained .exactSupport .witnessed .promotedBySeparateContract
  have : LoomPromotionState.promotionFalse = .promotedBySeparateContract := by
    rw [← hp₁, ← hp₂, hh R₁, hh R₂, ht₁, ht₂]
  exact absurd this (by decide)

/-- The canonical algebra's honesty flag agrees with the theorem above: it is
`true`, and it is now backed by `promotion_not_determined_by_bucket`. -/
theorem canonical_flag_is_backed :
    canonicalLoomRelationAlgebra.separatesRelationFromPromotion = true ∧
      ¬ ∃ h : LoomBucket → LoomPromotionState,
        ∀ R : LoomTypedRelation, R.promotionState = h R.bucket :=
  ⟨rfl, promotion_not_determined_by_bucket⟩

/-! ## The seam of the fourfold tone -/

/-- The seam of a fourfold tone: the stages at which rotation equivariance
fails. -/
def seam (f : Stage → TriTruth) : Finset Stage :=
  Finset.univ.filter (fun s => f (next s) ≠ rotateTri (f s))

/-- The seam of a sixfold tone. -/
def seam6 (f : Stage6 → TriTruth) : Finset Stage6 :=
  Finset.univ.filter (fun s => f (next6 s) ≠ rotateTri (f s))

/-- **Every fourfold tone has a seam.** -/
theorem seam_nonempty (f : Stage → TriTruth) : (seam f).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  refine no_equivariant_fourfold_tone ⟨f, fun s => ?_⟩
  by_contra hs
  have : s ∈ seam f := by simp [seam, hs]
  rw [hempty] at this
  exact absurd this (Finset.notMem_empty s)

/-- Cardinal form: at least one stage is a seam. -/
theorem one_le_seam_card (f : Stage → TriTruth) : 1 ≤ (seam f).card :=
  Finset.card_pos.2 (seam_nonempty f)

/-- **The supplied tone attains the minimum**: its seam is the single stage
`overflow`, exactly the seam recorded in the source material. -/
theorem stageTone_seam : seam stageTone = {Stage.overflow} := by decide

/-- Minimality, stated together: the supplied tone has a one-element seam and no
fourfold tone has a smaller one. -/
theorem stageTone_seam_minimal :
    (seam stageTone).card = 1 ∧ ∀ f : Stage → TriTruth, (seam stageTone).card ≤ (seam f).card :=
  ⟨by decide, fun f => by rw [show (seam stageTone).card = 1 from by decide]; exact one_le_seam_card f⟩

/-- The supplied seam surface of `StageQuotient` is exactly this seam: its
quotient is `stageTone`, and its recorded failure point is the seam element. -/
theorem supplied_seam_surface :
    AgdaMirror.StageQuotient.stageQuotientSeamSurface.quotient = stageTone ∧
      Stage.overflow ∈ seam stageTone :=
  ⟨rfl, by decide⟩

/-- **The sixfold carrier has no seam**: the descent tone of layer 1 is
equivariant everywhere. -/
theorem stage6Tone_seam_empty : seam6 stage6Tone = ∅ := by decide

/-- The layer-1 obstruction in quantitative form: the fourfold carrier admits no
seamless tone while the sixfold carrier does, and the fourfold defect is exactly
one stage. -/
theorem seam_dichotomy :
    (∀ f : Stage → TriTruth, (seam f).Nonempty) ∧
      seam6 stage6Tone = ∅ ∧ (seam stageTone).card = 1 :=
  ⟨seam_nonempty, stage6Tone_seam_empty, by decide⟩

end Synthesis.RelationSeam

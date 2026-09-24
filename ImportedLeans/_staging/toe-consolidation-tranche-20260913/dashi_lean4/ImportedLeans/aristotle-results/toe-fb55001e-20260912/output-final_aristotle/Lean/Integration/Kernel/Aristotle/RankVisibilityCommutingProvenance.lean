import Integration.Kernel.Welds.CommutingProvenanceSquare
import RequestProject.Ranks

/-!
# Aristotle instantiation: rank, truthy visibility, and the commuting square

The weld `Integration.Kernel.Welds.CommutingProvenanceSquare` insists that a
claim of the form "this coarse reading is a projection of the fine record" must
carry the square `π ∘ f = g ∘ π`, and proves that agreement along an observed
trajectory is strictly weaker.  This file instantiates the distinction on the
Wikidata rank semantics of `RequestProject.Ranks`, where the two coordinates
that are routinely confused are

* `statementRank ∈ {preferred, normal, deprecated}` — a property of the
  statement itself, and
* `statementVisibility ∈ {truthy, nonTruthy, unresolved}` — a property of the
  statement **relative to its whole `(Q,P)` sibling group**.

## What is proved

* `visibility` — the visibility reading, defined from the archive's `isTruthy`.
* **`rank_does_not_determine_visibility`** — the non-locality: one and the same
  normal-rank statement is truthy in one world and non-truthy in another, the
  difference being a *sibling*, not the statement.  So the rank coordinate is
  not a projection of the visibility coordinate.
* **`no_visibility_step_commutes`** — the negative square: for the pipeline step
  "retract the most recently added statement" there is **no** coarse step on
  visibilities making the diagram commute; two worlds with the same visibility
  reading are driven to different readings by the same step.
* **`family_projection_commutes`** — the positive square, and the reason the
  earlier fibre owner is well posed: the `(Q,P)` **family** reading *is* a
  projection of the claim set for the append step, for every claim and every
  world, hence (`family_projection_transports`) it stays correct after any
  number of appends.
* `visibility_is_a_function_of_the_family` — visibility, unlike rank, is
  recoverable from the family reading, which is exactly why the family is the
  right coarse state.

**Claim boundary.**  The worlds are finite claim sets defined here; `isTruthy`
and `bestRankNat` are the archive's.  Nothing is claimed about live Wikidata
content.
-/

namespace Integration.Kernel.Aristotle.RankVisibilityCommutingProvenance

open Integration.Kernel

/-! ## §1 Rank and visibility -/

/-- The visibility of a statement to a default (truthy) query. -/
inductive Visibility where
  /-- The statement is returned by a default query. -/
  | truthy
  /-- The statement is present and not returned. -/
  | nonTruthy
  /-- The statement is not in the world under consideration. -/
  | unresolved
deriving DecidableEq, Repr, Inhabited

/-- The visibility reading of a statement in a claim set, defined from the
archive's `isTruthy`. -/
def visibility (cs : Wikidata.Claim.Set) (c : Wikidata.Claim) : Visibility :=
  if c ∈ cs then
    if Wikidata.Claim.isTruthy cs c then Visibility.truthy else Visibility.nonTruthy
  else Visibility.unresolved

/-- Berlin, as a label. -/
def subj : Wikidata.Qid := .wd "Q64"
/-- Population, as a label. -/
def popP : Wikidata.Pid := .wd "P1082"
/-- Country, as a label. -/
def countryP : Wikidata.Pid := .wd "P17"

/-- The statement whose visibility is tracked: a normal-rank population value. -/
def tracked : Wikidata.Claim :=
  { subject := subj, pid := popP, value := .quantity 3645000 }

/-- A preferred sibling in the same family. -/
def preferredSibling : Wikidata.Claim :=
  { subject := subj, pid := popP, value := .quantity 3769000, rank := .preferred }

/-- An unrelated statement, in a different family. -/
def unrelated : Wikidata.Claim :=
  { subject := subj, pid := countryP, value := .item (.wd "Q183") }

/-- **The rank of a statement does not determine its visibility.**  The tracked
statement has rank `normal` in both worlds; it is truthy in the first and
non-truthy in the second, and the difference is a sibling of the family. -/
theorem rank_does_not_determine_visibility :
    tracked.rank = Wikidata.Rank.normal ∧
    visibility [tracked] tracked = Visibility.truthy ∧
    visibility [preferredSibling, tracked] tracked = Visibility.nonTruthy := by
  refine ⟨rfl, by decide, by decide⟩

/-- Consequently no function of the statement alone reports its visibility. -/
theorem visibility_is_not_a_function_of_the_statement :
    ¬ ∃ f : Wikidata.Claim → Visibility,
        ∀ cs c, c ∈ cs → visibility cs c = f c := by
  rintro ⟨f, hf⟩
  have h₁ := hf [tracked] tracked (by decide)
  have h₂ := hf [preferredSibling, tracked] tracked (by decide)
  rw [rank_does_not_determine_visibility.2.1] at h₁
  rw [rank_does_not_determine_visibility.2.2] at h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-! ## §2 The negative square -/

/-- The pipeline step: retract the most recently added statement. -/
def retractStep (cs : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  match cs with
  | [] => []
  | _ :: t => t

/-- The coarse reading: the visibility of the tracked statement. -/
def visibilityReport (cs : Wikidata.Claim.Set) : Visibility := visibility cs tracked

/-- A world in which the preferred sibling was added last. -/
def worldOne : Wikidata.Claim.Set := [preferredSibling, tracked]

/-- A world in which an unrelated statement was added last, over the same
preferred sibling. -/
def worldTwo : Wikidata.Claim.Set := [unrelated, preferredSibling, tracked]

theorem reports_agree_now : visibilityReport worldOne = visibilityReport worldTwo := by decide

theorem reports_disagree_after_one_step :
    visibilityReport (retractStep worldOne) ≠ visibilityReport (retractStep worldTwo) := by
  decide

/-- **No coarse step on visibilities commutes with the pipeline.**  Two worlds
with the same visibility reading are taken by the same step to different
readings, so the visibility reading is not a projection of the claim set for
this step, however plausible the agreement looks at the moment of
observation. -/
theorem no_visibility_step_commutes :
    ¬ ∃ g : Visibility → Visibility,
        Welds.CommutingProvenanceSquare.IsProjection visibilityReport retractStep g := by
  rintro ⟨g, hg⟩
  have h₁ := hg worldOne
  have h₂ := hg worldTwo
  rw [reports_agree_now] at h₁
  exact reports_disagree_after_one_step (h₁.trans h₂.symm)

/-! ## §3 The positive square: the family reading is a projection -/

/-- The coarse state: the `(Q,P)` statement family. -/
def familyOf (s : Wikidata.Qid) (p : Wikidata.Pid)
    (cs : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  Wikidata.Claim.group cs s p

/-- The fine step: a new statement arrives. -/
def appendClaim (c0 : Wikidata.Claim) (cs : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  c0 :: cs

/-- The coarse step: the new statement is recorded in the family exactly when it
belongs to it. -/
def coarseAppend (c0 : Wikidata.Claim) (s : Wikidata.Qid) (p : Wikidata.Pid)
    (g : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  if c0.subject = s ∧ c0.pid = p then c0 :: g else g

/-- **The family reading is a genuine projection.**  The square commutes for
every incoming statement and every world — not merely on an observed
trajectory. -/
theorem family_projection_commutes (c0 : Wikidata.Claim) (s : Wikidata.Qid) (p : Wikidata.Pid) :
    Welds.CommutingProvenanceSquare.IsProjection (familyOf s p) (appendClaim c0)
      (coarseAppend c0 s p) := by
  intro cs
  by_cases h : c0.subject = s ∧ c0.pid = p <;>
    simp [familyOf, Wikidata.Claim.group, appendClaim, coarseAppend, h]

/-- Hence the family reading stays correct after any number of appends. -/
theorem family_projection_transports (c0 : Wikidata.Claim) (s : Wikidata.Qid) (p : Wikidata.Pid)
    (n : ℕ) (cs : Wikidata.Claim.Set) :
    familyOf s p ((appendClaim c0)^[n] cs) = (coarseAppend c0 s p)^[n] (familyOf s p cs) :=
  Welds.CommutingProvenanceSquare.projection_iterate (family_projection_commutes c0 s p) n cs

/-- And the coarse state deserves its name: visibility, which the statement's
own rank does not determine, *is* determined by the family reading, for every
statement of the family. -/
theorem visibility_is_a_function_of_the_family {cs cs' : Wikidata.Claim.Set}
    {s : Wikidata.Qid} {p : Wikidata.Pid} {c : Wikidata.Claim}
    (hfam : familyOf s p cs = familyOf s p cs')
    (hc : c ∈ Wikidata.Claim.group cs s p) (hc' : c ∈ Wikidata.Claim.group cs' s p) :
    visibility cs c = visibility cs' c := by
  rcases Wikidata.Claim.mem_group_iff.1 hc with ⟨hmem, hsub, hpid⟩
  rcases Wikidata.Claim.mem_group_iff.1 hc' with ⟨hmem', -, -⟩
  have hbest : Wikidata.Claim.bestRankNat cs c.subject c.pid
      = Wikidata.Claim.bestRankNat cs' c.subject c.pid := by
    rw [hsub, hpid]
    unfold Wikidata.Claim.bestRankNat
    rw [show Wikidata.Claim.group cs s p = Wikidata.Claim.group cs' s p from hfam]
  simp [visibility, hmem, hmem', Wikidata.Claim.isTruthy, hbest]

end Integration.Kernel.Aristotle.RankVisibilityCommutingProvenance

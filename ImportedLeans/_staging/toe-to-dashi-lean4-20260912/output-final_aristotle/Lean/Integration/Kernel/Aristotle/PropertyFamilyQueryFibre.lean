import Integration.Kernel.PartialIdentification
import RequestProject.Ranks

/-!
# Aristotle instantiation: the compatible fibre of a Wikidata property family

The generic owner `Integration.Kernel.PartialIdentification` says that the
positive content of a partial observation is its *compatible fibre*, and that a
non-singleton fibre is not by itself an epistemic failure: a consumer can be
constant on it.  Until now that statement had only label-type instances.  This
file instantiates it on the Wikidata statement semantics of the archive module
`RequestProject.Ranks` (integrated in this project under
`Lean/DASHI/output-final_aristotle`), where the consumer is the genuine truthy
query of the Wikidata data model.

The hidden state is a whole claim set (an item, or a fragment of the graph).
The observation is the **statement family** of one subject–property pair,

  `F(Q,P) = Wikidata.Claim.group cs Q P = {s | subject s = Q ∧ property s = P}`,

and the consumer is `Wikidata.Claim.truthyValues cs Q P`, the values a default
Wikidata query returns.

## What is proved

* `truthyValues_congr_of_group_eq` — **the consumer factors through the family**:
  two claim sets with the same `(Q,P)` family return the same truthy values,
  whatever else they contain.  This is the load-bearing lemma; it is a statement
  about the archive's real `isTruthy`/`bestRankNat` definitions, not about a
  label type.
* `familyObs`, `compatible_family_eq` — the observation map into
  `PartialIdentification.compatible`.
* `family_fibre_not_singleton` / `not_pointIdentified_family` — observing the
  family does **not** identify the item: two distinct worlds sit in one fibre.
* **`consumer_closed_on_nonsingleton_family_fibre`** — nevertheless the truthy
  consumer is constant on that fibre with the determinate answer
  `[Value.quantity 3645000]`.  Concretely:
  *whole item unresolved ∧ the specific `(Q,P)` consumer closed*.
* **`uncovered_family_does_not_close_the_consumer`** — the converse discipline:
  if the family is only partially observed, an unseen *preferred* sibling
  changes the answer, so a truthy/non-truthy conclusion is not licensed.  The
  two worlds agree on every observed (normal-rank) statement and disagree on the
  consumer.
* `coverage_closes_or_reopens` — the two results side by side: coverage of the
  family is what the consumer needs, and item completeness is not.

**Claim boundary.**  `worldA`, `worldB`, `partialWorld`, `coveredWorld` are
stylised finite claim sets defined in this file.  Nothing here asserts anything
about the live Wikidata graph; the Q/P identifiers are labels.  The semantics of
`truthy` is the archive's, and the theorems are about these fixtures plus the
generic congruence lemma, which is quantified over all claim sets.
-/

namespace Integration.Kernel.Aristotle.PropertyFamilyQueryFibre

open Integration.Kernel

/-! ## §1 The consumer factors through the statement family -/

/-- The best rank of a subject–property pair is computed from the family alone. -/
theorem bestRankNat_congr_of_group_eq {cs cs' : Wikidata.Claim.Set}
    {s : Wikidata.Qid} {p : Wikidata.Pid} (h : Wikidata.Claim.group cs s p = Wikidata.Claim.group cs' s p) :
    Wikidata.Claim.bestRankNat cs s p = Wikidata.Claim.bestRankNat cs' s p := by
  unfold Wikidata.Claim.bestRankNat
  rw [h]

/-- **The truthy consumer factors through the `(Q,P)` family.**  Two claim sets
whose statements for the pair `(s,p)` coincide return the same truthy values for
`(s,p)`, no matter how much else they disagree about. -/
theorem truthyValues_congr_of_group_eq {cs cs' : Wikidata.Claim.Set}
    {s : Wikidata.Qid} {p : Wikidata.Pid} (h : Wikidata.Claim.group cs s p = Wikidata.Claim.group cs' s p) :
    Wikidata.Claim.truthyValues cs s p = Wikidata.Claim.truthyValues cs' s p := by
  unfold Wikidata.Claim.truthyValues
  have hfilter :
      (Wikidata.Claim.group cs s p).filter
          (fun c => decide (Wikidata.Claim.isTruthy cs c))
        = (Wikidata.Claim.group cs' s p).filter
          (fun c => decide (Wikidata.Claim.isTruthy cs' c)) := by
    rw [h]
    refine List.filter_congr ?_
    intro c hc
    rcases (Wikidata.Claim.mem_group_iff.1 hc) with ⟨-, hsub, hpid⟩
    have hbest : Wikidata.Claim.bestRankNat cs c.subject c.pid
        = Wikidata.Claim.bestRankNat cs' c.subject c.pid := by
      rw [hsub, hpid]
      exact bestRankNat_congr_of_group_eq h
    simp [Wikidata.Claim.isTruthy, hbest]
  rw [hfilter]

/-! ## §2 The fixtures -/

/-- Berlin, as a label. -/
def subj : Wikidata.Qid := .wd "Q64"

/-- Population, as a label. -/
def popP : Wikidata.Pid := .wd "P1082"

/-- Country, as a label. -/
def countryP : Wikidata.Pid := .wd "P17"

/-- A world: one population statement and one country statement. -/
def worldA : Wikidata.Claim.Set :=
  [ { subject := subj, pid := popP, value := .quantity 3645000 },
    { subject := subj, pid := countryP, value := .item (.wd "Q183") } ]

/-- A second world with the *same* population family and a different, and here
additionally deprecated, country statement. -/
def worldB : Wikidata.Claim.Set :=
  [ { subject := subj, pid := popP, value := .quantity 3645000 },
    { subject := subj, pid := countryP, value := .item (.wd "Q16957"),
      rank := .deprecated } ]

/-- The observation available to a consumer that inspects one property family. -/
def familyObs (s : Wikidata.Qid) (p : Wikidata.Pid) (cs : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  Wikidata.Claim.group cs s p

theorem worldA_ne_worldB : worldA ≠ worldB := by decide

theorem familyObs_worldA_eq_worldB :
    familyObs subj popP worldA = familyObs subj popP worldB := by decide

/-- The two worlds sit in one compatible fibre of the family observation. -/
theorem compatible_family_eq :
    worldB ∈ PartialIdentification.compatible (familyObs subj popP)
      (familyObs subj popP worldA) :=
  familyObs_worldA_eq_worldB.symm

/-- **Observing the family does not identify the item.** -/
theorem not_pointIdentified_family :
    ¬ PartialIdentification.PointIdentified (familyObs subj popP)
        (familyObs subj popP worldA) :=
  PartialIdentification.not_pointIdentified_of_collision
    familyObs_worldA_eq_worldB worldA_ne_worldB

/-- The fibre really has two distinct members. -/
theorem family_fibre_not_singleton :
    ∃ x y : Wikidata.Claim.Set,
      x ∈ PartialIdentification.compatible (familyObs subj popP)
        (familyObs subj popP worldA) ∧
      y ∈ PartialIdentification.compatible (familyObs subj popP)
        (familyObs subj popP worldA) ∧
      x ≠ y :=
  ⟨worldA, worldB, rfl, familyObs_worldA_eq_worldB.symm, worldA_ne_worldB⟩

/-! ## §3 Closure of the consumer on a non-singleton fibre -/

/-- The truthy answer of the fixture. -/
theorem worldA_answer :
    Wikidata.Claim.truthyValues worldA subj popP = [Wikidata.Value.quantity 3645000] := by
  decide

/-- **Whole item unresolved, specific `(Q,P)` consumer closed.**  Every world
compatible with the observed population family returns the same truthy value,
although the fibre is not a singleton and the item as a whole is not
identified. -/
theorem consumer_closed_on_nonsingleton_family_fibre :
    (¬ PartialIdentification.PointIdentified (familyObs subj popP)
        (familyObs subj popP worldA)) ∧
    ∀ cs ∈ PartialIdentification.compatible (familyObs subj popP)
        (familyObs subj popP worldA),
      Wikidata.Claim.truthyValues cs subj popP = [Wikidata.Value.quantity 3645000] := by
  refine ⟨not_pointIdentified_family, ?_⟩
  intro cs hcs
  have h : Wikidata.Claim.group cs subj popP = Wikidata.Claim.group worldA subj popP := hcs
  rw [truthyValues_congr_of_group_eq h]
  exact worldA_answer

/-! ## §4 Uncovered family: the answer is not licensed -/

/-- What has actually been seen: the normal-rank statements of the family. -/
def observedNormal (s : Wikidata.Qid) (p : Wikidata.Pid) (cs : Wikidata.Claim.Set) : Wikidata.Claim.Set :=
  (Wikidata.Claim.group cs s p).filter (fun c => c.rank == Wikidata.Rank.normal)

/-- A world in which the only population statement is the observed normal one. -/
def partialWorld : Wikidata.Claim.Set :=
  [ { subject := subj, pid := popP, value := .quantity 3645000 } ]

/-- A world with the same observed normal statement plus an unobserved
*preferred* sibling in the same family. -/
def coveredWorld : Wikidata.Claim.Set :=
  [ { subject := subj, pid := popP, value := .quantity 3645000 },
    { subject := subj, pid := popP, value := .quantity 3769000, rank := .preferred } ]

theorem observedNormal_agree :
    observedNormal subj popP partialWorld = observedNormal subj popP coveredWorld := by decide

/-- **An uncovered family does not close the consumer.**  The two worlds agree
on everything observed and disagree on the truthy answer, so no
truthy/non-truthy conclusion is licensed before the family is covered. -/
theorem uncovered_family_does_not_close_the_consumer :
    observedNormal subj popP partialWorld = observedNormal subj popP coveredWorld ∧
    Wikidata.Claim.truthyValues partialWorld subj popP
      ≠ Wikidata.Claim.truthyValues coveredWorld subj popP := by
  refine ⟨observedNormal_agree, ?_⟩
  decide

/-- The two halves side by side: coverage of the family is what the consumer
needs, and identification of the item is not. -/
theorem coverage_closes_or_reopens :
    (∀ cs ∈ PartialIdentification.compatible (familyObs subj popP)
        (familyObs subj popP worldA),
      Wikidata.Claim.truthyValues cs subj popP = [Wikidata.Value.quantity 3645000]) ∧
    (¬ PartialIdentification.PointIdentified (familyObs subj popP)
        (familyObs subj popP worldA)) ∧
    (∃ x y : Wikidata.Claim.Set,
      observedNormal subj popP x = observedNormal subj popP y ∧
      Wikidata.Claim.truthyValues x subj popP ≠ Wikidata.Claim.truthyValues y subj popP) :=
  ⟨consumer_closed_on_nonsingleton_family_fibre.2,
   not_pointIdentified_family,
   ⟨partialWorld, coveredWorld, uncovered_family_does_not_close_the_consumer.1,
     uncovered_family_does_not_close_the_consumer.2⟩⟩

end Integration.Kernel.Aristotle.PropertyFamilyQueryFibre

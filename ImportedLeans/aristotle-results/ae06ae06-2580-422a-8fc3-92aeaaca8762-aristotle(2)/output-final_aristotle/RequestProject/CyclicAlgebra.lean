import RequestProject.ProgramAlgebra
import RequestProject.PeriodicityReport

/-!
# The cyclic part of the corpus, as an element of the transformation algebra

`RequestProject.ProgramAlgebra` proves that the powers of a relation on a finite
carrier are eventually periodic.  This module computes that periodicity exactly
for the part of the downloaded class hierarchy where it is visible: the eleven
items on a `subclass of` cycle and the eleven statements between them.

* `cyclicRel_subset_corpus` — the eleven statements are statements of the corpus,
  read off the four cycles of the defect report;
* `cyclicRel_pow_twelve` and `cyclicRel_pow_ne_id` — the relation is a
  **permutation of order exactly twelve**: twelve steps return every one of the
  eleven items to itself, and no smaller number of steps does;
* `cyclicRel_order_eq_lcm` — twelve is the least common multiple of the four
  component periods 2, 4, 3 and 2, which
  `RequestProject.PeriodicityReport` certifies with phase arguments.

So the transformation algebra of the corpus does carry an exact finite
periodicity, and it is `ZMod 12` on the cyclic part.  It is worth being explicit
about what that is not: it is the least common multiple of four independent
cycle lengths in one dataset, with no proved relation to any periodicity theorem
of algebra or topology.
-/

namespace Wikidata
namespace CyclicAlgebra

open Wikidata.DefectReport Wikidata.RelAlg

/-- The eleven items on a `subclass of` cycle. -/
def cyclicItems : Finset Qid :=
  {Qid.wd "Q82794", Qid.wd "Q3622002", Qid.wd "Q901", Qid.wd "Q1650915",
   Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q379825", Qid.wd "Q5358816",
   Qid.wd "Q36808958", Qid.wd "Q1184244", Qid.wd "Q1456832"}

/-- The eleven `subclass of` statements between them: four disjoint cycles of
lengths 2, 4, 3 and 2. -/
def cyclicRel : Finset (Qid × Qid) :=
  {(Qid.wd "Q82794", Qid.wd "Q3622002"), (Qid.wd "Q3622002", Qid.wd "Q82794"),
   (Qid.wd "Q901", Qid.wd "Q1650915"), (Qid.wd "Q1650915", Qid.wd "Q66666685"),
   (Qid.wd "Q66666685", Qid.wd "Q3400985"), (Qid.wd "Q3400985", Qid.wd "Q901"),
   (Qid.wd "Q379825", Qid.wd "Q5358816"), (Qid.wd "Q5358816", Qid.wd "Q36808958"),
   (Qid.wd "Q36808958", Qid.wd "Q379825"),
   (Qid.wd "Q1184244", Qid.wd "Q1456832"), (Qid.wd "Q1456832", Qid.wd "Q1184244")}

theorem cyclicItems_card : cyclicItems.card = 11 := by decide

theorem cyclicRel_card : cyclicRel.card = 11 := by decide

theorem cyclicRel_subset : cyclicRel ⊆ cyclicItems ×ˢ cyclicItems := by decide

/-- **Every one of the eleven statements is a statement of the corpus**, read off
the four cycles the defect report found. -/
theorem cyclicRel_subset_corpus : ∀ e ∈ cyclicRel, e ∈ corpus.sub := by
  intro e he
  simp only [cyclicRel, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact geographicalArea_cycle.1
  · exact geographicalArea_cycle.2
  · exact scientist_cycle.1
  · exact scientist_cycle.2.1
  · exact scientist_cycle.2.2.1
  · exact scientist_cycle.2.2.2
  · exact element_cycle.1
  · exact element_cycle.2.1
  · exact element_cycle.2.2
  · exact delict_cycle.1
  · exact delict_cycle.2

/-- **Twelve steps return every item to itself.** -/
theorem cyclicRel_pow_twelve : pow cyclicItems cyclicRel 12 = idRel cyclicItems := by
  native_decide

/-- No smaller number of steps does. -/
theorem cyclicRel_pow_ne_idB :
    ((List.range 12).all fun k => k == 0 || (pow cyclicItems cyclicRel k != idRel cyclicItems))
      = true := by native_decide

theorem cyclicRel_pow_ne_id {k : ℕ} (hk : 0 < k) (hlt : k < 12) :
    pow cyclicItems cyclicRel k ≠ idRel cyclicItems := by
  have hmem : k ∈ List.range 12 := List.mem_range.2 hlt
  have := List.all_eq_true.1 cyclicRel_pow_ne_idB k hmem
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with h | h
  · omega
  · exact h

/-- **The cyclic part of the class hierarchy is a permutation of order exactly
twelve.** -/
theorem cyclicRel_order_twelve :
    pow cyclicItems cyclicRel 12 = idRel cyclicItems ∧
      ∀ k, 0 < k → k < 12 → pow cyclicItems cyclicRel k ≠ idRel cyclicItems :=
  ⟨cyclicRel_pow_twelve, fun _ hk hlt => cyclicRel_pow_ne_id hk hlt⟩

/-- Twelve is the least common multiple of the four component periods — 2 for
*region*, 4 for *scientist*, 3 for *element*, 2 for *delict* — each of which is
certified by a phase argument in `RequestProject.PeriodicityReport`. -/
theorem cyclicRel_order_eq_lcm : Nat.lcm (Nat.lcm 2 4) (Nat.lcm 3 2) = 12 := by decide

/-- **The prime fibers of the cyclic part.**  Twelve factors as `2 ^ 2 * 3`, and
the cyclic group of order twelve splits over those two prime powers: the
*scientist* fibre of order four and the *element* fibre of order three.  (The
two components of order two contribute the factor `2 ^ 2` shares with the
*scientist* cycle.) -/
theorem cyclicOrder_factorization : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num

/-- The Chinese-remainder splitting of the phase group of the cyclic part. -/
noncomputable def cyclicPhaseCRT : ZMod 12 ≃+* ZMod 4 × ZMod 3 :=
  ZMod.chineseRemainder (m := 4) (n := 3) (by norm_num)

end CyclicAlgebra
end Wikidata

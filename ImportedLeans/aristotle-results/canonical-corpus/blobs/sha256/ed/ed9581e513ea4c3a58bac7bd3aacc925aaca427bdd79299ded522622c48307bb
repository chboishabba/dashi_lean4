import RequestProject.CorpusFrontier
import RequestProject.Generated.Frontier3
import RequestProject.Generated.Frontier4

/-!
# Closing the frontier: rounds three and four

`RequestProject.CorpusFrontier` asked, of the downloaded corpus, which items it
mentions but says nothing about, and answered the question twice: the corpus had
**144** such items, the download that asks Wikidata about them left **70**, and a
second round left **42**.

This file continues the same loop.  `data/frontier3.wdkb` asks Wikidata about
those 42 items and `data/frontier4.wdkb` about the ones that remain, so the
chain of corpora is

`Core` ⊆ `coreExtended` ⊆ `coreExtended2` ⊆ `coreExtended3` ⊆ `coreExtended4`,

with 588, 749, 847, 889 and 918 items, and with

**144 → 70 → 42 → 18 → 14**

items said nothing about (`Corpus.frontier_sizes`,
`Corpus.frontier_sizes_decreasing`).  Every round is again answered by Wikidata
for all but one item: of the 42 asked in round three exactly `Q16003513` came
back with no `subclass of` and no `instance of` statement
(`Corpus.round_three_leaves_one_root`), and the same in round four
(`Corpus.round_four_leaves_one_root`).  So the frontier does not vanish — each
download declares new items of its own — but it shrinks quickly, and the one
item that survives every round is the same one throughout.

Nothing is lost on the way: `Corpus.coreExtended4_entails_core` and its
companions say that the corpus of round four still derives every statement of
the original corpus and of every one of the four downloads.  These are proved
abstractly, from the general theorems about merging and normalisation, with no
evaluation at all.
-/

namespace Wikidata
namespace Corpus

open Wikidata.Generated

/-! ### Round three -/

/-- The corpus after the third round of downloading. -/
def coreExtended3 : KB := (coreExtended2.merge Frontier3.kb).normalize

/-- It is well formed, so the certified queries apply to it. -/
theorem coreExtended3_wellFormed : coreExtended3.wellFormed = true :=
  KB.normalize_wellFormed (KB.wellFormed_merge coreExtended2_wellFormed Frontier3.kb_wellFormed)

/-- 889 items after the third round. -/
theorem coreExtended3_card : coreExtended3.items.length = 889 := by native_decide

/-- **The frontier shrinks again**: 18 items the corpus of round three says
nothing about, down from 42. -/
theorem coreExtended3_rootless_card : coreExtended3.rootlessL.length = 18 := by native_decide

/-- And again exactly one of the items asked about in the third round came back
with nothing: `Q16003513`. -/
theorem round_three_leaves_one_root :
    (let R := coreExtended3.rootlessL; coreExtended2.rootlessL.filter (fun q => q ∈ R)) =
      [Qid.wd "Q16003513"] := by
  native_decide

/-! ### Round four -/

/-- The corpus after the fourth round of downloading. -/
def coreExtended4 : KB := (coreExtended3.merge Frontier4.kb).normalize

/-- It is well formed too. -/
theorem coreExtended4_wellFormed : coreExtended4.wellFormed = true :=
  KB.normalize_wellFormed (KB.wellFormed_merge coreExtended3_wellFormed Frontier4.kb_wellFormed)

/-- 918 items after the fourth round. -/
theorem coreExtended4_card : coreExtended4.items.length = 918 := by native_decide

/-- 14 items are still said nothing about. -/
theorem coreExtended4_rootless_card : coreExtended4.rootlessL.length = 14 := by native_decide

/-- Once more, `Q16003513` is the only item of the previous frontier that
Wikidata answers with no statement of its own. -/
theorem round_four_leaves_one_root :
    (let R := coreExtended4.rootlessL; coreExtended3.rootlessL.filter (fun q => q ∈ R)) =
      [Qid.wd "Q16003513"] := by
  native_decide

/-- Spelled out on the abstract relations: after four rounds of downloading,
`Q16003513` (*Wikimedia entity*) is still an item the corpus declares and states
nothing about. -/
theorem q16003513_still_rootless :
    Qid.wd "Q16003513" ∈ coreExtended4.items ∧
      (∀ b, ¬ coreExtended4.Sub (Qid.wd "Q16003513") b) ∧
      (∀ c, ¬ coreExtended4.Inst (Qid.wd "Q16003513") c) :=
  KB.mem_rootlessL_iff.1 (by native_decide)

/-! ### The whole chain -/

/-- **The sizes of the successive frontiers**: 144, 70, 42, 18, 14. -/
theorem frontier_sizes :
    [Core.kb.rootlessL.length, coreExtended.rootlessL.length, coreExtended2.rootlessL.length,
        coreExtended3.rootlessL.length, coreExtended4.rootlessL.length] =
      [144, 70, 42, 18, 14] := by
  rw [core_rootless_card, coreExtended_rootless_card, coreExtended2_rootless_card,
    coreExtended3_rootless_card, coreExtended4_rootless_card]

/-- Each round leaves strictly fewer items unexplained than the one before. -/
theorem frontier_sizes_decreasing :
    coreExtended4.rootlessL.length < coreExtended3.rootlessL.length ∧
      coreExtended3.rootlessL.length < coreExtended2.rootlessL.length ∧
        coreExtended2.rootlessL.length < coreExtended.rootlessL.length ∧
          coreExtended.rootlessL.length < Core.kb.rootlessL.length := by
  rw [core_rootless_card, coreExtended_rootless_card, coreExtended2_rootless_card,
    coreExtended3_rootless_card, coreExtended4_rootless_card]
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The corpus itself has 588 items. -/
theorem core_card : Core.kb.items.length = 588 := by native_decide

/-- And the corpora grow. -/
theorem corpus_sizes :
    [Core.kb.items.length, coreExtended.items.length, coreExtended2.items.length,
        coreExtended3.items.length, coreExtended4.items.length] =
      [588, 749, 847, 889, 918] := by
  rw [core_card, coreExtended_card, coreExtended2_card, coreExtended3_card, coreExtended4_card]

/-! ### Nothing is lost -/

/-- The corpus of round three entails the corpus of round two. -/
theorem coreExtended3_entails_coreExtended2 : coreExtended3.Entails coreExtended2 = true :=
  KB.entails_trans coreExtended3_wellFormed
    (KB.wellFormed_merge coreExtended2_wellFormed Frontier3.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended2_wellFormed Frontier3.kb_wellFormed))
    (KB.merge_entails_left coreExtended2_wellFormed Frontier3.kb_wellFormed)

/-- … and the third download. -/
theorem coreExtended3_entails_frontier3 : coreExtended3.Entails Frontier3.kb = true :=
  KB.entails_trans coreExtended3_wellFormed
    (KB.wellFormed_merge coreExtended2_wellFormed Frontier3.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended2_wellFormed Frontier3.kb_wellFormed))
    (KB.merge_entails_right coreExtended2_wellFormed Frontier3.kb_wellFormed)

/-- The corpus of round four entails the corpus of round three. -/
theorem coreExtended4_entails_coreExtended3 : coreExtended4.Entails coreExtended3 = true :=
  KB.entails_trans coreExtended4_wellFormed
    (KB.wellFormed_merge coreExtended3_wellFormed Frontier4.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended3_wellFormed Frontier4.kb_wellFormed))
    (KB.merge_entails_left coreExtended3_wellFormed Frontier4.kb_wellFormed)

/-- … and the fourth download. -/
theorem coreExtended4_entails_frontier4 : coreExtended4.Entails Frontier4.kb = true :=
  KB.entails_trans coreExtended4_wellFormed
    (KB.wellFormed_merge coreExtended3_wellFormed Frontier4.kb_wellFormed)
    (KB.normalize_entails (KB.wellFormed_merge coreExtended3_wellFormed Frontier4.kb_wellFormed))
    (KB.merge_entails_right coreExtended3_wellFormed Frontier4.kb_wellFormed)

/-- **The corpus of round four derives everything the original corpus did.** -/
theorem coreExtended4_entails_core : coreExtended4.Entails Core.kb = true :=
  KB.entails_trans coreExtended4_wellFormed coreExtended3_wellFormed
    coreExtended4_entails_coreExtended3
    (KB.entails_trans coreExtended3_wellFormed coreExtended2_wellFormed
      coreExtended3_entails_coreExtended2
      (KB.entails_trans coreExtended2_wellFormed coreExtended_wellFormed
        coreExtended2_entails_coreExtended coreExtended_entails_core))

/-- And everything each of the four frontier downloads stated: round one … -/
theorem coreExtended4_entails_frontier : coreExtended4.Entails Frontier.kb = true :=
  KB.entails_trans coreExtended4_wellFormed coreExtended3_wellFormed
    coreExtended4_entails_coreExtended3
    (KB.entails_trans coreExtended3_wellFormed coreExtended2_wellFormed
      coreExtended3_entails_coreExtended2
      (KB.entails_trans coreExtended2_wellFormed coreExtended_wellFormed
        coreExtended2_entails_coreExtended coreExtended_entails_frontier))

/-- … and round two. -/
theorem coreExtended4_entails_frontier2 : coreExtended4.Entails Frontier2.kb = true :=
  KB.entails_trans coreExtended4_wellFormed coreExtended3_wellFormed
    coreExtended4_entails_coreExtended3
    (KB.entails_trans coreExtended3_wellFormed coreExtended2_wellFormed
      coreExtended3_entails_coreExtended2 coreExtended2_entails_frontier2)

/-- … and round three. -/
theorem coreExtended4_entails_frontier3 : coreExtended4.Entails Frontier3.kb = true :=
  KB.entails_trans coreExtended4_wellFormed coreExtended3_wellFormed
    coreExtended4_entails_coreExtended3 coreExtended3_entails_frontier3

/-- Consequently every `subclass of` statement of the corpus and of the four
frontier downloads is derivable in the corpus of round four. -/
theorem coreExtended4_derives_sub :
    ∀ p ∈ Core.kb.sub ++ Frontier.kb.sub ++ Frontier2.kb.sub ++ Frontier3.kb.sub ++
        Frontier4.kb.sub,
      Relation.ReflTransGen coreExtended4.Sub p.1 p.2 := by
  intro p hp
  have key : ∀ (kb : KB), coreExtended4.Entails kb = true → p ∈ kb.sub →
      Relation.ReflTransGen coreExtended4.Sub p.1 p.2 := by
    intro kb hkb hmem
    exact (KB.isSubclassOf_iff coreExtended4_wellFormed _ _).1
      (KB.entails_sub hkb (show kb.Sub p.1 p.2 from hmem))
  rcases List.mem_append.1 hp with hp | hp
  · rcases List.mem_append.1 hp with hp | hp
    · rcases List.mem_append.1 hp with hp | hp
      · rcases List.mem_append.1 hp with hp | hp
        · exact key _ coreExtended4_entails_core hp
        · exact key _ coreExtended4_entails_frontier hp
      · exact key _ coreExtended4_entails_frontier2 hp
    · exact key _ coreExtended4_entails_frontier3 hp
  · exact key _ coreExtended4_entails_frontier4 hp

end Corpus
end Wikidata

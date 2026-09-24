import RequestProject.Generated.TheorySources
import RequestProject.Generated.TheorySitelinks
import RequestProject.Generated.Enriched
import RequestProject.Generated.Theories
import RequestProject.Generated.TheoryAuthority
import RequestProject.FieldsOfStudy

/-!
# The enrichment run, machine-checked

`RequestProject.Enrichment` says what the enrichment tool computes and
`RequestProject.Cli.Enrich` downloads the documents.  This file is the place
where the two meet the actual data: every number quoted in `docs/ENRICHMENT.md`
about the run over the seven theory articles is a theorem here, decided by
computation on the downloaded scan.

The run, in three rounds:

1. the Wikidata items of the seven theories were looked up and **all** their
   sitelinks pulled — 311 Wikimedia pages over 135 sites
   (`RequestProject.Generated.TheorySitelinks`, where the table is checked to be
   a partial bijection between items and pages);
2. their Wikipedia articles in ten languages were downloaded and scanned — 51
   documents; then the most cited external sources of those articles were
   downloaded and scanned in two further rounds — 25 more documents
   (`RequestProject.Generated.TheorySources`);
3. the eighty most referenced missing items were downloaded from Wikidata and
   their `subclass of` / `instance of` statements added to the theory corpus
   (`RequestProject.Generated.Enriched`).

What is checked below: the size and languages of the scan; the head of each of
the three rankings, hence *what the most referenced missing term, the most used
unmodelled property and the most cited uncollected source are*; and that the
enrichment step did what it promises — the enriched base is well formed, entails
the base it came from, declares every term it was asked to absorb, and leaves
strictly fewer terms missing.
-/

namespace Wikidata
namespace EnrichmentRun

open Enrichment

/-- The documents the run downloaded and scanned. -/
abbrev sources : List ScannedSource := Generated.TheorySources.sources

/-- The corpus the run started from: the seven theories and their neighbourhood. -/
abbrev baseKB : KB := Generated.Theories.kb

/-- The corpus after the autoformalisation step. -/
abbrev enrichedKB : KB := Generated.Enriched.kb

/-! ### What was pulled in -/

/-- Seventy-six documents were scanned. -/
theorem sources_length : sources.length = 76 := by native_decide

/-- Fifty-one of them are Wikipedia articles, in ten languages; the other
twenty-five are external sources cited by those articles (and by each other). -/
theorem articles_length : (sources.filter fun s => s.ref.lang != "").length = 51 := by
  native_decide

theorem external_length : (sources.filter fun s => s.ref.lang == "").length = 25 := by
  native_decide

/-- The languages of the scanned articles (`""` marks a non-Wikipedia source). -/
theorem languages_scanned :
    Generated.TheorySources.languages =
      ["en", "de", "fr", "es", "it", "ru", "ja", "zh", "pt", "nl", ""] := by native_decide

/-- The scan mentions 4191 items and cites 1748 sources. -/
theorem mentions_length : (sources.flatMap fun s => s.mentions).length = 4191 := by native_decide

theorem cites_length : (sources.flatMap fun s => s.cites).length = 1748 := by native_decide

/-- Every sitelink pulled is a page of a Wikimedia site, and the table is a
partial bijection — see `Generated.TheorySitelinks.sites_partialBijection`. -/
theorem sitelinks_length : Generated.TheorySitelinks.sites.links.length = 311 := by native_decide

/-! ### The frontier: what is missing, and how often it is referred to -/

/-- The ten most referenced items the corpus did not have. -/
theorem termDemand_top :
    (termDemand baseKB sources).take 10 =
      [(Qid.wd "Q180969", 27), (Qid.wd "Q3968", 25), (Qid.wd "Q82571", 23),
       (Qid.wd "Q1166618", 23), (Qid.wd "Q12479", 22), (Qid.wd "Q1260632", 22),
       (Qid.wd "Q5165061", 22), (Qid.wd "Q12488383", 22), (Qid.wd "Q12482", 20),
       (Qid.wd "Q379825", 20)] := by native_decide

theorem termDemand_head :
    (termDemand baseKB sources).head? = some (Qid.wd "Q180969", 27) := by native_decide

/-- **The most referenced missing term is `algebraic geometry` (Q180969)**, named
by 27 of the 76 documents: nothing missing is referred to more often. -/
theorem algebraicGeometry_most_referenced {q : Qid} {n : ℕ}
    (h : (q, n) ∈ termDemand baseKB sources) : n ≤ 27 :=
  termDemand_head_max
    (p := (Qid.wd "Q180969", 27))
    (List.cons_head?_tail (Option.mem_def.2 termDemand_head)).symm
    h

/-- It really is missing from the corpus, and really is mentioned. -/
theorem algebraicGeometry_missing : Qid.wd "Q180969" ∈ missingTerms baseKB sources := by
  native_decide

/-- The ten most used Wikidata properties this development has no Lean predicate
for.

When the run was first made, `is the study of` (P2578) and `topic's main
category` (P910) sat in this list, at 37 uses each.  They are the two the run
asked for and `RequestProject/FieldsOfStudy.lean` supplies, so they are gone from
the ranking below; what is left at the top are external identifiers and
Wikimedia project bookkeeping. -/
theorem predicateDemand_top :
    (predicateDemand Cli.modelledPredicates sources).take 10 =
      [("P646", 50), ("P373", 43), ("P6366", 43), ("P5008", 37), ("P6104", 37),
       ("P1482", 36), ("P3417", 36), ("P4215", 33), ("P1051", 30), ("P11514", 30)] := by
  native_decide

/-- The two predicates the run asked for are modelled now, so the scan no longer
demands them. -/
theorem studyPredicates_modelled :
    "P2578" ∈ Cli.modelledPredicates ∧ "P2579" ∈ Cli.modelledPredicates ∧
      "P910" ∈ Cli.modelledPredicates ∧ "P301" ∈ Cli.modelledPredicates := by native_decide

theorem studyPredicates_not_demanded :
    "P2578" ∉ missingPredicates Cli.modelledPredicates sources ∧
      "P910" ∉ missingPredicates Cli.modelledPredicates sources :=
  ⟨not_mem_missingPredicates_of_modelled studyPredicates_modelled.1,
   not_mem_missingPredicates_of_modelled studyPredicates_modelled.2.2.1⟩

/-- Ninety properties are still unmodelled. -/
theorem predicateDemand_length :
    (predicateDemand Cli.modelledPredicates sources).length = 90 := by native_decide

theorem predicateDemand_head :
    (predicateDemand Cli.modelledPredicates sources).head? = some ("P646", 50) := by native_decide

/-- **The most used unmodelled property is `Freebase ID` (P646)**, on 50 of the
scanned items — an external identifier, hence an instance of the `IdKB` layer
rather than a new predicate; `Generated.TheoryAuthority` collects those. -/
theorem freebaseId_most_used {p : String} {n : ℕ}
    (h : (p, n) ∈ predicateDemand Cli.modelledPredicates sources) : n ≤ 50 :=
  predicateDemand_head_max
    (p := ("P646", 50))
    (List.cons_head?_tail (Option.mem_def.2 predicateDemand_head)).symm
    h

/-- The most cited source not yet downloaded. -/
theorem sourceDemand_head :
    (sourceDemand sources).head? = some ("https://challenges.cloudflare.com", 5) := by
  native_decide

theorem cloudflare_most_cited {u : String} {n : ℕ} (h : (u, n) ∈ sourceDemand sources) :
    n ≤ 5 :=
  sourceDemand_head_max
    (p := ("https://challenges.cloudflare.com", 5))
    (List.cons_head?_tail (Option.mem_def.2 sourceDemand_head)).symm
    h

/-- The run is not finished: the scan still points at items, properties and
sources the library does not have. -/
theorem frontier_not_empty :
    (State.mk baseKB sources Cli.modelledPredicates).frontier.isEmpty = false := by
  native_decide

/-! ### What the enrichment step did -/

/-- The enriched corpus is well formed, so the certified queries apply to it. -/
theorem enriched_wellFormed : enrichedKB.wellFormed = true := by native_decide

/-- **Conservativity, on the real data**: everything the theory corpus asserted is
still derivable after enrichment. -/
theorem enriched_entails_base : enrichedKB.Entails baseKB = true := by native_decide

/-- The corpus grew from 191 to 553 items. -/
theorem items_grew : baseKB.items.length = 191 ∧ enrichedKB.items.length = 553 := by
  native_decide

/-- Every one of the eighty terms the run absorbed is now an item of the corpus. -/
theorem enriched_covers_top :
    ((termDemand baseKB sources).take 80).all (fun p => enrichedKB.items.contains p.1) = true := by
  native_decide

/-- In particular the most referenced missing term is missing no longer. -/
theorem algebraicGeometry_now_present : Qid.wd "Q180969" ∈ enrichedKB.items := by native_decide

/-- And the frontier of missing terms is strictly smaller than before. -/
theorem missingTerms_shrank :
    (missingTerms enrichedKB sources).length < (missingTerms baseKB sources).length := by
  native_decide

theorem missingTerms_counts :
    (missingTerms baseKB sources).length = 1162 ∧
      (missingTerms enrichedKB sources).length = 1061 := by native_decide

/-! ### The external identifiers the ranking pointed at

`wikidata authority` collects the string-valued statements whose property has a
`formatter URL`, which is what an external identifier is.  Over the seven theory
items that is 153 identifiers for 74 properties — and it settles what the two
constraints on identifier properties do here. -/

/-- The downloaded authority file. -/
theorem authority_size : Generated.TheoryAuthority.authority.ids.rows.length = 153 := by
  native_decide

/-- Every identifier belongs to at most one item, so an identifier identifies its
item (`Generated.TheoryAuthority.authority_distinctValues`). -/
theorem authority_distinctValues : Generated.TheoryAuthority.authority.DistinctValues :=
  Generated.TheoryAuthority.authority_distinctValues

/-- But the single-value constraint fails: `Stack Exchange tag` (P1482) and
`Quora topic ID` (P3417) give one item several identifiers, so not every
identifier property is a partial function
(`Generated.TheoryAuthority.authority_not_singleValue`).  Dropping those
properties restores it
(`Generated.TheoryAuthority.authoritySingle_partialBijection`). -/
theorem authority_not_singleValue : ¬ Generated.TheoryAuthority.authority.SingleValue :=
  Generated.TheoryAuthority.authority_not_singleValue

end EnrichmentRun
end Wikidata

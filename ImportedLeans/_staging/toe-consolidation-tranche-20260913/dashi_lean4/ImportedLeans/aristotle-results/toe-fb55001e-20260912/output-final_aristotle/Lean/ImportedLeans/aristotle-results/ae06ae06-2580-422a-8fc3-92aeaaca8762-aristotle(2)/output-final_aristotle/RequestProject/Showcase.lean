import RequestProject.Main
import RequestProject.Taxa
import RequestProject.TaxaLineage
import RequestProject.TaxaDiagnostics
import RequestProject.TaxaExamples
import RequestProject.Series
import RequestProject.SeriesChain
import RequestProject.SeriesExamples
import RequestProject.SeriesDiagnostics
import RequestProject.Queries
import RequestProject.Cli.Import
import RequestProject.Cli.Derive
import RequestProject.Cli.Format
import RequestProject.Cli.Codegen
import RequestProject.CompiledFacts
import RequestProject.CorpusEntailment
import RequestProject.MetaFrobenius
import RequestProject.MathCorpus
import RequestProject.TheoryCorpus
import RequestProject.Grounded
import RequestProject.PullbackRetraction
import RequestProject.RetractTopology
import RequestProject.PeriodicityReport
import RequestProject.SpectrumReport
import RequestProject.FeedbackSets
import RequestProject.SignedWords
import RequestProject.CyclicAlgebra
import RequestProject.CompilerPipeline
import RequestProject.OntologyLimits
import RequestProject.OntologyColimits
import RequestProject.OntologySheaves
import RequestProject.EnrichmentCorpus
import RequestProject.CorpusRounds
import RequestProject.Cli.ScanFormat

/-!
# The showcase, in Lean

`docs/showcase.svg` is a one-page poster of this development and
`docs/SHOWCASE.md` is its companion page.  Every claim they make is a named
theorem, and this module is the index: each section below `#check`s the results
the poster shows, so the poster is checked by the build rather than maintained
by hand.  Nothing new is proved here.

The sections follow the poster:

1. the five hierarchies of the ontology, and their separation;
2. the tools, and the guarantee attached to each stage of the pipeline;
3. Wikidata itself, compiled to Lean;
4. the ontology inside the ontology — see `docs/META.md`.
-/

namespace Wikidata
namespace Showcase

/-! ## 1. Five hierarchies, kept apart

Each hierarchy is a computable layer over a knowledge base whose Boolean engine
decides exactly the reflexive–transitive closure of the asserted statements, is
a partial order and is well founded on a validated layer, and is proved to be
none of the other hierarchies.
-/

/-! ### The taxonomy: `instance of` (P31) and `subclass of` (P279) -/

#check @KB.isSubclassOf_iff              -- the engine is exact for P279
#check @KB.isInstanceOf_iff              -- and for P31
#check @KB.isSubclassOf_trans
#check @KB.subclass_antisymm             -- a partial order on a valid base
#check @Ontology.instanceOf_trans_subclassOf   -- instances inherit upwards
#check @Ontology.level_instanceOf        -- levels drop by one across P31
#check @Ontology.level_subclassOf        -- and are constant across P279
#check @Examples.instanceOf_not_transitive     -- P31 is not transitive
#check @KB.isSubclassOf_iff_subclassOf   -- the engine agrees with the abstract model

/-! ### The meronomy: `part of` (P361) and `has parts of the class` (P2670) -/

#check @MKB.isPartOfB_iff
#check @MKB.isPartOfB_antisymm
#check @MKB.properPartOf_trans
#check @MKB.properWhole_wf               -- well founded, so induction upwards is legitimate
#check @MKB.exists_atom_part             -- atomistic
#check @MKB.partComplete_exhibits        -- P2670 completeness really exhibits the parts
#check @MKB.mem_expectedPartClasses_of_subclass  -- inherited down P279
#check @MKB.part_not_subclass            -- the meronomy is not the taxonomy
#check @MKB.part_not_instance

/-! ### Kinship: `father` (P22), `mother` (P25) and `spouse` (P26) -/

#check @FKB.descendsFromB_iff
#check @FKB.descendsFromB_antisymm
#check @FKB.properAncestor_wf            -- nobody is their own ancestor
#check @FKB.card_parents_le_two          -- at most two recorded parents
#check @FKB.sibling_symm
#check @FKB.sibling_irrefl
#check @FKB.spouseB_symm
#check @FKB.related_not_transitive       -- relatedness is not transitive
#check @FKB.parent_not_subclass          -- the family tree is not the taxonomy
#check @FKB.parent_not_instance

/-! ### Alternative parenting: `parent` (P8810), `stepparent` (P3448), roles -/

#check @ParentingKB.descendsFromB_iff            -- certified ancestry, whatever the role
#check @ParentingKB.geneticDescendsFromB_iff     -- certified *genetic* ancestry
#check @ParentingKB.properAncestor_wf            -- still well founded
#check @ParentingKB.geneticProperAncestor_trans
#check @ParentingKB.card_geneticParentsF_le_two  -- at most two *genetic* parents
#check @ParentingKB.rainbow_four_parents         -- but four recorded parents is fine
#check @ParentingKB.surrogacy_birth_not_genetic  -- the surrogate gave birth, the donor the genes
#check @ParentingKB.adoption_legal_disjoint_genetic
#check @ParentingKB.step_not_genetic_ancestor
#check @FKB.pValid_toParentingKB         -- the classical kinship layer embeds
#check @ParentingKB.pErrors_eq_nil_iff   -- the report is sound and complete
#check @ParentingKB.report_eq_nil_iff_pValid
#check @ParentingKB.stepWarnings_eq_nil_iff

/-! ### The series: `follows` (P155), `part of the series` (P179), `series ordinal` (P1545) -/

#check @SKB.isAfterB_iff
#check @SKB.after_antisymm
#check @SKB.predecessor_wf
#check @SKB.exists_origin                -- every item has an origin
#check @SKB.mem_chainFrom_iff            -- walking the chain enumerates exactly the items after
#check @SKB.chainFrom_nodup              -- each of them once
#check @SKB.head?_chainFrom

/-! ### Biological taxa: `parent taxon` (P171), `taxon rank` (P105), `taxon name` (P225) -/

#check @TKB.isDescendantB_iff
#check @TKB.descent_antisymm
#check @TKB.parent_wf
#check @TKB.exists_root                  -- every taxon descends from a root
#check @TKB.no_cycle_of_ranks            -- ranks certify acyclicity locally
#check @TKB.descent_total_of_functional  -- one parent per taxon makes a tree
#check @TKB.exists_unique_root
#check @TKB.taxon_of_name_unique         -- taxon name is injective
#check @TKB.parentTaxon_not_taxonomic    -- the tree of life is not the taxonomy

/-! ## 2. The tools

The stages of the `wikidata` pipeline — see `docs/CLI.md` — and the theorem
behind each of them.
-/

/-! ### `fetch` / `import`: the download is faithful -/

#check @Cli.sub_kbOfEntities_iff
#check @Cli.inst_kbOfEntities_iff
#check @Cli.kbOfEntities_wellFormed

/-! ### `check`: the report is sound, complete and witnessed -/

#check @KB.errors_eq_nil_iff_valid
#check @KB.mem_cycleIssues_iff
#check @KB.warning_prunable

/-! ### `derive` / `ask`: fact construction is sound and conservative -/

#check @KB.newSubL_sound
#check @KB.newInstL_sound
#check @KB.saturate_isSubclassOf
#check @KB.saturate_isInstanceOf
#check @KB.saturate_valid

/-! ### `why`: explanations are certified -/

#check @KB.checkSubChain_sound
#check @KB.subChain?_sound

/-! ### `query`: the evaluator is sound and complete -/

#check @Query.eval_sound
#check @Query.eval_complete
#check @Query.evalT_eq_eval              -- and the fast evaluator agrees with it

/-! ### `merge` / `normalize`: nothing is lost -/

#check @Query.Sat_normalize
#check @KB.dropSub_isSubclassOf          -- pruning a redundant statement is lossless
#check @KB.dropSub_valid
#check @KB.dropSub_length_lt             -- and terminates

/-! ### the `.wdkb` files: reading back gives exactly what was written -/

#check @Cli.parseKB?_renderKB

/-! ### `lean`: the compiled facts are exactly the entailed facts -/

#check @Cli.subFacts_sound
#check @Cli.subFacts_complete
#check @Cli.instFacts_sound
#check @Cli.instFacts_complete

/-! ## 3. Wikidata itself, compiled to Lean

The fragments in `data/` compiled into `RequestProject/Generated/`, and what the
real data turned out to look like — see `docs/CORPUS.md`.
-/

#check @Compiled.adams_instanceOf_naturalPerson   -- a downloaded fragment that is an ontology
#check @Compiled.level_naturalPerson
#check @Compiled.geography_subclass_cycle         -- a genuine P279 cycle in live Wikidata
#check @Compiled.no_ontology_over_geography       -- so no ontology has exactly those statements
#check @Compiled.no_ontology_over_core
#check @Compiled.core_knows_more_than_adams       -- merging adds knowledge
#check @Compiled.adams_organism_needs_both_downloads
#check @Corpus.core_entails_fragments             -- and loses none
#check @Compiled.unique_human_of_adamsFragment    -- a query answered over the real data

/-! ## 4. The ontology inside the ontology

The meta level, as reduction, retraction, pullback and a Frobenius-like
automorphism; the companion page is `docs/META.md`.
-/

#check @KB.selfDescription_valid          -- every base has a valid meta-description
#check @KB.valid_rename_iff               -- renaming along an injection changes nothing
#check @KB.metaReduce_metaLift            -- the reduction undoes the lift
#check @KB.metaRetract                    -- lift and reduction are a retraction
#check @KB.metaLift_subclassOf_iff        -- so the meta copy is conservative
#check @KB.metaLift_instanceOf_iff
#check @KB.metaLift_isMetaclass_iff
#check @KB.metaCore_eq_self_iff           -- the fixed points of the idempotent
#check @KB.metaEquiv                      -- the Frobenius-like automorphism
#check @KB.metaLift_merge                 -- which is a homomorphism for merging
#check @KB.metaLift_entails_iff           -- and for entailment
#check @KB.metaLift_isPullback            -- the meta copy is a fibre product
#check @Ontology.pullback.lift            -- the universal property of the pullback
#check @Ontology.pullback.lift_unique
#check @Ontology.Retract.subclassOf_iff   -- retracts are conservative extensions
#check @Ontology.Alignment.projection_formula   -- Frobenius reciprocity
#check @Ontology.Alignment.push_subset_iff      -- pushforward is left adjoint to pullback

/-! ## 5. The mathematics the library is made of

The Wikidata articles naming the notions of the development, the constructions
that instantiate them and the theorems that prove it; the companion page is
`docs/MATH.md`.
-/

#check @Ontology.endoSubmonoid                  -- monoid (Q208237)
#check @WellFormedKB.instPreorder               -- preorder (Q1425985)
#check @WellFormedKB.not_symm                   -- … not an equivalence relation
#check @WellFormedKB.not_antisymm               -- … and not a partial order
#check @Ontology.properSubclassOf_isStrictOrder -- strict order (Q11077412)
#check @Ontology.Alignment.pushPull_gc          -- adjoint functor (Q357858)
#check @Ontology.Retract.idem_isIdempotentElem  -- idempotent function (Q44106280)
#check @Ontology.Retract.fixedPoints_idem       -- fixed point (Q217608)
#check @KB.metaCore_isIdempotentElem            -- idempotence (Q368988)
#check @KB.fixedPoints_metaCore
#check @KB.metaEquiv_bijective                  -- bijection (Q180907)
#check @KB.metaLift_surjective_onto_allMeta     -- surjective function (Q229102)
#check @KB.renameSetoid                         -- equivalence relation (Q130998)
#check @KB.renameQuotientEquiv                  -- quotient set (Q3966112)
#check @Ontology.IsDisjointUnion.extension_eq_iUnion         -- partition of a set (Q381060)
#check @Ontology.IsDisjointUnion.pairwiseDisjoint_extension
#check @MathCorpus.mathArticles_are_items       -- the articles were downloaded …
#check @MathCorpus.mathArticles_are_grounded    -- … and each names a declaration
#check @MathCorpus.pullback_subclass_limit      -- Wikidata: a pullback is a limit
#check @MathCorpus.bijection_subclass_injection -- an injection …
#check @MathCorpus.bijection_subclass_surjection -- … and a surjection
#check @Grounded.vocabulary_grounded            -- every notion carries the label claimed

/-! ## 6. Topology, category theory and the theories around the pullback

The layers added on top of the fibre product: the category of ontologies, the
topology of a class hierarchy, the Grothendieck topology of covering families,
the homotopy- and cubical-type-theoretic readings of matched pairs, the
symmetries of a pullback and its `GF(2)`-linear algebra.
-/

#check @Ontology.ontCategory                    -- category theory (Q217413)
#check @Ontology.isPullback_pbOnt               -- the fibre product is a pullback in `Ont`
#check @Ontology.instHasPullbacksOnt            -- … and `Ont` has all of them
#check @Ontology.forgetOnt_isPullback           -- the items are the matched pairs
#check @Ontology.subclassTopology               -- topology (Q42989)
#check @Ontology.instAlexandrovDiscreteItemSpace -- Alexandrov topology (Q3532117)
#check @Ontology.continuous_iff_subclass        -- continuity is monotonicity
#check @Ontology.isPullback_topCat              -- the pullback of item spaces, in `TopCat`
#check @Ontology.continuous_pbCompare           -- the comparison map is continuous
#check @Ontology.specializes_iff_subclassOf     -- specialization is the subclass order
#check @Ontology.isHomeomorph_pbCompare_of_componentwise -- when the two pullbacks agree
#check @Ontology.exists_not_isHomeomorph_pbCompare       -- … and a cospan where they do not
#check @Ontology.surjectivePretopology          -- Grothendieck topology (Q1062242)
#check @Ontology.pbSnd_surjective_of_surjective -- covers are stable under base change
#check @Ontology.ontologyTopology_pullback_stable
#check @Ontology.pullbackEquivSigma             -- homotopy type theory (Q5891840)
#check @Ontology.fibPbFstEquiv                  -- base change of fibrations (Q493941)
#check @Ontology.pullbackPasteEquiv             -- the pasting lemma
#check @Ontology.cubePullbackEquiv              -- cubical type theory (Q139761564)
#check @Ontology.Iv.deMorgan_meet               -- De Morgan algebra (Q5244640)
#check @Ontology.autPerm                        -- automorphism group (Q60790315)
#check @Ontology.autOverSubgroup                -- subgroup (Q466109)
#check @Ontology.pbAut                          -- group theory (Q874429)
#check @Ontology.pbAut_fst                      -- the projections are equivariant
#check @Ontology.ExtSpace                       -- vector space (Q125977) over `GF(2)`
#check @Ontology.chi_symmDiff                   -- symmetric difference is addition
#check @Ontology.comapLin_pb_comm               -- the pullback square, linearly
#check @Ontology.injective_toExtPullback
#check @TheoryCorpus.theoryArticles_are_items   -- the articles were downloaded …
#check @TheoryCorpus.theoryArticles_are_grounded -- … and each names a declaration
#check @TheoryCorpus.group_subclass_monoid      -- Wikidata: a group is a monoid
#check @TheoryCorpus.field_subclass_vectorSpace -- … a field is a vector space

/-!
## 5. The pullback and the retraction, continued

The calculus of the two constructions the poster's fourth panel is built on —
see `docs/META.md`.
-/

#check @Ontology.pullback.symmIso               -- the fibre product is symmetric
#check @Ontology.pullback.idIso                 -- … trivial along the identity
#check @Ontology.pullback.assocIso              -- … and associative (pasting)
#check @Ontology.pullback.subVocabularyIso      -- two sub-vocabularies meet in their intersection
#check @Ontology.mono_pbSnd_of_mono             -- monomorphisms are stable under base change
#check @Ontology.Retract.comp                   -- retracts compose
#check @Ontology.Retract.isKernelPair_sec       -- a section is its own kernel pair
#check @Ontology.Retract.baseChange             -- retracts are stable under base change
#check @Ontology.splitRetract                   -- idempotents split
#check @Ontology.isIdempotentComplete_Ont       -- so `Ont` is idempotent complete (Q6371155)
#check @Ontology.Duplicate.mergeRetract         -- merging a duplicate item is a retraction
#check @Ontology.exists_no_retract              -- conservativity is a real constraint
#check @Ontology.exists_bijective_not_isIso     -- a bijective strict morphism need not be invertible
#check @Ontology.pullback.homEquiv              -- the universal property as a bijection
#check @Ontology.Retract.isEmbedding_sec        -- a retract of ontologies is a retract of spaces
#check @Ontology.Retract.isQuotientMap_ret      -- the retraction is a quotient map
#check @Ontology.exists_retract_ret_not_isOpenMap -- … but not always an open map

/-!
## 6. The terms of the corpus, and the periodicity search

The two layers of `docs/PERIODICITY.md`: the Wikidata terms of every entity of
the downloaded corpus, and the search for periodic points of its class
hierarchy.
-/

#check @KbTerms.corpus_item_has_label           -- every corpus item has an English label
#check @KbTerms.kbTerms_uniqueOk_en             -- the label/description constraint holds
#check @KbTerms.kbTerms_aliasOk                 -- no alias repeats its own item's label
#check @KbTerms.element_byLabel                 -- two items of the corpus are labelled *element*
#check @KB.mem_periodicItems                    -- the search finds exactly the periodic points
#check @KB.mem_periodicItems_iff_mem_cyclicItems -- … which are the cyclic items of the report
#check @Periodicity.periodOf_min                -- the search returns the shortest cycle
#check @Periodicity.isPeriodDivisor_iff_of_connected -- the period belongs to the component
#check @Periodicity.isPeriodDivisor_of_phase    -- a phase certificate bounds it from below
#check @Periodicity.isReturn_iff_multiple       -- … so the return times are known exactly
#check @PeriodicityReport.periodicItems_eq      -- 11 periodic items in the downloaded data
#check @PeriodicityReport.periodicItems_labels  -- what Wikidata calls them
#check @PeriodicityReport.periods               -- the shortest cycle through each
#check @PeriodicityReport.scientist_returns     -- the *scientist* component has period 4
#check @PeriodicityReport.acyclicCorpus_no_periodic -- the repair removes every periodic point

/-!
## 7. The periodicity spectrum

The widened search of `docs/SPECTRUM.md`: every relation of the ontology layer
as an operator, words in them, the phase of each component, the distance from
the class hierarchy to acyclicity, and the terminology graph against it.
-/

#check @KB.mem_wordStep                         -- a word computes its property path exactly
#check @Ontology.level_of_eval_wordExpr         -- a word raises the level by its P31 letters
#check @Ontology.instCount_eq_zero_of_closed    -- so no mixed word closes in an ontology
#check @Periodicity.isPeriodDivisor_of_phaseCertB -- phases, from reachability alone
#check @SpectrumReport.subPeriodOf_isSome_imp   -- no bound finds a twelfth periodic item
#check @SpectrumReport.periodHistogram_100      -- the histogram of shortest returns
#check @SpectrumReport.word_spectrum            -- the spectrum of the fourteen short words
#check @SpectrumReport.variableOrderClass_selfInstance -- an item that is an instance of itself
#check @SpectrumReport.instSub_periodicItems    -- nine items on a mixed-relational cycle
#check @SpectrumReport.mixed_disjoint_from_p279 -- … none of them on a `subclass of` cycle
#check @SpectrumReport.no_ontology_over_acyclicCorpus_links -- the repair is still not enough
#check @SpectrumReport.entity_instSub_periodDivisor_eq_one -- shortest return 3, period 1
#check @SpectrumReport.region_periodDivisor'    -- the *region* phase, without a closure table
#check @SpectrumReport.periodicItems_colliding  -- 3 of the 11 carry an ambiguous label
#check @FeedbackSets.min_feedbackEdgeSet_card   -- four statements away from acyclicity
#check @FeedbackSets.min_feedbackVertexSet_card -- four items away from acyclicity

/-!
## 8. The transformations, as an algebra

The programs-as-numbers ladder of `docs/PROGRAM-ALGEBRA.md`: a Gödel numbering
of the relation words, their composition monoid, the integer grading by
metaclass level, the compiler acting by morphisms, and the order-twelve cyclic
part.  Nothing above the integer grading — no quaternions, no Clifford algebra,
no Bott periodicity — is claimed.
-/

#check @RelWord.equivNat                        -- words in the relations *are* the naturals
#check @RelWord.decode_encode                   -- the Gödel numbering, one way …
#check @RelWord.encode_decode                   -- … and the other
#check @KB.wordStep_append                      -- concatenation of words is composition
#check @RelWord.degree_append                   -- the degree is a homomorphism to (ℤ, +)
#check @Ontology.level_add_degree               -- … and it is the metaclass level shift
#check @sdegree_append                          -- with inverses, an honest integer grading
#check @Ontology.level_add_sdegree              -- forward and backward steps cancel
#check @KB.roundTrip_isReturn                   -- why the searches use forward words only
#check @RelAlg.exists_eventually_periodic       -- finite carrier ⇒ eventually periodic powers
#check @CyclicAlgebra.cyclicRel_order_twelve    -- the cyclic part has order exactly twelve
#check @CyclicAlgebra.cyclicPhaseCRT            -- its phase group splits as ZMod 4 × ZMod 3
#check @CompilerPipeline.wordStep_compiled_mono -- a compiler stage is a morphism
#check @CompilerPipeline.compiled_answers_subclass -- … and preserves every derived answer

/-!
## 9. Limits, colimits and sheaves on the category of ontologies

What shape `Ont` has, beyond the pullback: which limits it has and which it does
not, the disjoint union as a coproduct, and a presheaf on the site of ontologies
that is a sheaf.
-/

#check @Ontology.mono_iff_injective             -- monomorphisms are the injections
#check @Ontology.isInitial_emptyOnt             -- the empty ontology is initial
#check @Ontology.not_hasTerminal                -- … and there is no terminal one
#check @Ontology.isColimit_sumCofan             -- the disjoint union is a coproduct
#check @Ontology.instHasBinaryCoproductsOnt     -- so `Ont` has binary coproducts
#check @Ontology.forgetOnt_sumOnt               -- whose items are the disjoint union
#check @Ontology.isSheaf_funPresheaf            -- labellings are a sheaf on the site …
#check @Ontology.funSheaf                       -- … so a sheaf of `Ont` (Q1094223)

/-!
## 10. Growing the corpus from its own sources

The enrichment loop of `docs/ENRICHMENT.md` and the frontier rounds of
`docs/CORPUS.md`: what the sources point at and the library does not have, the
absorption of the most referenced of it, and the guarantee that each round is
conservative.
-/

#check @KB.enrich_wellFormed                    -- an enriched base is still well formed
#check @KB.enrich_entails                       -- … entails the base it came from
#check @KB.enrich_provenance                    -- … and every new statement names its source
#check @Enrichment.termDemand_head_max          -- the head of the ranking is a most wanted term
#check @Enrichment.frontier_isEmpty_iff_closed  -- the to-do list is empty exactly when closed
#check @Enrichment.State.step_entails           -- a whole round is conservative
#check @Cli.parseScan?_renderScan               -- a scan survives the disk
#check @EnrichmentRun.enriched_entails_base     -- the first run, over the seven theories
#check @EnrichmentRun.missingTerms_shrank       -- … left fewer terms missing
#check @Corpus.coreExtended_entails_core        -- the frontier round loses nothing
#check @Corpus.frontier_sizes                   -- 144, 70, 42, 18, 14 items on the frontier
#check @Corpus.frontier_sizes_decreasing        -- … shrinking round by round

end Showcase
end Wikidata

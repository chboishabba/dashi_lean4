# Summary of changes for run d2062c22-7777-42ed-8bfb-f569d441c848
The single-page report is done, generated, verified and committed.

**The page itself — `site/report.html`** (3.5 MB, ~293 kB gzipped; drop it on any static host, no server, no network, no build step):
- Carries all 24 downloaded Wikidata ontologies and the 8,645 diagnostics inline as data blocks, plus the whole app (JS and CSS) inlined — nothing is fetched at runtime.
- **Query system**: a small surface syntax (`sub`, `inst`, `dsub`, `dinst`, `class`, `ne`) over one base or over the whole corpus, with an answers table and CSV/JSON download of the result.
- **Report/SVG output**: five views — corpus sizes, one dataset, defects by kind, answers, and a P279 neighbourhood graph — all drawn as SVG.
- **Export**: PNG download at 1×/2×/4× rendered from the current view, SVG download, and "Copy link to this view" which encodes the query and view in the URL hash for sharing.
- **Self check on load**: the browser re-runs 121 checks (query answers and chart digests) against values computed by the verified Lean engine and reports agreement in the status line.

**How it is produced and checked**:
- New command `wikidata onepage` (`RequestProject/Cli/OnePage.lean`), with `--assets`, `--out`, `--name`, `--warn`; regenerate with `scripts/make-onepage.sh`. Output is deterministic.
- `RequestProject/OnePage.lean` models the page and proves its guarantees: the sanitiser never leaves a `<` in a data block, sanitising published data is lossless, what a browser parses back out of a block is exactly the ontology that went in, the corpus round trip, the chart bars are one per ontology/kind and sum to the item counts, and the query probe answers agree with the verified evaluator. `RequestProject/Cli/OnePage.lean` proves the same round trip for the block the command actually emits, and the command re-checks it base by base before writing the file.
- `RequestProject/OnePageExamples.lean` runs those guarantees on the Douglas Adams fragment as concrete worked examples.
- All three files build with no `sorry`; a repo-wide search for `sorry` in `RequestProject` finds none, and the theorems depend only on the standard axioms (the worked examples additionally use the compiler-evaluation axioms inherent to `native_decide`).
- Headless check `scripts/verify_onepage.js` on the committed page: no script error, 24 blocks, self check agrees on all 121 checks with 0 disagreements, all five views well-formed SVG, query returns answers, PNG data URL lossless.

**Docs and plumbing**: `docs/ONEPAGE.md`, README and `docs/README.md`/`docs/CLI.md` entries, a CI step in `.github/workflows/lean.yml`, and a link to the report from the published index (`site/index.html`, `site/manifest.json` refreshed; the site verifier reports 48 files verified).

# Summary of changes for run 3ad2d497-5a84-4fab-8ec4-c6aa89c88f90
I continued the Lean 4 formalisation of the Wikidata ontology, adding the parts of the *property-constraint* layer that the development did not yet cover. Everything compiles: `lake build` finishes with **8212/8212 jobs, no errors**, there is no `sorry` anywhere in `RequestProject/`, and the new results use only the standard axioms. All executable checks in the new files are machine-evaluated (`decide`).

New files, all under `RequestProject/`:

- `RangeConstraints.lean` — the **range constraint** (Q21510860) and the **difference within range constraint** (Q21510854). Endpoints may be absent, so "no bounds" is the doubly unbounded case. Proved: the executable checks are exact characterisations of the abstract constraints; intersecting two ranges admits exactly what both admit and is the greatest such range; a range whose maximum lies below its minimum forbids the property numeric values outright; conformance is downward closed along sublists (hence holds of the rank-filtered "truthy" fragment), splits over concatenation, and is monotone in the table of constraints; the bounds can be read back off any conforming statement. For differences: a non-negative minimum orders the two properties (this is what makes `date of death` follow `date of birth`), differences compose with added intervals, reversing the two properties negates the interval, and a range on the compared property propagates into bounds for the constrained one. Worked fragment: population, birth years and a 0–150 year lifespan, with negative populations, far-future births, a death before the birth and an implausibly long life each rejected.

- `FormatConstraints.lean` — the **format constraint** (Q21502404) with a *certified* matcher for `format as a regular expression` (P1793). A small regular-expression language (character classes, concatenation, alternation, star, plus the derived literal, `plus`, `opt`, exact and bounded repetition) is given an inductive matching relation; matching is decided by Brzozowski derivatives, and the derivative and the resulting matcher are both proved to agree exactly with that relation. Bounded repetition is characterised as repetition at most *n* times. On top: string values of a constrained property must match the pattern, the checker is characterised exactly, conformance is downward closed and monotone in the table, a pattern that does not match the empty string forbids empty identifiers, and non-string values are outside the scope. Worked fragment: VIAF and ISNI patterns, with a leading zero, a letter, an empty identifier and a misgrouped ISNI all rejected.

- `ContemporaryConstraint.lean` — the **contemporary constraint** (Q25796498). Existence intervals are read off birth/inception and death/dissolution dates, with unknown dates leaving a side unbounded. Proved: the nonemptiness and overlap tests are correct; overlapping is symmetric, reflexive on nonempty existences, monotone under widening, and an item with unknown dates overlaps everything; separated existences do not overlap; and being contemporary is **not transitive**, so it cannot be propagated along chains. The claim-set checker is characterised exactly, and from conformance one gets that two related items with known dates are never separated in time.

- `CardinalityConstraints.lean` — **single-value** (Q19474404) and **multi-value** (Q21510857) constraints, counted on *distinct truthy values*, so ranks are taken into account. Proved: a maximum of one makes the property a partial function on the truthy data; a minimum of two yields two genuinely different values; a property declared both single- and multi-valued has no statements at all. The fragment shows two competing capitals rejected, and the same pair accepted once ranks single one of them out.

- `ConstraintSuite.lean` — the six statement-level checks (qualifiers, property scope, range, format, cardinality, contemporary) gathered in one profile and one run, with a defect report. Proved: the combined run is exactly the conjunction of the individual ones, the empty profile accepts everything, the report is honest (a kind is listed exactly when its check fails, and the report is empty exactly when the run succeeds), and the four claim-local checks are preserved by removing statements, hence hold of the truthy fragment — while the contemporary check is **not**, with an explicit base that satisfies it although its truthy fragment does not, so a report must be run on the fragment it is reported for.

As elsewhere in this development the identifiers follow Wikidata, but the example fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments. The Properties table lists the new definitions and main theorems, with every property marked proved.

# Summary of changes for run 9b444344-2e50-46eb-a8dc-62d475952e42
The publication layer is complete, and the whole library now builds end to end: `lake build` finishes with **8201/8201 jobs, no errors and no `sorry`** anywhere in `RequestProject/`.

**What the project now does with the findings**

*Proved Lean modules (all sorry-free, standard axioms):*
- `RequestProject/Publish.lean` — a JSON Lines publication format for a knowledge base plus content addressing. Reading a published file back gives exactly what was written (`parseJsonl?_jsonlOfKB`), the file carries one row per fact (`length_kbRecs`), and the canonical text determines the base, so the content address identifies it (`eq_of_renderKB_eq`, `cid_eq_of_renderKB_eq`).
- `RequestProject/Sync.lean` — the peer-to-peer layer. Merging is the least upper bound for entailment: it keeps everything either peer knew (`sync_entails_left/right`) and invents nothing (`sync_least`); it is commutative, associative and idempotent up to equivalence, so one round of gossip leaves every peer in the same state (`gossip_pairwise_equiv`) with no contribution lost (`gossip_entails_all`).
- `RequestProject/Archive.lean` — the archive.org deposit format: a deposit re-imports to the base it was made from (`importKB?_bundleOf`), the public JSON Lines file alone suffices (`importKB?_rows_only`), the copies inside a bundle agree, and the manifest of lengths and digests is honest (`checkManifest_bundleOf`).
- `RequestProject/PublishExamples.lean` — all of it exercised on the Douglas Adams fragment: 64 published rows, content address `wdkb1-d85a9bb9e764ac9a`, a deposit that re-imports, and two replicas proved to disagree and then proved to converge.

*Tool and generated artefacts:* four new commands — `wikidata publish`, `archive`, `unarchive`, `sync` — where `publish` emits the static site and JSON API. `site/` (24 published ontologies, 48 manifest-checked files) and `archive/` (deposits for the three canonical bases) are generated and committed; `scripts/verify_site.py site` re-verifies every length and digest against `site/manifest.json`.

*Deployment targets:* GitHub Pages (`.github/workflows/pages.yml`), Vercel (`vercel.json`), Cloudflare Pages (`wrangler.toml`), Hugging Face dataset and Space (`hf/`, `scripts/hf_sync.py`), Wikimedia Toolforge (`toolforge/`), archive.org upload/download and IPFS/peer scripts (`scripts/`, `p2p/`, browser peer code in `site/js/p2p.js`). A mirrors workflow drives them all, each step gated on the corresponding secret, and a CI workflow builds the library, greps for `sorry`, and checks that the committed site matches what the tool regenerates.

*Documentation:* new `docs/PUBLISHING.md`; the README, `docs/README.md`, `docs/CLI.md`, `docs/stats.py`, `examples/demo.sh` and now `docs/SHOWCASE.md` (new section 12) all cover the layer, and `docs/status.svg` and `docs/showcase.svg` were regenerated to include it.

In this session I completed the remaining polish (showcase prose and status figure for the publication layer), confirmed the full build succeeded, re-verified the generated site against its manifest, and committed and pushed everything.

# Summary of changes for run 976b8229-9413-47f5-a94b-16d49dacefeb
I picked the project up where it stopped, checked its health, and added a new layer to the Wikidata ontology formalisation.

**First, the health check.** A full rebuild of the library and the `wikidata` executable now completes with no errors, no `sorry` anywhere in `RequestProject/`, and only the standard axioms (plus the compiler/native-evaluation axioms the project already uses for facts computed from the downloaded data). One thing was genuinely broken and is now fixed: the shared module layering behind the two generated figures (`docs/showcase.svg`, `docs/status.svg`) had fallen thirteen modules behind the sources, so the generators refused to draw. The layering covers every module again — including a new layer for the wikitext modules — and both figures were regenerated.

**New: module extraction, a self-contained sub-ontology about a chosen set of items.**

- `RequestProject/Modules.lean` — `Wikidata.KB.moduleOf kb seeds` keeps the items reachable from the seeds along `subclass of` (P279) and `instance of` (P31) statements, together with every statement issuing from them; `mem_moduleItemsF_iff` says exactly what that set is. Proved about it: extraction is **sound** (`moduleOf_isSubclassOf_le`, `moduleOf_isInstanceOf_le` — the module derives nothing the base does not); it is **conservative** (`moduleOf_isSubclassOf`, `moduleOf_isInstanceOf` — about an item it keeps, the module derives *exactly* the facts the whole base derives, so extraction loses nothing); the lists the engine prints agree too (`moduleOf_superclassesOfL`, `moduleOf_classesOf`); a module of a validated base **passes the validator** (`moduleOf_valid`), hence is again an abstract ontology to which every theorem of the core applies; the base **entails** its own modules (`entails_moduleOf`); and the operation is monotone in the seeds, idempotent, and returns the base itself when the seeds are all its items.
- `RequestProject/ModulesExamples.lean` — on the worked fragment: the module about Douglas Adams keeps six of the seven items and drops `film` together with the disjointness statement about it, is valid, and still derives that Douglas Adams is an entity.
- `RequestProject/ModulesCorpus.lean` — on the downloaded corpus of 1578 items, 2257 `subclass of` and 1169 `instance of` statements: the module about *mathematics* (Q395) has 279 items, 405 `subclass of` and 266 `instance of` statements — about a fifth of the corpus — and answers every `subclass of` and `instance of` question about Q395 exactly as the whole corpus does. Sizes for the modules about `human` and `academic discipline`, and for the two seeds together (345 items, not the sum), are computed from the data as well; conservativity there needs only well-formedness, which the corpus has even though it is not valid.
- A new tool command, `wikidata module FILE.wdkb Q395 [Q5 …] [--out F] [--name N]`, with its guarantees recorded in `docs/CLI.md`, a step added to `examples/demo.sh` (on the corpus it reports 588 items down to the 93 about mathematics), and entries in the module overview, `README.md`, `docs/SHOWCASE.md` and the Lean showcase index that re-checks every claimed name.

The Properties table lists the new definition and the main theorems, all marked proved. All work is committed and pushed.

# Summary of changes for run b98f541c-98ec-449e-820e-39cf2d749c17
The "things to work on" reporting layer is complete, verified and checked in.

**What is in the project now**

*Lean modules (all build under the project's library target, no `sorry`, no extra axioms — only `propext`, `Classical.choice`, `Quot.sound`):*

- `RequestProject/Worklist.lean` — turns the existing report into a worklist: rows are grouped into `Task`s by a key (error type, file, layer, or kind of work), each task carrying its size, error/warning counts, the number of fixes that are *proved* safe versus merely suggested, the layers and codes involved, a sample, and a plain-English "what it takes" line. Renderers produce CSV, HTML and SVG from the same data. Proved about it: the grouping is a genuine partition of the report (`tasks_flatMap_perm`, `worklist_flatMap_perm`), the task sizes add up to the number of issues (`worklist_size_sum`), the worklist is sorted biggest-first (`worklist_sorted`), it is empty exactly when there is nothing to do (`worklist_eq_nil_iff`), the SVG bars count the same items as the table (`taskBars_count_sum`), the CSV reads back exactly as written (`parseCsvText_worklistCsv`), and a task marked "safe" contains only rows whose fix is proved to change no derived fact (`Task.automatic_rows_provenFix`).
- `RequestProject/Gaps.lean` — work that is not a defect: items with no parent, items no statement mentions, and declared classes with nothing under them, each turned into a report row. Proved: what "isolated" and "childless class" mean in terms of the base's statements (`mem_isolatedL_iff`, `mem_childlessClassL_iff`), every gap row is a warning and never an error (`gapRows_severity`), and an empty gap table certifies that no such gaps exist (`gapRows_eq_nil_iff`).
- `RequestProject/WorklistExamples.lean` — compile-time checks on the sample bases, including that a clean base has an empty worklist.
- `RequestProject/Cli/WorklistCmd.lean` and the new `wikidata worklist <files…> [--gaps] --out <dir>` command in `RequestProject/Cli/Tool.lean`.

*Generated artifacts, committed under `docs/reports/worklist/`:* four groupings — by error type, by file, by layer, by kind of work — each as `.csv`, `.html` and `.svg`; one CSV per task under `tasks/` (30 files) holding just that task's issues with identifiers, labels and suggested fix; and a `README.md` index. Over the current corpus the run reports 7398 items of work (5161 errors, 2237 warnings) in 30 tasks by error type and 25 by file; the largest are `level-sub` (3141), `level-inst` (1979), `no-parent` (1541) and `childless-class` (593), while `redundant-sub` (75) is the task whose every fix is machine-checked safe.

*Docs:* `docs/REPORTS.md`, `docs/CLI.md` (command, guarantees and source-layout rows), `docs/README.md`, `docs/reports/README.md`, the top-level `README.md`, and `scripts/make-reports.sh`, which now regenerates the worklist with `--gaps`.

The whole library was rebuilt from scratch after these additions and completed successfully (8184 jobs, no errors), and the headline theorems were checked for their axiom dependencies.

# Summary of changes for run dd6f06cc-3a73-4b4b-94b7-f8f7fbaf4df2
I picked the project back up, and the first thing I found was that it did not build: the `Qualifiers` module (allowed/mandatory qualifiers and the property scope constraint) failed to compile, and with it every target that depends on it. That is now fixed, and I also extended the formalisation with four new layers of the Wikidata ontology.

**The build is repaired.** `RequestProject/Qualifiers.lean` had six broken proofs (a lookup lemma that no longer exists, two inductions that needed generalising, and two mis-applied sublist lemmas). I replaced them with two general, reusable lemmas about looking a key up in a table — one for tables without repeated keys, one giving that a key that occurs can be looked up — and repaired the remaining proofs. All statements are unchanged. The whole library now builds (`lake build`, 8180 jobs) together with the `wikidata` command-line executable, with no `sorry` anywhere and only the standard axioms.

**New modules, all proved and machine-checked:**

- `RequestProject/GeoValues.lean` — **globe coordinates** (`coordinate location`, P625). Latitude, longitude, precision and globe; the box a measurement denotes; bounding boxes with their inclusion order (a partial order along which containment is monotone). Two measurements are *compatible* when they can denote the same point, and this is proved to be exactly overlap of the two boxes, and exactly closeness in the angular distance — which is shown to be a pseudometric vanishing precisely on coordinates naming the same point. On top of that sits the geographic containment layer of `located in the administrative territorial entity` (P131), with a certified decision procedure for containment (soundness *and* completeness of the saturation) and a decidable consistency check; in a consistent layer the coordinate of a region lies in the bounding box of every region containing it, so a coordinate outside a box refutes containment. The worked fragment puts Paris in France in Europe and derives the inherited location; two malformed variants are rejected.

- `RequestProject/ConstraintExceptions.lean` — the **administrative qualifiers of a constraint**: `exception to constraint` (P2303), `constraint status` (P2316) and `constraint scope` (P4680). Exceptions weaken a constraint exactly at the listed items; the items that really break it form the smallest admissible exception list, so any exception outside it is redundant; errors are exactly the unlisted violators of a mandatory constraint, a suggestion is never an error, and demoting a mandatory constraint removes its error. Scoped checking splits over unions of scopes and strengthens as the scope grows. The exception-aware checker is proved sound, and a worked `sex or gender` one-of constraint passes with the exception declared and fails without it.

- `RequestProject/SoftIdentity.lean` — **`said to be the same as` (P460) versus `different from` (P1889)**. The identity closure of P460 is proved to be an equivalence relation and the *smallest* one containing the declared statements, decided by a certified engine. Conflicts — pairs the closure identifies although P1889 declares them different — are detected exactly by a decidable check, and a merge-safety check is proved sound against declared class disjointness. The fragment shows two individually harmless P460 statements whose closure conflicts, and a link identifying a person with a city that the safety check rejects.

- `RequestProject/AllowedUnits.lean` — the **allowed-units constraint** (Q21514353) on quantity-valued properties, on top of the existing quantity and unit-conversion layer. The checker decides the constraint and reports exactly the offending statements; enlarging the allowed list weakens it and an empty list forbids quantity statements outright. The repair is proved correct: normalising a base into SI units satisfies any constraint allowing the SI unit while leaving every measurement's SI value and well-formedness unchanged.

The module overview and runnable demonstrations in `RequestProject/Main.lean`, the README, the shared module layering in `docs/stats.py` and the two generated figures (`docs/showcase.svg`, `docs/status.svg`) were all updated; the figure generators had also been left stale by a module missing from their layering, which is fixed. The Properties table lists the new definitions and main theorems, all marked proved. As before, the identifiers follow Wikidata but the example fragments are stylised excerpts, and the theorems about them are statements about those fragments.

# Summary of changes for run 7b6ab8a8-6cad-4b9e-ba3a-77bb6d0d060f
I refreshed both infographics and the written status report so they match the current state of the development, and fixed the two things that were making them wrong.

**The generated images (`docs/showcase.svg`, `docs/status.svg`)**
- Both generators were failing outright: 39 modules added since the images were last drawn were missing from the layer charts, whose guard refuses to draw a stale chart. The layering is now one shared list in `docs/stats.py`, used by both generators, so the two images cannot disagree; it covers all 144 modules exactly once and adds three new layers — the categorical/topological/type-theoretic layer, the programs–periodicity–spectrum layer, and the enrichment layer — plus the new defect, field-of-study, related-notions and baby-step modules in the existing ones.
- The poster's compiled-corpus table now lists all twenty-two downloaded fragments (it showed twelve), with a note on the merged `data/all.wdkb` base of 1578 items that the defect report, term table and periodicity search run over; I checked that every fragment's items really are contained in it.
- New poster section, "The ontology as mathematics": the category/topology/type theory of ontologies, the periodicity of the class hierarchy, and the algebra of transformations (Gödel numbering, composition monoid, the integer grading with inverses, the order-twelve cyclic part).
- The status report's "newest layers" panel now describes the signed words and the integer grading, the program algebra, the periodicity spectrum, the categorical layer and the enrichment loop, and the feature chips gained the newly covered Wikidata features.
- Figures that were typed in are now counted: the "merging adds knowledge" number (1178 subclass-of and 1044 instance-of facts no single fragment entails) is computed from the generated modules rather than quoted, and the sorry counter no longer miscounts a downloaded Wikidata description containing the word "admit" — it reports 0 gaps, which a search of the sources confirms.

**The written pages**
- `docs/SHOWCASE.md` (the companion status page) gained four sections — the ontology as a mathematical object, periodicity, the transformations as an algebra, and growing the corpus from its own sources — each naming the theorems behind the claims, and its stale figures were corrected (1610 grounded entities, 174 grounded notions, twenty-two fragments).
- `docs/CORPUS.md` gained the two missing fragment rows (`Theories`, `Enriched`) and a paragraph on `all.wdkb`; `docs/CLI.md` now documents the seven enrichment-loop commands the tool has (so the "tool commands" figure is 24, not 17); `docs/README.md` and the root `README.md` were brought in step, including the corrected frontier sizes (144, 70, 42, 18, then 14 left).
- `RequestProject/Showcase.lean`, the Lean index that re-checks every name the status page quotes, gained two sections: limits, colimits and sheaves on the category of ontologies, and the enrichment/frontier results. Adding them exposed a genuine name collision — two different top-level `Wikidata.Claim` declarations, in `Ranks.lean` and `Enrichment.lean`, which made the two halves of the library un-importable together. I renamed the enrichment one to `CandidateClaim`; no statement text changed, since the proofs use anonymous constructors.

`lake build` completes successfully over all 8170 jobs with no errors and no project warnings, and no `sorry` remains anywhere in `RequestProject/`. No new properties were added, so the properties table is unchanged.


# Summary of changes for run 3e17882d-b639-46a5-856b-5289f5d67e30
I picked up where the previous session left off and finished the outstanding work; the whole project now builds clean (`lake build`, 8170 jobs, no errors, no warnings from project modules) with no `sorry` anywhere in `RequestProject/`.

**What was completed this session**

1. **`RequestProject/SignedWords.lean` (new, now building).** Relation letters may be run backwards, as inverse property paths. It defines the signed alphabet `SLink`, the integer degree `sdegree` of a signed word and its additivity along concatenation, the reading of a signed word as a `PathExpr` (`swordExpr`), and the operator `KB.swordStep` with a proof that it computes exactly the path semantics (`KB.mem_swordStep`). The main results are:
   - `Ontology.level_add_sdegree` — the degree of a signed word is precisely the metaclass-level displacement it performs, so a forward and a backward `instance of` step cancel: an honest ℤ-grading;
   - `Ontology.sdegree_eq_zero_of_closed` and `KB.no_ontology_of_sword_return` — a closed signed walk has degree zero, hence any closing signed word of non-zero degree in a knowledge base refutes every ontology model of it;
   - `KB.roundTrip_isReturn` — the caveat that with inverses allowed *every* statement closes a loop, which is why the corpus searches use forward words only; the informative invariant is the degree, not the existence of a loop.

2. **`RequestProject/CyclicAlgebra.lean`.** Added the prime-fibre split of the order-twelve cyclic part: `cyclicOrder_factorization : 12 = 2 ^ 2 * 3` and `cyclicPhaseCRT : ZMod 12 ≃+* ZMod 4 × ZMod 3`.

3. **Documentation.** New `docs/PROGRAM-ALGEBRA.md` sets out the ℕ → ℤ → ℚ → ℂ → ℍ → 𝕆 → Clifford → Bott ladder rung by rung, naming for each rung the theorem that establishes it or stating plainly that it is not instantiated. Proved rungs: the Gödel numbering of relation words (`RelWord.equivNat`), the composition monoid (`KB.wordStep_append`), the ℤ grading with and without inverses, functoriality of the compiler stages, the `ZMod d` phases, finite eventual periodicity, and the order-exactly-twelve cyclic part. Not instantiated, and said so explicitly: ℚ, ℂ, ℍ, 𝕆, Clifford algebras and Bott periodicity — the observed 12 is the least common multiple of four independent cycle lengths in one downloaded dataset, with no proved relation to Bott's 8. Linked from `docs/README.md` and the root `README.md`, which gained a section on the transformation algebra.

4. **`RequestProject/Showcase.lean`** gained a section 8 indexing these results with `#check`s (importing `SignedWords`, `CyclicAlgebra`, `CompilerPipeline`), alongside the existing section 7 for the periodicity spectrum.

5. **Properties table** updated with the previously unregistered deliverables: the Gödel numbering, word concatenation as composition, the degree homomorphism, eventual periodicity of relation powers, the order-twelve cyclic part, the compiler stage morphism, and the three signed-word results. All the new properties are marked proved; axiom checks show only the project-standard `propext, Classical.choice, Quot.sound` (plus `Lean.ofReduceBool, Lean.trustCompiler` for the computed corpus facts).

All work is committed and pushed.


# Summary of changes for run 14275097-c657-4ada-839d-8c947296a6cb
The requested continuation is complete and the whole project builds cleanly (8163 build jobs, no `sorry`, only the standard axioms plus the compiler/native-evaluation axioms used by the data computations).

**1. Wikidata terms for the current knowledge base.** `scripts/fetch_kb_terms.py` downloads the English labels, descriptions and aliases of every entity appearing in the downloaded corpus (`data/all.wdkb`), including the properties P31/P279, caching the raw responses in `data/kb-terms-cache/` and writing `data/kb-terms.tsv` plus the Lean table `RequestProject/Generated/KbTerms.lean`. The result covers **1580 entities: all 1580 labelled, 1519 described, 3515 aliases**, assembled as a `Wikidata.TermStore`.

`RequestProject/KbTerms.lean` proves machine-checked properties of that table: the counts, full coverage of the corpus (`kbTerms_covers_corpus`, `corpus_item_has_label`), the Wikidata label/description uniqueness constraint (`kbTerms_uniqueOk_en`, via a new general lemma replacing an expensive quadratic check), alias well-formedness, and worked lookup examples showing label ambiguity (two distinct items both labelled *element*).

**2. The periodicity search.** `RequestProject/Periodicity.lean` develops the general theory: bounded reachability `ReachIn`, return times, periodic points, the computable shortest-period search `periodOf` with correctness and minimality theorems, period divisors, the transfer theorem showing periodicity is a property of a strongly connected component, and phase certificates (`isPeriodDivisor_of_phase`) that make component periods exact rather than upper bounds — together with a decidable knowledge-base layer (`KB.periodicItems`, `KB.aperiodicItems`, `KB.phaseOkB`) and a small worked fragment.

**3. Applied to the knowledge base.** `RequestProject/PeriodicityReport.lean` runs the search over the entire downloaded corpus (1578 items, 2257 `subclass of` statements). Exactly **eleven items are periodic points of the class hierarchy** — *geographical area*, *academic professional*, *academic*, *region*, *scientist*, *researcher*, *delict*, *violation of law*, *element*, *element of set*, *element*, named from the extracted term table — and the remaining 1567 are aperiodic. The shortest cycles have lengths 2, 4, 4, 2, 4, 4, 2, 2, 3, 3, 3, and a phase certificate for each of the four affected components proves the period exactly: e.g. the return times of *scientist* are precisely the positive multiples of 4. Finally, the repaired hierarchy of the defect report has no periodic point at all.

Documentation was updated accordingly: `docs/PERIODICITY.md`, a new README section on the corpus terms and the periodicity search, and additional `#check` entries in `RequestProject/Showcase.lean`.

# Summary of changes for run 58d21954-c311-4793-9f6d-8b5085b66ee5
Another small, self-contained step on the Wikidata ontology formalisation — plus repairs that got the whole project compiling again.

**New: `RequestProject/BabyStepsAlignment.lean` — "Baby steps, part three".**
Following the same numbered, one-theorem-per-step style as the existing `BabySteps` and `BabyStepsProperties` files, this instalment takes the four-item Wikidata fragment built by hand in `BabySteps` and *aligns* it with a small upper ontology (`douglas` → `person` ⊑ `agent`, with a metaclass on top):

- Steps 0–1 build the upper ontology by hand, discharging each of its four obligations (levels, class-hood, no subclass cycles) as a finite case analysis.
- Step 2 gives the `equivalent class` links and checks they form a sound alignment: every asserted statement of the fragment becomes a *derived* fact upstairs.
- Steps 3–5 read off what the alignment transports: the asserted facts, the inherited fact "Douglas Adams is an agent" (which no statement upstairs asserts), class-hood, metaclass-hood and the instance/class level step.
- Step 6 shows the non-facts survive: the alignment does not smuggle in the missing transitivity of `instance of`.
- Step 7 records identity and composition.
- Step 8 proves a limit that holds for *every* alignment out of *any* ontology: no alignment can link an item and one of its classes to the same target item (`map_ne_of_P31`).
- Step 9 contrasts conservative with lossy: our alignment reflects the class hierarchy exactly (`align_conservative`), whereas an alignment that merges two distinct classes is still sound but not conservative (`mergeAlign_not_conservative`).

All of it compiles without `sorry` and uses only the standard axioms.

**Repairs to the existing development.** The project as I received it did not build: three modules failed to elaborate, and a fourth was unreachable behind them.
- `Stratification` and `Paths`: two proofs relied on the computed reachable set being syntactically the fixed-iteration form; both now go through the existing bridging lemma.
- `Defects`: the cycle-detection definition no longer took the knowledge base as a parameter, and its characterisation lemma and two later proofs were rewritten against the current list/`ite` API.
- `DefectReport` (the scan of the 1578-item downloaded corpus) referred to a check that no longer exists and to an older form of the losslessness lemma; it is now stated against the current API, and one proof was reformulated to avoid an unfolding blow-up. Two of its statements lost membership hypotheses that the current lemma does not need.
- One genuine performance bug: the bulk-pruning definition recomputed the whole closure table once per statement, which made the corpus scan effectively non-terminating. Hoisting the table out of the filter makes that module build in about 1.5 hours, and its findings — 11 items on a `subclass of` cycle, 234 redundant statements, the bulk deletion being lossy before the cycles are broken and lossless after, 17 pairs asserted both ways — are now machine-checked again.

A full `lake build` of the project completes successfully with no errors and no warnings, and a search over the sources confirms no `sorry` remains.


# Summary of changes for run 7956e1f2-adc6-475b-8e37-e7204978c49d
I continued the pullback and retraction layer of the Wikidata ontology formalisation with two new modules, both `sorry`-free and using only the standard axioms; the whole project still builds cleanly.

**`RequestProject/PullbackRetraction.lean`** — the calculus of the two constructions.

*Isomorphisms.* `Ontology.Isomorphism` (a strict morphism with a strict inverse), its identity/inverse/composition, and the fact that every isomorphism is a retract in both directions; `ontIso` / `isoToIsomorphism` identify it with isomorphism in the category of ontologies.

*Pullbacks.* The fibre product is symmetric (`pullback.symmIso`), trivial along the identity (`idIso`), associative — an iterated fibre product is a fibre product along the composite (`assocIso`) — and the fibre product of an injective morphism with itself is its source (`diagonalIso`). The universal property is repackaged as a bijection of morphism sets (`homEquiv`). Its items are exactly the matched ones (`range_fst`, `range_snd`, `image_range_fst`), from which: **the fibre product of two sub-vocabularies of one ontology is the sub-vocabulary of their intersection** (`subVocabularyIso`). Monomorphisms are stable under base change (`mono_pbSnd_of_mono`, with the missing `pbFst_injective_of_injective`).

*Retractions.* Retracts contain the isomorphisms and compose; a section is a split monomorphism, a retraction a split epimorphism, and a section is its own kernel pair. **Idempotents split** (`splitRetract`): an idempotent strict endomorphism exhibits its fixed sub-vocabulary as a retract, and its associated idempotent is the endomorphism again — hence the category of ontologies is idempotent complete (`isIdempotentComplete_Ont`), making "retract" and "split idempotent" the same notion. **Retracts are stable under base change** (`Retract.baseChange`), so conservativity survives alignment against a third ontology (`baseChange_subclassOf_iff`, `baseChange_instanceOf_iff`).

*Worked examples.* Merging a duplicated item is the splitting of an idempotent, so the deduplicated fragment is a retract and the merge loses nothing (`Duplicate.mergeRetract`). Conversely, conservativity is a real constraint: two classes with nothing said about them are **not** a retract of the same two classes with a `subclass of` statement between them (`exists_no_retract`), which also shows a strict morphism can be a bijection on items without being an isomorphism (`exists_bijective_not_isIso`).

**`RequestProject/RetractTopology.lean`** — the topological reading: a retract of ontologies is a retract of item spaces. The section is a topological embedding (`Retract.isEmbedding_sec`), under which specialization between embedded items is exactly the `subclass of` order of the small ontology (`Retract.specializes_iff`, conservativity in topological form), and the retraction is a quotient map (`Retract.isQuotientMap_ret`) — but it need not be an open map (`exists_retract_ret_not_isOpenMap`, with an explicit witness). Both legs are also split mono / split epi of spaces under the existing functor to `TopCat`.

Duplication was avoided where the project already had a result: the monomorphism characterisation and the one-item ontology already in the limits module are reused rather than restated. `README.md`, `docs/META.md` and `RequestProject/Showcase.lean` were updated so the prose and the `#check` index stay in step with the build.


# Summary of changes for run 576f55ec-3cb9-4242-ba78-2da8d3dc68d5
Taking one more small, self-contained step on the existing formalisation, I added `RequestProject/BabyStepsProperties.lean` — the sequel to `RequestProject/BabySteps.lean`, in the same gentle numbered style, but for the *property* layer of Wikidata.

It builds a five-item, four-property fragment entirely by hand — Douglas Adams, Jane Belson, London, England, Europe, with `spouse` (P26), `relative` (P1038), `part of` (P361) and `has part(s)` (P527) — and goes from raw statements to conclusions one step at a time:

- Steps 0–3: the items and properties; the three asserted statements; what Wikidata says about the properties themselves (`spouse` is a subproperty of `relative` via P1647 and is declared symmetric; `part of` is declared transitive and is the P1696 inverse of `has part(s)`); the single obligation discharged, giving the fragment as a property layer, `fam`.
- Steps 4–5: the asserted statements, and then the derived ones, each by exactly one rule — Adams is a *relative* of Jane (property hierarchy), Jane is Adams's *spouse* (symmetry), London is *part of* Europe (transitivity), Europe *has part* London (inverse), and `has part(s)` inherits transitivity from its inverse even though it was never declared transitive.
- Steps 6–8: how to show something is *not* derived. Using the minimality of the derived statement relation, two over-approximations are built and each proved closed under all four derivation rules; from them follow the non-facts: no statement of the fragment ever links a place to a person (so London is not a relative of Jane), `part of` strictly increases place rank — hence England is not part of London and nothing is part of itself — and every derived `relative` statement is one of the two directions between the married pair, so England is not a relative of Europe.

The file depends only on the property layer, so it can be read straight after the first baby-steps file; `README.md` now points to it. It contains no `sorry` and no added axioms — the new theorems depend only on the standard `propext`, `Classical.choice` and `Quot.sound`. The whole project, including the `wikidata` executable, still builds cleanly, and the rest of the development is untouched. The new definition and the four main theorems are in the Properties table, all marked proved. Everything is committed and pushed.

As with the existing examples, the identifiers follow Wikidata but the fragment is a stylised excerpt rather than a dump; the theorems are statements about that fragment.

# Summary of changes for run 86beaed6-aa31-48c6-afe4-85c066f4563d
The seven requested theories are now all in the project, each stated as a result *about* the ontology pullback (the fibre product `Wikidata.Ontology.pullback` of two ontologies over a third, in `RequestProject/Reflection.lean`). The whole project builds cleanly with no `sorry` and no added axioms.

**The seven layers** (all in `RequestProject/`, namespace `Wikidata.Ontology`):

1. **Category theory** — `CategoryOfOntologies.lean`: the category `Ont` of ontologies and strict morphisms, the forgetful functor to `Type`, and `isPullback_pbOnt` showing the hand-built fibre product is a pullback square in Mathlib's sense, so `Ont` has all pullbacks; base change preserves injectivity and surjectivity.
2. **Topology** — `OntologyTopology.lean`: the Alexandrov topology of the `subclass of` order, continuity = monotonicity, item spaces are T₀, the functor `ontTop : Ont ⥤ TopCat`, and the pullback of item spaces in `TopCat`.
3. **Grothendieck** — `GrothendieckSite.lean`: jointly surjective families form a pretopology `surjectivePretopology` and a Grothendieck topology `ontologyTopology`; covers are stable under base change along the pullback.
4. **Homotopy type theory** — `HomotopyTypes.lean`: matched pairs as triples `(x, y, p)`, fibres of the projections, base change of fibrations and of equivalences, and the pasting lemma.
5. **Cubical type theory** — `CubicalTypes.lean`: the De Morgan interval, paths, cubes, faces and degeneracies, and the equivalence "a cube in the pullback = a compatible pair of cubes".
6. **Group theory** — `OntologyGroups.lean`: automorphism groups, the subgroup of compatible triples of symmetries, the homomorphism into the symmetries of the pullback, and equivariance of both projections.
7. **Field theory** — `OntologyFields.lean`: class extensions as a GF(2)-vector space (symmetric difference = addition), the pullback square realised linearly, and the fibre product of extension spaces.

**New this session** — `RequestProject/PullbackComparison.lean` settles the one question the topology layer had left open, namely how the item space of the fibre-product ontology compares with the topological fibre product:

* `specializes_iff_subclassOf` — topological specialization in an item space is exactly the derived `subclass of` order;
* `isHomeomorph_pbCompare_of_componentwise` — the comparison map is a homeomorphism whenever componentwise subclass chains can be run simultaneously;
* `exists_not_isHomeomorph_pbCompare` — this can fail: an explicit cospan (a three-item chain glued to a two-item ontology over a reference ontology asserting the transitive step directly) whose comparison map is a continuous bijection but not a homeomorphism, so the ontology-level pullback is genuinely finer.

**Wikidata grounding.** A 191-item fragment covering the theory articles (topology, Grothendieck topology, HoTT, cubical type theory, category theory, field theory, group theory and neighbours) is downloaded and compiled into the corpus, with machine-checked agreement theorems in `TheoryCorpus.lean` (e.g. a group is a monoid, a field is a vector space, HoTT is a type theory). The glossary holds 1005 entities / 601 articles and the vocabulary 174 notions, each cross-checked against the downloaded data.

Documentation is in `docs/THEORIES.md` (with the topology entry updated to record the new comparison results), with `#check` tours in `RequestProject/Showcase.lean`. Everything is committed and pushed.

# Summary of changes for run 0dcf9b3f-6eef-4186-a9c1-170fe9ab6ba7
I continued the search for Wikidata's mathematics articles that resonate with the internal structures of this formalisation, and turned each match into a checked theorem. The whole project builds cleanly (`lake build`, 8117 jobs), with no `sorry` and only the standard axioms.

**32 mathematics articles matched, each backed by a theorem.** `RequestProject/MathResonance.lean` restates the library's own constructions in Mathlib's vocabulary, so "this really is a pullback / a retract / an idempotent / an adjunction" is proved rather than asserted:

- *monoid* (Q208237) — the structure-preserving self-maps of an ontology form `Ontology.endoSubmonoid`, a `Submonoid (Function.End I)`, whose elements are exactly the strict endomorphisms;
- *preorder* (Q1425985) — entailment between well-formed knowledge bases is a `Preorder`, and it is genuinely neither an equivalence relation (`not_symm`) nor a partial order (`not_antisymm`), each shown by a decided counterexample;
- *strict order* (Q11077412) — proper `subclass of` is an `IsStrictOrder`;
- *adjoint functor* (Q357858) — pushing class extensions forward along an alignment is left adjoint to pulling back: a `GaloisConnection`, with unit and counit;
- *idempotent function / idempotence / fixed point* (Q44106280, Q368988, Q217608) — the retraction idempotent and the meta core are `IsIdempotentElem` in `Function.End`, and their `Function.fixedPoints` are computed exactly (the image of the section; the meta-written bases);
- *partition of a set* (Q381060) — a disjoint union of classes splits the extension of the whole into a union of pairwise disjoint extensions;
- *equivalence relation / quotient set* (Q130998, Q3966112) — an item merge identifies items along `Setoid.ker` of the renaming, and the merged vocabulary is the quotient;
- *injection / surjective function / bijection / isomorphism* (Q182003, Q229102, Q180907, Q189112) — for the meta lift and its inverse;
- *least fixed point* (Q6134913) — the reachable set of the saturation engine is an `IsLeast`;
- plus *homomorphism, pullback, limit, universal property, commutative diagram, retract, Conservative extension, Frobenius reciprocity, well-founded relation, decidability, soundness, completeness, upper bound, intransitivity, Herbrand structure, restriction, directed graph*, each matched with an existing result of the library.

**The grounding table.** `RequestProject/Vocabulary.lean` now pairs 150 declarations (up from 118) with the Wikidata entity each formalises, and `RequestProject/Grounded.lean` re-checks every entry against the freshly downloaded glossary — 899 entities, all grounded, each carrying exactly the label claimed.

**The articles as data.** The same 32 articles were queried from Wikidata into a new corpus fragment `data/structures.wdkb` (163 items, 232 statements, entailing 502 `subclass of` and 245 `instance of` facts) and compiled to `RequestProject/Generated/Structures.lean`; `scripts/refresh-corpus.sh` reproduces it. `RequestProject/MathCorpus.lean` closes the loop: every article is an item of the fragment and names a declaration of the library, and several of Wikidata's own statements are checked next to the theorem that says the same thing here — a bijection is an injection and a surjection, a pullback is a limit, an equivalence relation is a preorder, an adjoint functor is a functor, an idempotent function is an idempotent element.

**Documentation.** New page `docs/MATH.md` (the full match table and the agreements), linked from `README.md`, `docs/README.md`, `docs/SHOWCASE.md` and `docs/CORPUS.md`; the new results are indexed by `#check` in `RequestProject/Showcase.lean`, and both generated posters were regenerated with the new layer and figures. `ARISTOTLE_SUMMARY.md` was left untouched; all work is committed and pushed.

# Summary of changes for run a559edb9-44e1-497b-89fa-29aee3d4fc43
I continued the Wikidata ontology formalisation by modelling "the ontology inside the ontology" as the four constructions you named — reduction, pullback, retraction, and a Frobenius-like automorphism — and reviewed each notion against the formalisation. Everything builds cleanly with no `sorry` and only the standard axioms.

**The operation.** The move that puts an ontology inside itself is the *meta lift* `KB.metaLift kb = kb.rename Qid.about`, which re-reads every identifier `x` as the meta-level name `about x`; its inverse is the *reduction* `KB.metaReduce`, which reads meta names as the items they name.

**Three new modules.**

- `RequestProject/Reflection.lean` — the abstract layer over the existing `Ontology`/`Alignment` model: strict morphisms (`Ontology.Morphism`, lax alignments being unsuitable for limits); the reduct of an ontology along an injective renaming (`Ontology.comap`) and along an inclusion of a sub-vocabulary (`Ontology.subVocabulary`), proved to invent nothing; the fibre product `Ontology.pullback` with projections, a commuting square and the universal property in both halves (`pullback.lift`, `pullback.lift_unique`); retracts (`Ontology.Retract`) with the conservativity theorems `subclassOf_iff`, `instanceOf_iff`, `hasInstance_iff`, `isMetaclass_iff` and the split idempotent with its fixed-point description; and Frobenius reciprocity for class extensions — the adjunction `push_subset_iff` and the projection formula `f_*(A ⊓ f^*B) = f_*A ⊓ B`.
- `RequestProject/Renaming.lean` — the reduction machinery at the executable level: for an **injective** renaming, membership, metaclass levels, asserted statements, their reflexive–transitive closures, the certified engine and every clause of the validator transport in both directions, ending in `KB.valid_rename_iff`. (Contrast with the existing item merges, where a non-injective map genuinely changes the ontology.)
- `RequestProject/MetaFrobenius.lean` — the meta level itself. `KB.metaReduce_metaLift` (the reduction undoes the lift exactly, hence the lift is injective); `KB.metaRetract` (an ontology is a retract of its own meta copy) with the resulting conservativity results `metaLift_subclassOf_iff`, `metaLift_instanceOf_iff`, `metaLift_isMetaclass_iff` and their Boolean counterparts, plus `metaLift_valid_iff`; the idempotent `KB.metaCore` with `metaCore_eq_self_iff` characterising its fixed points as the knowledge bases written entirely in meta-vocabulary; `KB.metaLift_isPullback`, showing the meta copy *is* the fibre product of the reduction along the identity; and the Frobenius analogy made precise — injectivity, homomorphism laws for merging (`metaLift_merge`), entailment (`metaLift_entails_iff`) and validity, no fixed non-empty base (`metaLift_ne_self`), the reduction fixing exactly the ground identifiers (`Qid.deMeta_eq_self_iff`, the analogue of the prime field), the tower of iterates, and the isomorphism onto the "perfect" part, `KB.metaEquiv : KB ≃ {kb // kb.allMetaB = true}`. Two theorems tie the layer to the existing self-description, and a worked three-item fragment checks all of it by computation, including the two-step tower `about (about Q42)`.

**Review and documentation.** `docs/META.md` is the written review: what reduction, retraction, pullback and (both senses of) Frobenius mean in general, and which theorem realises each here. `docs/SHOWCASE.md`, `docs/README.md` and `README.md` link to it, `RequestProject/Showcase.lean` now `#check`s the new results so the prose stays in step with the build, and both generated posters were regenerated (their layer charts had also been missing the parenting modules from the previous run, which is fixed).

Existing declarations were reused rather than duplicated: class extensions come from `Concepts.lean`, and the new sub-vocabulary reduct is named apart from the statement-selection reduct in `Provenance.lean`. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.

# Summary of changes for run 9d2cac41-356f-47c8-831a-ed4238d629b9
I extended the formalisation with a parenting layer that allows alternative family structures — several parents, adoption, step- and foster parents, legal guardians, surrogates, gamete donors and godparents — while keeping everything computable and machine-checked. The whole project builds cleanly with no `sorry` and no warnings.

**The new layer (`RequestProject/Parenting.lean`).** A `ParentingKB` is an ontology together with role-tagged parenthood statements. Each statement records the child, the parent, a `ParentRole` (biological, gamete donor, surrogate, adoptive, step, foster, legal guardian, godparent — each grounded in the Wikidata item that names it) and a `ParentSlot`, i.e. which Wikidata property carries it: `father` (P22), `mother` (P25) or the gender-neutral `parent` (P8810). Spouse (P26) statements are kept as before. From these it computes all parents, the genetic, legal and social parents separately, children, siblings and genetic siblings, co-parents, the person who gave birth (`gestationalParent?`), and ancestry both in the wide sense and genetically.

**What is proved.**
- Both engines are exact: the Boolean descent checks decide the reflexive–transitive closures of the asserted statements (`ParentingKB.descendsFromB_iff`, `ParentingKB.geneticDescendsFromB_iff`), and genetic descent implies descent.
- Ancestry stays a partial order and is well founded (`ParentingKB.properAncestor_wf`, `ParentingKB.geneticProperAncestor_trans`/`_asymm`), so nobody is their own ancestor.
- The number of parents is unbounded, but a validated layer still gives at most **two genetic parents** — one genetic father, one genetic mother (`ParentingKB.card_geneticParentsF_le_two`).
- The classical `father`/`mother` layer embeds: every P22/P25 statement becomes a biological edge, the derived parents and ancestry are unchanged, and a validated kinship layer becomes a validated parenting layer (`FKB.pValid_toParentingKB`). The new layer is therefore a conservative extension of the old one, which is left untouched.

**Worked examples (`RequestProject/ParentingExamples.lean`), all decided by computation.** A child with four recorded parents — genetic mother, sperm donor, gestational surrogate and adoptive co-mother — passes the validator, has exactly two genetic parents, and the surrogate who gave birth is neither a genetic nor a legal parent while the donor is genetic but neither legal nor social. An adoption with a stepparent shows legal, social and genetic parenthood pulling apart, a stepparent who is not a genetic ancestor, and five recorded parents. Two genetic mothers, a genetic statement filed under the neutral `parent` property, self-parenthood and cycles are rejected; two adoptive parents are not.

**Diagnostics (`RequestProject/ParentingDiagnostics.lean`).** A report listing each defect with its witness, proved sound and complete: it is empty exactly when the layer is valid (`ParentingKB.report_eq_nil_iff_pValid`). Several parents, adoptive parents, surrogates and donors are deliberately not defects; step-parenthood not backed by a recorded marriage is reported as a warning instead.

**Grounding and docs.** All new Wikidata identifiers were looked up in Wikidata and added to the glossary (now 799 identifiers, all grounded), the vocabulary of defined notions gained the new entries (118 notions, each checked against the downloaded labels), and the counts asserted in the grounding checks were updated accordingly. The showcase list, `README.md` and `docs/SHOWCASE.md` describe the new layer, and the results are `#check`ed in `RequestProject/Showcase.lean`. I also replaced a deprecated string function in the command-line tool so the build is warning-free.

# Summary of changes for run 80cd68be-093d-440c-851a-5902b70960b4
Every term in the system is now grounded in Wikidata, and the grounding is machine-checked.

**The glossary.** A script (`scripts/fetch_glossary.py`) scans the whole project — Lean sources, downloaded corpus fragments, docs, examples — for Wikidata identifiers, looks each one up in the live Wikidata API, and records its English label, description, English Wikipedia article and canonical id. The result is exported three ways: `data/glossary.tsv`, the human-readable `docs/GLOSSARY.md`, and the Lean table `RequestProject/Generated/Glossary.lean` (`Wikidata.Generated.glossary`).

It covers **780 entities — 47 properties and 733 items; 422 of them have an English Wikipedia article, and 1 identifier turned out to be a redirect** (Q7184903 → Q7048977). Nine toy identifiers that appear only in hand-written illustrations (Q1–Q9, Q999999) are deliberately excluded and documented as such. `python3 scripts/fetch_glossary.py --check` reports 780/780 identifiers grounded.

**The vocabulary of the formalisation.** Identifiers were only half the story, so `RequestProject/Vocabulary.lean` grounds the other half: 103 notions the library itself defines, each paired with the Wikidata entity it formalises and that entity's label (e.g. `Wikidata.Ontology.subclassPartialOrder` ↦ `partial order`, Q1069998). Declarations are written as name literals, so Lean rejects an entry naming something that does not exist.

**Machine-checked guarantees** (`RequestProject/Grounding.lean` for the definitions and meaning lemmas, `RequestProject/Grounded.lean` for the checks), all proved without `sorry`:
- `glossary_wellFormed` — well-formed identifiers, no duplicates — plus the counts 780 / 422 articles / 1 redirect;
- `lookup_unique` — each identifier has exactly one entry;
- `corpus_covered` — every item of all twelve downloaded corpus fragments has a glossary entry;
- `handwritten_covered` — likewise for the hand-built ontologies (upper ontology, taxonomy, examples, subsumption, disjoint-union and alignment fragments);
- `vocabulary_grounded` — every notion of the vocabulary map resolves in the glossary with exactly the claimed label.

**Tooling and docs.** The command-line tool gained `wikidata gloss (Q64 | P279 | FILE.wdkb) …`, printing what Wikidata says about identifiers or about every item of a stored base, with links to the Wikidata concept and the Wikipedia article; `examples/demo.sh` demonstrates it. `README.md`, `docs/README.md`, `docs/CLI.md`, `docs/SHOWCASE.md` and the generated status/showcase posters were updated with the grounding layer and figures.

The full project builds successfully with no errors, no `sorry`, and only the standard axioms.

# Summary of changes for run ae61134f-b2f1-4c72-9979-1ee0b8c88799
I built a new status infographic and a showcase of the ontology and the tools, both generated from the sources rather than typed in by hand.

**New poster — `docs/showcase.svg`** (generated by `docs/make_showcase_svg.py`). One page covering:
- headline figures: 1737 theorems/lemmas, 939 definitions, ~44.5k lines of Lean, 78 modules, 16 tool commands, 588 Wikidata items compiled, 0 `sorry`;
- **the ontology**: the five hierarchies — taxonomy (P31/P279), meronomy (P361/P2670), kinship (P22/P25/P26), series (P155/P156/P179/P1545) and biological taxa (P171/P105/P225) — each with its properties, its headline results and its module list, plus the "separation, proved" panel (no hierarchy is allowed to be another);
- the data model around them, as a chip list (ranks, snaks, qualifiers, references, terms, sitelinks, identifiers, quantities, times, paths, constraints, schemas, lexemes, RDF, queries, diagnostics, …);
- **the tools**: the pipeline `fetch/import → check → derive/ask/why → query → merge/normalize → lean`, each stage showing its command, what it does and the guarantee that is a theorem, plus every command of the executable;
- **the compiled corpus**: all twelve fragments with items, asserted P279/P31 and entailed facts (bar chart), and three findings about the real data (a fragment that is a genuine ontology, the live `subclass of` cycle in the geography data, and that merging adds knowledge while losing none);
- theorems per layer of the development, and a verification footer (clean build, no `sorry`, standard axioms only, 543 `decide` checks, 95 `#eval` demos).

**Refreshed status report — `docs/status.svg`** (`docs/make_status_svg.py` rewritten): the shorter one-pager, with all figures recounted, the layer chart extended to the kinship, series and taxa modules, the feature chips updated, and the "newest layers" panel now describing `Taxa.lean` and `Kinship.lean`.

**How the figures stay honest.** `docs/stats.py` counts the modules, theorems, definitions, lines, `decide` checks and `#eval` demos in `RequestProject/`, the items and statements in `data/*.wdkb`, the entailed-fact lists in `RequestProject/Generated/`, and the commands documented in `docs/CLI.md`; `docs/svgkit.py` is the small shared SVG writer. Both generators refuse to draw a chart if a module is left out of the layering or counted twice.

**Companion text and a checked index.** `docs/SHOWCASE.md` names the theorem behind every claim on the poster, and the new `RequestProject/Showcase.lean` is that list in Lean: 78 `#check`s of the quoted results, grouped exactly like the poster, so the build fails if any cited name or statement changes. Nothing new is asserted there. Making that module possible required one rename: the time-qualified knowledge base of `Temporal.lean` is now `Wikidata.TimeKB`, since `Wikidata.TKB` was also used by the taxon layer and the two modules could not previously be imported together.

`README.md` and `docs/README.md` now point at the poster, the companion page and the regeneration commands. The whole project builds cleanly (`lake build`, 8104 jobs), contains no `sorry` or `admit`, and no axioms were added. All work is committed and pushed.

# Summary of changes for run 5177d034-fc06-4add-8628-109ac4044773
I continued the Wikidata formalisation with a small, self-contained increment: a **kinship layer** for the individual-level family properties, which the library did not yet cover.

**New: `RequestProject/Kinship.lean`** — an `FKB` is an executable knowledge base together with `father` (P22), `mother` (P25) and `spouse` (P26) statements. Everything is computable (`descendsFromB`, `isProperAncestorB`, `childrenL`, `ancestorsL`, `spouseB`, `siblingB`, `fullSiblingB`, `relatedB`, `fatherOf?`, `motherOf?`) and there is a validator `fValid`. Proved:
- **Certified ancestry**: on a well-formed layer, the Boolean check `descendsFromB` decides exactly the reflexive–transitive closure of the asserted parenthood statements.
- Ancestry is a partial order on a valid layer, so proper ancestry is a strict order, the ancestor count strictly decreases on going up a generation, and the genealogy is **well founded** — nobody is their own ancestor along a chain of any length.
- With at most one father and one mother recorded per person, the lookups return exactly the asserted parents, they are unique, and **each person has at most two parents**.
- Siblinghood is symmetric and irreflexive, full siblinghood implies siblinghood, spouse is symmetric and (on a validated layer) irreflexive, and the listed children and ancestors of a person are exactly the right ones.
- Relatedness (a common ancestor) is symmetric, reflexive, and holds between a person and each ancestor; it is **not transitive**, shown by a decided example.
- **The genealogy is not the taxonomy**: a validated layer never asserts parenthood between items related by `subclass of` or `instance of`; nobody is their own parent; and a decided counterexample shows parenthood is not inherited through `instance of`.
- Worked fragments: a three-generation family that passes every check, a blended family where half siblings are siblings but not full siblings, and rejected bases (an ancestry cycle, two different fathers).

**New: `RequestProject/KinshipDiagnostics.lean`** — the Boolean validator turned into a list of individually witnessed issues (dangling P22/P25/P26 endpoints, two fathers or two mothers, an ancestry cycle, a self-spouse, parenthood duplicating a taxonomy fact), with the soundness-and-completeness theorem that the ontology report and the kinship report are both empty exactly when the layer is valid.

`RequestProject/Main.lean` now imports the new modules and carries a runnable demo whose outputs are checked at compile time, and `README.md` mentions the new layer. The full project builds with no `sorry`, and the new results depend only on the standard axioms.


# Summary of changes for run 2053e6b1-f950-4736-9228-601f1257cadd
Continued the Wikidata formalisation by adding a certified conjunctive-query layer and exposing it through the command-line tool.

### New formal query language
- Added `RequestProject/Queries.lean`.
- Queries are conjunctions of atoms with variables or fixed items:
  - derived `subclass of` and `instance of`;
  - directly asserted P279 and P31 statements;
  - classhood;
  - disequality.
- Added executable binding enumeration and answer projection.
- Proved soundness and completeness: the evaluator returns exactly the assignments satisfying the query in the abstract ontology (`mem_eval_iff`).
- Proved that an empty result is equivalent to unsatisfiability over the knowledge-base items (`eval_eq_nil_iff`).
- Added an evaluator backed by the precomputed closure table and proved it returns exactly the same bindings (`evalT_eq_eval`).
- Proved query semantics are unchanged by knowledge-base normalisation (`Sat_normalize`).
- Proved monotonicity under entailment and specialised it to valid merges (`Sat_of_entails`, `Sat_merge_left`, `Sat_merge_right`).

### Query surface syntax and CLI
- Added `RequestProject/Cli/Query.lean` with syntax such as:
  ```sh
  wikidata query corpus.wdkb 'inst ?x Q5' 'sub ?x Q35120' --select x
  ```
- Supported atom keywords: `sub`, `inst`, `dsub`, `dinst`, `class`, and `ne`.
- Proved that printing and parsing valid atoms and complete queries round-trip.
- Added the `query` command to the `wikidata` executable. It evaluates against the certified closure-table implementation and prints selected variable bindings.
- Verified the executable on stored Wikidata data; for example, querying `data/douglas.wdkb` for `inst ?x Q5` returns `Q42`.

### Checked examples and downloaded data
- Extended `RequestProject/Cli/Examples.lean` with compile-time query examples.
- Extended `RequestProject/CompiledFacts.lean` with queries over the generated Douglas Adams fragment:
  - Douglas Adams is the unique item in that fragment returned as a human;
  - the query for class instances has ten answers;
  - the expected human/metaclass pair occurs among them.
- The uniqueness result uses evaluator completeness, so it is a theorem about the fragment’s ontology rather than merely an observed computation.

### Documentation
- Updated `README.md`, `docs/CLI.md`, and `examples/demo.sh` with query usage and guarantees.
- Refreshed `docs/status.svg` and its generator to include the query layer and current source counts.

The complete project and the `wikidata` executable build successfully. The modified Lean sources contain no `sorry`, `admit`, new axioms, or unsupported implementation hooks. The principal new theorems use only the permitted standard axioms. All changes are committed and pushed.

# Summary of changes for run e755f8bb-fe27-4457-8185-5d10f0c79ca4
Taking a small, self-contained step on top of the existing formalisation, I added `RequestProject/BabySteps.lean`: a gentle, numbered walkthrough of the Wikidata ontology model.

It builds a four-item fragment of Wikidata entirely by hand — Douglas Adams, `human`, `person`, and the metaclass "organisms known by a particular common name" — and takes it from raw statements to derived facts in one small step at a time:

- Step 0–1: the four items, the single `subclass of` (P279) statement, the two `instance of` (P31) statements, and the metaclass level of each item.
- Step 2: the four obligations of the abstract model discharged one by one (levels drop by exactly one across `instance of`, are constant across `subclass of`, only classes have subclasses, and the hierarchy has no cycles — the last via a small lemma classifying all `subclass of` chains).
- Step 3: `Wikidata.BabySteps.tiny`, the fragment as an abstract ontology.
- Steps 4–8: the facts read off from it — the asserted statements; inheritance (`adams_inst_person`: Douglas Adams is a person, though nobody said so); the failure of `instance of` to be transitive (`instanceOf_not_transitive`); who is an individual, a class, a metaclass (`organismName_isMetaclass`); that an individual has neither instances nor subclasses; and that the class hierarchy is a partial order in which the one asserted step cannot be reversed.

The file depends only on the core model, so it can be read first; the README now points to it as the starting point. It compiles as part of the full project build, contains no `sorry`, and its theorems depend only on the standard axioms (`propext`). The rest of the project is untouched and still builds cleanly. All work is committed and pushed.

# Summary of changes for run 7d3f1122-5256-4406-a90b-1889a4d9546a
I added a Lean 4 command line tool, `wikidata`, on top of the existing formalisation, so people can download, check and construct Wikidata facts from the shell. The whole project builds cleanly, contains no `sorry`, and every new theorem depends only on the standard axioms.

**Build and use it**

```
lake build wikidata                                     # → ./.lake/build/bin/wikidata
wikidata fetch Q42 --depth 3 --out douglas.wdkb         # download from the API
wikidata check douglas.wdkb                             # validate (exit 1 if broken)
wikidata derive douglas.wdkb --out closed.wdkb          # construct the implied facts
wikidata why douglas.wdkb Q5 Q154954                    # a re-checked explanation
```

Other commands: `import` (local `Special:EntityData` JSON), `ask`, `add` (assert a new statement, saved only if the ontology still holds up), `classes`, `instances`, `stats`, `merge`. Downloads are cached, so repeat runs and `--offline` need no network. `docs/CLI.md` documents everything; `examples/demo.sh` is a network-free tour using `examples/mini-wikidata.json`, and `RequestProject/Cli/Examples.lean` re-runs the same checks at compile time.

**What is verified** (new theorems, all machine-checked)

- *Import is faithful* (`Cli.sub_kbOfEntities_iff`, `Cli.inst_kbOfEntities_iff`): the tool asserts a P279/P31 statement exactly when the source JSON carries that claim — nothing invented, nothing dropped; and what it imports is always well-formed (`Cli.kbOfEntities_wellFormed`).
- *Fact construction is sound and conservative* (`KB.newSubL_sound`, `newInstL_sound`, `saturate_isSubclassOf`, `saturate_isInstanceOf`): every new fact reported by `derive` is derivable in the input, and adding them all changes nothing about what is derivable. Saturation preserves validity (`saturate_valid`) and reaches a fixed point in one pass (`newSubL_saturate`, `newInstL_saturate`).
- *Explanations are certified* (`KB.checkSubChain_sound`, `subChain?_sound`): the chain `why` prints really is a derivation, and the search only returns chains that pass the check.
- *Local files are lossless* (`Cli.parseKB?_renderKB`): reading back a file the tool wrote returns exactly the knowledge base written, under the separator-freeness condition the tool checks before writing. This is proved layer by layer — decimal numerals, tab/newline fields, identifiers, records, record lists.
- `check` reuses the project's existing diagnostics report, whose emptiness is already proved equivalent to validity.

One honest limitation, stated in the code and the docs: metaclass levels are not part of the Wikidata data model, so the importer infers them heuristically. No theorem claims the guess is right; the tool re-runs the validator and reports what it finds (on real crawls it does flag genuine level mismatches).

New files: `RequestProject/Cli/{Derive,Format,Import,Fetch,Tool,Examples}.lean`, `docs/CLI.md`, `examples/`; `lakefile.toml` gained the `wikidata` executable target, and `README.md` and the overview in `RequestProject/Main.lean` now point at the tool.

# Summary of changes for run ccbaf2f4-d162-45a9-acc5-91d548550d04
I continued the Lean 4 formalisation of the Wikidata ontology with three new layers, all machine-checked: the whole project builds cleanly, contains no `sorry`, and every new theorem depends only on the standard axioms (checked with `#print axioms`). Executable claims are decided (`decide`) or checked `#eval`s.

**`RequestProject/Mereology.lean` — the meronomy (`part of`, P361, and `has parts of the class`, P2670).** A mereological layer over the existing knowledge bases, with a computable part-of engine. Proved: the Boolean check decides exactly the reflexive–transitive closure of the asserted `part of` statements; on a valid layer part-of is a partial order, so proper part-of is a strict order; the hierarchy is well founded (the number of wholes above an item strictly decreases as one moves up), so induction from parts upwards is legitimate; and it is atomistic — every item has a part with no proper parts of its own. The meronomy is kept apart from the taxonomy: a validated layer never asserts a part statement between a class and one of its superclasses or classes, and a worked bicycle/wheel/rim fragment decides that `part of` is **not** inherited through `instance of`. For P2670: expectations are inherited downwards along `subclass of`, an item passing the completeness check really exhibits the required parts, and asserting further part statements never destroys completeness. Two classical mereological principles are shown *not* to follow from the data model: weak supplementation fails on the bicycle fragment (the wheel has only one recorded part) and is restored once a tyre is added, and a valid fragment records two distinct wholes with exactly the same proper part, refuting extensionality of parthood.

**`RequestProject/Redundancy.lean` — redundant `subclass of` statements.** A statement is redundant when its value is already reachable through another direct superclass. Proved: deleting a redundant statement is **lossless** — the pruned base derives exactly the same subclass and instance facts — and preserves validity, and the base gets strictly smaller so repeated pruning terminates. The combinatorial core is stated for an arbitrary relation: deleting one edge that is shortcut by a detour does not change the reflexive–transitive closure, antisymmetry being what makes this true. A worked fragment shows the shortcut being found and pruned, and that deleting a genuinely load-bearing statement does lose information.

**`RequestProject/Diagnostics.lean` — a witnessed issue report.** The single validity Boolean is turned into a list of concrete problems (dangling statements, metaclass level mismatches, subclass cycles, disjointness violations) plus redundancy warnings. Proved: the report is **sound and complete** — it is empty exactly when the base is valid — every reported issue comes with its witness, and every warning can be acted on by a deletion that changes no derived fact and keeps the base valid. A deliberately broken fragment produces the expected five errors.

`RequestProject/Main.lean` imports the new modules and runs demos of them, and the status infographic in `docs/` was regenerated with the new layer and recounted figures (39 modules, 1007 theorems/lemmas, 542 definitions, ~13.2k lines, 0 `sorry`); `docs/make_status_svg.py` regenerates it. All work is committed and pushed.

# Summary of changes for run fde868ea-d9ab-4591-af0a-7722fa3569bc
I continued the Lean 4 formalisation of the Wikidata ontology and produced the infographic status report you asked for.

**Infographic (new)** — `docs/status.svg` is a self-contained SVG status report showing: the headline figures (36 modules, 971 theorems/lemmas, 488 definitions, ~11.9k lines, 0 `sorry`), a bar chart of where the results sit across the four layers of the development (foundations and engine, class hierarchy and ontology, property layer and constraints, data model and serialisation) with the modules in each, a chip list of the Wikidata features covered (P31/P279, metaclass levels, disjointness, disjoint union and union of, ranks, qualifiers, some-value/no-value, references, terms, sitelinks, external identifiers, quantities and units, time precision, validity intervals, property paths, entity schemas, property constraints, P1963, lexemes, P1709, item merges, RDF export), a panel on the newest layer, and a verification footer. `docs/make_status_svg.py` regenerates it and `docs/README.md` explains how; every figure is counted from the sources and from a full build.

**New Lean layer** — `RequestProject/Rdf.lean` formalises the RDF rendering of the data model, which the development did not yet cover: the *truthy* layer (one direct `wdt:` triple per truthy statement) and the *full* layer (every statement reified at its own statement node with `p:`, `ps:`, `wikibase:rank` and one `pq:` triple per qualifier). Proved: the reified layer is **lossless** — each statement, rank and qualifiers included, is read back off the exported graph, hence the export is **injective**; a direct triple is exported exactly for the values a default query returns; no deprecated statement ever produces a direct triple, while the full layer keeps every statement whatever its rank; and RDFS-style entailment on the exported ontology graph (reflexivity and transitivity of `wdt:P279`, and `wdt:P31` followed by `wdt:P279`) is **sound and complete** for the derived `subclass of` and `instance of` facts, so it agrees exactly with what the executable engine computes. A worked fragment exports the Berlin statements (18 reified triples plus 3 direct ones), recovers the deprecated and the superseded statements from the graph, and derives "Douglas Adams is an entity" by the RDFS rules while rejecting a spurious triple — all by computation.

The module is wired into the overview in `RequestProject/Main.lean` with runnable demonstrations. The whole project builds cleanly, contains no `sorry`, and the new theorems depend only on the standard axioms. All work is committed and pushed, and the Properties table lists the new definitions and theorems as proved.

As before, the identifiers follow Wikidata but the example fragments are stylised excerpts, and the theorems about them are statements about those fragments.

# Summary of changes for run 0d7da31a-e1d9-4ea2-9248-e8e060d2566f
I continued the Lean 4 formalisation of the Wikidata ontology, adding four new layers on top of the existing development. The whole project builds cleanly, contains no `sorry`, and every new theorem depends only on the standard axioms (checked with `#print axioms`). All executable claims are machine-decided (`decide`) or checked `#eval`s.

New files, all under `RequestProject/`:

- `TypeProperties.lean` — **`properties for this type` (P1963) as a data layer**. A class declares the properties its instances are expected to carry; the file computes the expectations of a class and of an item, the *missing properties* report, and the completeness check. Proved: expectations are inherited downwards along `subclass of`, so an instance is held to the profile of every class above it; a base passing the completeness check really satisfies those inherited obligations; asserting further statements never destroys completeness, while asserting further `instance of` statements only adds obligations; and the layer is tied back to the abstract soft constraint already present in the project, so a complete base satisfies each of its P1963 declarations in the abstract semantics. A worked fragment shows Douglas Adams missing a citizenship statement, the completion, and the loss of completeness when a new `instance of` statement is added.

- `Stratification.lean` — **the shape of the class hierarchy**. The *height* of an item is its number of superclasses. Proved: height drops strictly at every proper subclass step, so it is a linear extension of the subclass order; the strict superclass relation is therefore well founded (induction on classes is legitimate); heights are bounded by the size of the base, so an ascending chain of classes has fewer steps than the base has items; items of equal height are never comparable; the items split into strata by height, each item in exactly one, with every P279 edge leading to a strictly lower stratum. It also gives an executable topological sort of the items, **proved correct**: every class precedes each of its proper superclasses.

- `Lexemes.lean` — **the lexicographical layer**: lexemes with a language, a lexical category, forms carrying grammatical features, and senses linked to items by `item for this sense` (P5137), with a validator. Proved: when the forms of a lexeme have pairwise different feature sets, lookup by features returns exactly the form having them; a lexeme *means* a class exactly when one of its senses denotes an instance of it (certified against the abstract `instance of`); translation through a shared denotation preserves meaning; and a lexeme with denotations in two disjoint classes necessarily has at least two senses. The *bank* fragment (English *bank*, German *Bank* and *Ufer*) shows that sharing a sense is not transitive.

- `Schemas.lean` — **entity schemas as cardinality shapes**: per-property minima and optional maxima, optionally closed shapes, and a decidable conformance check. Proved: the check is characterised exactly; a conforming item of a closed shape carries no statement outside the shape; conformance to the conjunction of two open shapes is conformance to both; shapes without upper bounds are monotone under further statements; and the P1963 completeness check is *exactly* conformance to the shape asking for one statement per expected property, identifying that soft constraint as the cardinality-one fragment of the schema language. A worked human schema (exactly one date of birth, at least one citizenship, closed) accepts one item and rejects another, and shows a closed shape and a maximum being broken.

`Engine.lean` gained the two general transitivity lemmas the new layers use (derived `subclass of` is transitive, and derived `instance of` composes with it), and `Main.lean` was extended with the new module overview entries and runnable demonstrations. As before, identifiers follow Wikidata but the fragments are stylised excerpts; the theorems about them are statements about those fragments.


# Summary of changes for run a28594e0-13d1-453b-b89e-9a7c32dc6740
I continued the Lean 4 formalisation of the Wikidata ontology, adding seven further layers on top of the existing development. Everything compiles with no `sorry`, uses only the standard axioms, and the executable checks are machine-evaluated (`decide` and `#guard_msgs`-checked `#eval`s). The module overview in `RequestProject/Main.lean` was extended with the new modules and runnable demonstrations.

New files, all under `RequestProject/`:

- `Provenance.lean` — **references and verifiability**: `stated in` (P248), `reference URL` (P854) and `imported from Wikimedia project` (P143), the last of which is not a source. Statements carry reference lists, and three ordinary knowledge bases are extracted: everything asserted, the *sourced* fragment and the *reliable* fragment. Proved: selecting statements by any reference test preserves validity, so the sourced and reliable fragments are valid ontologies and every ontology theorem applies to them; sourcing never invents facts (the derived facts only grow along the chain reliable ⊆ sourced ⊆ asserted); and every derived `subclass of` fact rests on a finite chain of asserted statements, so a chain of referenced statements is exactly what makes a fact verifiable. The fragment exhibits a fact that is asserted but unverifiable and one that rests only on an `imported from` note.

- `Matching.lean` — the shape shared by several layers of the data model: a table of ⟨subject, key, value⟩ triples. Proved: a table that is functional (one value per subject and key) and injective (one subject per value and key) is a **partial bijection**, its two lookups being mutually inverse; and two tables sharing a key induce a **matching** which is symmetric, injective and transitive along a third table.

- `Sitelinks.lean` — the sitelink layer, built on `Matching`: an item has at most one page per site and a page is linked from at most one item, making the sitelink table a partial bijection between items and pages of a site, so a sitelink identifies its item. Merging two items is proved legitimate exactly when their sitelinks do not clash on a common site — with a worked table in which merging a duplicate is accepted and merging two items sharing a wiki is rejected.

- `ExternalIds.lean` — **external identifiers and authority control** (`VIAF ID` P214, `GND ID` P227, ...) with their `formatter URL` (P1630). Proved: under the single-value and distinct-values constraints an identifier property identifies the item; resolution to a URL is injective, so the address identifies the item too; a pair of distinct items sharing an identifier is exactly a distinct-values violation, which the executable duplicate finder reports; and two databases sharing an identifier property are matched through it, symmetrically, injectively and transitively.

- `TimeValues.lean` — the **time datatype**: a date recorded to a stated precision (millennium … day) in a stated calendar model, denoting the set of instants agreeing with it as far as its precision reaches. Proved: reading a date at a precision is determined by reading it at any finer one, so agreement is an equivalence relation growing coarser-wards; a more precise value denotes fewer instants; two values in the same calendar can refer to a common instant exactly when they agree at the coarser of their two precisions; and compatibility, though reflexive and symmetric, is **not transitive** — `1 May 1990` and `1 July 1990` are both compatible with `1990` but not with each other. Values in different calendar models are never compatible, and BCE years are handled by floor division.

- `Subsumption.lean` — **least common subsumers**: the most specific class subsuming two given ones. Proved: it is unique when it exists, symmetric and idempotent, equal to `b` when `a` is a subclass of `b`; anything instantiating both classes instantiates it; items at different metaclass levels have no common superclass at all; the executable candidate list contains exactly the least common subsumers, hence at most one element, and both soundness and completeness of the computation are proved. A fragment with genuine multiple inheritance (ducks and swans, both birds and aquatic animals) is shown to have **no** least common subsumer.

- `Snaks.lean` — the snak types **`somevalue` and `novalue`**, which make the data model genuinely logical: an existential and a negative claim. An assignment records the values each item really has; it models a base when every snak comes out true. Proved: a value entails `somevalue`; a `novalue` snak clashing with a value or a `somevalue` makes the base unsatisfiable; **a base has a model exactly when it is clash-free**, and the clash test is executable, so consistency of the snak layer is decidable; and a consistent base entails `novalue` exactly when it asserts it and `somevalue` exactly when it asserts a value or a `somevalue`, so the layer says neither more nor less than what is written in it. The fragment (Elizabeth I with no children, an unknown father, a recorded spouse) is checked, together with two inconsistent variants.

The Properties table lists the new definitions and main theorems, all marked proved. As before, the identifiers follow Wikidata but the example fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments.

# Summary of changes for run 55a4a0c2-286b-4473-a213-24545ca8e318
I continued the Lean 4 formalisation of the Wikidata ontology, adding five further layers on top of the existing development, and verified the whole project: everything compiles with no `sorry`, uses only the standard axioms, and the executable checks are machine-evaluated (`decide` and `#guard_msgs`-checked `#eval`s). The module overview in `RequestProject/Main.lean` was extended with the new modules and runnable demonstrations.

New files, all under `RequestProject/`:

- `Temporal.lean` — **time-qualified statements**, i.e. the qualifiers `start time` (P580) and `end time` (P582). A validity interval is an optional start and an optional end, with membership, a decision procedure, intersection, inclusion and disjointness; a time-qualified knowledge base attaches such an interval to each `subclass of` / `instance of` statement, and its **snapshot** at a point in time is the ordinary knowledge base of the statements valid then. Proved: deleting statements from a valid base leaves it valid, hence **every snapshot of a valid time-qualified base is a valid ontology**, so the ontology theorems hold at every point in time; a snapshot never invents facts; unqualified statements survive every snapshot while a statement whose end precedes its start is invisible at all times; and a set of statements is single-valued at each moment exactly when statements of the same subject with different values have disjoint intervals. The worked fragment (Berlin, East Germany, Germany) is checked at several dates, and shows a pair of overlapping intervals being rejected and the corrected version accepted.

- `Paths.lean` — **property paths, the query language**. Path expressions (empty path, atomic property, inverse, composition, alternation, closure) with their semantics over any labelled relation. Proved: the algebra of paths — composition is associative with the empty path as unit and distributes over alternation, alternation is a commutative idempotent operation, inversion is an involutive anti-automorphism commuting with alternation and closure, and the closure satisfies its unfolding law, is idempotent and absorbs composition with itself. The executable evaluator over a finite labelled graph is **certified**: the computed answer set is exactly the semantics. The pay-off: the Wikidata idiom `wdt:P31/wdt:P279*` computes exactly derived `instance of` and `wdt:P279*` exactly derived `subclass of`, both abstractly and as run on a knowledge base, and a property declared transitive answers the path `p/p*`. A worked fragment runs the queries by evaluation.

- `Terms.lean` — **labels, descriptions and aliases**. The term table of a knowledge base with its lookups and search functions. Proved: the executable label/description uniqueness check is *exactly* the constraint it expresses — it holds precisely when the assignment of a (label, description) pair to an item is injective among the items carrying both in a language — so a search by label and description returns at most one item; the alias check guarantees that an item's label is never among its own aliases. A fragment where three items are labelled *Mercury* shows that labels alone do not identify an item, and duplicated label-plus-description and an alias repeating its own label are both rejected.

- `Concepts.lean` — **the extensional view of the class hierarchy**. The maps sending a set of items to the classes they all share and a set of classes to the items instantiating all of them form an antitone Galois connection, so their composite is a closure operator; its fixed points, the *extents*, are closed under arbitrary intersections, include the extension of every class, and form a complete lattice with intersection as meet. Inheritance is exactly inclusion of extents — but the converse fails, and a valid knowledge base is exhibited in which two distinct classes have exactly the same instances while neither is a subclass of the other, so the extensional reading is strictly coarser than the asserted hierarchy.

- `Quantities.lean` — **the quantity datatype**: an amount with an uncertainty interval and a unit, and a table of `conversion to SI unit` (P2370) factors. Proved: rescaling by a positive factor is functorial, preserves well-formedness and transports the uncertainty interval and the order of amounts exactly; conversion into SI units is well-formed; comparison of quantities across units by SI value is a total preorder; and consistency of two measurements (overlapping uncertainty intervals) is reflexive, symmetric and invariant under conversion, so whether two measurements agree does not depend on the unit they were recorded in. The fragment records a length as 1 kilometre and as 1000 metres — the same SI value, hence consistent — while 1 metre is not consistent with a rough kilometre.

The Properties table lists the new definitions and main theorems, all marked proved. As before, the identifiers follow Wikidata but the example fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments.

# Summary of changes for run 5f6fdebf-2b9f-40fa-a568-cd22ea5de060
I continued the Lean 4 formalisation of the Wikidata ontology, adding four further layers on top of the existing development. Everything compiles with no `sorry` and uses only the standard axioms; the executable checks are machine-evaluated (`decide` and `#guard_msgs`-checked `#eval`s), and the module overview in `RequestProject/Main.lean` was updated with the new modules and runnable demonstrations.

New files, all under `RequestProject/`:

- `Semantics.lean` — **the extensional semantics and its adequacy**. Until now `subclass of` and `instance of` were treated proof-theoretically, as inductively derived facts. A `Model` of an ontology interprets each item both as a point of a domain and as a set (its *extension*), so that asserted `instance of` (P31) statements become memberships and asserted `subclass of` (P279) statements become inclusions. Proved: **soundness** — in every model the derived relations hold extensionally, so the derivation rules never assert more than the intended reading; **completeness** — via a canonical model, an inclusion (resp. membership) that holds in every model is exactly a derivable `subclass of` (resp. `instance of`) fact; **consistency of the disjointness layer** — every ontology with disjointness declarations has a model where the declared disjoint classes really have disjoint extensions, and in that model a class has a nonempty extension exactly when it has an instance; models pull back along `equivalent class` alignments. The same soundness/completeness picture is then proved one level up for the statement relation of the property layer. The worked Wikidata fragment is interpreted in its own model.

- `StatementConstraints.lean` — **the statement-level property constraints**: item-requires-statement (Q21503247), value-requires-statement (Q21510864), conflicts-with (Q21502838), one-of (Q21510859), none-of (Q52558054) and the inverse constraint (Q21510855), plus the soft `properties for this type` (P1963). Proved: every constraint of a property is a constraint of each of its subproperties (and relaxes to superproperties on the required side); conflicts-with is symmetric; a property that conflicts with itself, or that both requires and conflicts with the same property, has no statements at all; a one-of list contained in a none-of list forces the property to be empty; a one-of list of instances of a class yields the value-type constraint for that class; the inverse constraint at a single property is exactly symmetry of the derived statements, and a declared `inverse property` pair satisfies it; P1963 expectations are inherited by subclasses and combine with a type constraint to give an item-requires-statement constraint. Six executable checkers are proved sound against these abstract notions, and a worked fragment (place of birth / country of citizenship / country) exercises them, including a constraint that is correctly rejected.

- `ItemMerge.lean` — **merging items (redirects)**. A merge is a renaming of identifiers; `rename` rewrites a knowledge base along an identifier map and `mergeItems` does so along a redirect table. Proved: the renaming is a sound alignment, so **no derived fact is lost** — derived `subclass of` and `instance of` facts, classhood and metaclasshood all transport, and merged identifiers become interchangeable. Validity, by contrast, is **not** preserved: the fragment shows a harmless merge of a duplicate item together with three merges the validator rejects — one creating a cycle in the class hierarchy, one merging an individual with its own class, and one merging two items that are instances of disjoint classes.

- `ClassAlgebra.lean` — **`union of` (P2737) and class intersections**. `IsUnion` allows overlapping parts (unlike the existing `disjoint union of`), `IsIntersection` characterises a class as the intersection of several classes. Proved: the instances of a union are exactly the instances of its parts; a disjoint union is a union; a union of empty classes is empty; unions compose under refinement; a single-part union has the instances of that part; the instances of an intersection are exactly the items lying in every part; the intersection is the largest such class; an intersection of two disjoint classes is empty. Executable checkers `unionOk` and `interOk` are proved sound, and a worked fragment has `artist` as the union — but demonstrably *not* the disjoint union, since Michelangelo is both — of `painter` and `sculptor`, with the painter-sculptors checked to be their intersection.

The Properties table now also lists these new definitions and main theorems, all marked proved. As before, the identifiers follow Wikidata but the example fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments.

# Summary of changes for run 9c79ba0b-f775-4894-bd73-c598d442687e
I continued the Lean 4 formalisation of the Wikidata ontology, adding three parts of the data model and ontology layer that the development did not yet cover. Everything compiles with no `sorry` and uses only the standard axioms; the executable checks are machine-evaluated (`decide` / `#guard_msgs`-checked `#eval`s), and the module overview in `RequestProject/Main.lean` was updated with the new modules and runnable demonstrations.

New files, all under `RequestProject/`:

- `Ranks.lean` — **statement ranks and qualifiers**, i.e. the *truthy* fragment. A `Claim` is a statement ⟨subject, property, value⟩ carrying a rank (`preferred`, `normal`, `deprecated`) and qualifiers; values may be items, quantities, times or strings. `bestRankNat`, `isTruthy` and `truthyValues` implement Wikidata's rule that a default query returns the preferred statements if any, otherwise the normal ones, and never a deprecated one. Proved: the executable query returns exactly the truthy values; a deprecated statement is never truthy; as soon as one non-deprecated statement is present something is truthy, so ranks never hide all the data; the two clauses of the rank rule, each as an exact characterisation; truthiness depends only on subject, property and rank, not on the value or the qualifiers; adding a deprecated statement changes nothing visible, while adding a preferred one hides every previously visible value; and the truthy item-valued statements feed the existing property engine, so its ontology theorems apply to them. A worked fragment (Berlin's population at three ranks, with `point in time` qualifiers, plus item-valued statements) is checked by evaluation, including the variant where the preferred statement is demoted.

- `DisjointUnion.lean` — **`disjoint union of` (P2738)**. `IsDisjointUnion O c Part` says a class is partitioned by subclasses (each part a subclass, no shared instances, full coverage). Proved: every instance lies in exactly one part, so one may reason by cases; the instances of the whole are exactly those of the parts; two parts with a common instance coincide; the class is empty when all parts are; a part equal to the whole leaves the others empty; a subclass avoiding all parts is empty; partitions compose under refinement; and declared disjointness plus coverage yields a partition. An executable checker `KB.dunOk` is proved sound against the abstract notion, and a worked fragment (animal split into vertebrate and invertebrate) is checked, used for a case analysis, and shown to be rejected both when a case is missing and when two parts overlap.

- `Alignment.lean` — **`equivalent class` (P1709)**: alignment with external ontologies. An `Alignment` maps asserted statements of one ontology to derived facts of another. Proved: the derived subclass and instance relations transfer; having instances, being a class and being a metaclass transfer; the level step between an instance and its class is preserved; alignments include the identity and compose; a conservative alignment transports the hierarchy in both directions; and disjointness declared in the external ontology can be imported. The executable checker `KB.alignOk` on a finite link table is proved sound, and a worked example aligns a Wikidata fragment into an external ontology with different identifiers, transports a derived fact along it, and shows a wrong link table being rejected.

The Properties table lists the new definitions and the main theorems, all marked proved. As before, the identifiers follow Wikidata but the example fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments.

# Summary of changes for run 21d0aead-ba4c-4c34-aef2-0f3a294770ac
I continued ingesting the Wikidata ontology into Lean 4, extending the existing formalisation with the **property layer** and two substantial new ontology fragments. Everything compiles with no `sorry` and uses only the standard axioms.

New files (all under `RequestProject/`):

- `Properties.lean` — the abstract property layer. A `Wikidata.PropertyLayer` records statements ⟨subject, property, value⟩, `subproperty of` (P1647) declarations, properties declared transitive (Q18647515) or symmetric (Q18647518), and `inverse property` (P1696) pairs; the derived statement relation `Holds` is defined as the least relation containing the asserted statements and closed under those rules. Proved: statements are inherited upwards along the property hierarchy; inverse properties are the same statements read backwards; symmetric properties hold both ways; transitive properties are already transitively closed; and `Holds` is minimal (nothing is derived that is not forced). It also models the type (Q21503250) and value-type (Q21510865) constraints, with the propagation results: constraints apply to all subproperties and to superclasses of the constraining class, the subject constraint of a property is a value constraint for its inverse, and a property whose subject and value types are disjoint classes never relates an item to itself.

- `PropertyEngine.lean` — the executable counterpart, `Wikidata.PKB`: a finite property layer over a knowledge base, with computable queries (`isSubPropertyOf`, `supportsB`, `relatedB`, `valuesOf`, `subjectsOf`) and a validator `pvalid` covering the property constraints. These are certified: `isSubPropertyOf` decides exactly the closure of the P1647 statements; everything the engine computes is derivable (soundness); and for layers without symmetry or inverse declarations whose transitivity is inherited upwards it computes *exactly* the derivable statements (completeness). A validated base satisfies its type and value-type constraints in the abstract model.

- `PropertyConstraints.lean` — the single-value (Q19474404), distinct-values (Q21502410) and irreflexive (Q21510863) constraints, with certified executable checks, plus the theorem that an irreflexive transitive property is asymmetric and acyclic, hence a strict order.

- `UpperOntology.lean` — a larger ingested fragment: the upper class hierarchy (entity, object, concrete/abstract object, person, human, painting, geographic region, administrative territorial entity), the metaclass tower (first-order class, second-order class, "organisms known by a particular common name"), individuals, and three property layers: meronomy (`part of` P361 with `located in the administrative territorial entity` P131 as a transitive subproperty), the social layer (`spouse` P26, `relative` P1038, `different from` P1889, `has part(s)` P527 as inverse of P361) and `capital` (P36). Machine-checked results include: everything passes the validator; London is derived to be part of Europe through a mixed P131/P361 chain, while it is *not* derived to be located in the administrative territorial entity Europe; `part of` is irreflexive, asymmetric and acyclic on the fragment; `capital` is single-valued and distinct-valued; symmetry and the inverse pair behave as expected; and a statement violating a type constraint is rejected. A final section formalises why the Wikidata item `class` cannot be strictly stratified — classes with a common superclass sit at the same metaclass level, so no ontology can generalise first-order and second-order classes under one class — with the validator rejecting such a knowledge base and the stratified per-level replacement shown to work.

- `Taxonomy.lean` — a second domain: taxa ordered by `parent taxon` (P171, transitive) with their `taxon rank` (P105). The whole ancestry of the lion up to Animalia is derived from the individual parent statements; rank is shown *not* to be inherited from the parent taxon; `parent taxon` is irreflexive and acyclic (a strict order on the taxa); each taxon has at most one rank; and taxa and ranks are provably disjoint.

`Reachability.lean` gained a general reachability decision lemma reused by the new engine, and `Main.lean` was updated with the module overview and runnable demonstrations. The identifiers follow Wikidata, but the fragments are stylised excerpts rather than dumps; the theorems about them are statements about those fragments.

# Summary of changes for run 54add490-a780-428b-813a-c808ce00d503
I formalised the Wikidata ontology layer in Lean 4, in the abstract-axiomatic style you chose, including metaclass levels and disjointness — and made it **executable**, so an ontology can be run, validated, and can carry and reason about itself and other ontologies. Everything compiles with no `sorry` and uses only the standard axioms.

**What is in the project** (all under `RequestProject/`):

- `Core.lean` — the abstract model. A `Wikidata.Ontology` consists of items with direct `instance of` (P31) and `subclass of` (P279) statements plus a metaclass level (0 = individuals, 1 = classes, 2 = metaclasses, …), subject to: an instance sits one level below its class; subclass statements preserve level and only relate classes; the class hierarchy is antisymmetric. Derived `subclass of` is the reflexive–transitive closure of P279, derived `instance of` is P31 followed by P279 steps. Proved: the class hierarchy is a partial order; inheritance (an instance of a class is an instance of all its superclasses); `instance of` is acyclic (nothing is an instance of itself, along chains of any length); a class is never a subclass of its own instance; individuals have no instances and no subclasses; metaclasses live at level ≥ 2 and their instances are classes. Disjointness is added as an extension: disjoint classes share no instance, disjointness is inherited by subclasses, a class with instances is not a subclass of a class disjoint from it, and a self-disjoint class is empty.

- `Reachability.lean` — a certified, executable finite-graph saturation procedure (soundness *and* completeness with respect to `Relation.ReflTransGen`), the engine behind the subclass closure.

- `Engine.lean` — `Wikidata.KB`, a finite fully computable ontology (items, level table, P279/P31/disjointness statements) with computable queries `isSubclassOf`, `isInstanceOf`, `classesOf`, `instancesOf`, `isMetaclassB`, … and a validator `valid` (well-formedness, level discipline, acyclicity, disjointness). These are *certified*: the Boolean checks are proved to decide exactly the abstract derived relations, and any knowledge base passing `valid` is turned into an abstract `Ontology` (and `WithDisjointness`), so every theorem of `Core` applies to it.

- `Merge.lean` — reasoning about other ontologies: `merge` (import) and the computable `Entails` check. Proved: entailing another ontology's asserted statements automatically transfers all of its *derived* facts; entailment is reflexive and transitive; a merge entails both parts, so importing loses no knowledge. Validity, by contrast, is not automatic under import — and that is demonstrated by example.

- `SelfDescription.lean` — self-reference. Identifiers can name an ontology, name another item at the meta level, and name "the class of all items of level n". `selfDescription kb` builds the meta-ontology of any knowledge base: an item denoting the ontology itself, a meta-level name for each item classified by its level, and the tower `lvl n` instance of `lvl (n+1)`. Main theorem: **the meta-description of any knowledge base is valid** — hence a meta-description of a meta-description is too, at any depth. Also proved: the meta-ontology knows the ontology it describes, classifies each item by level, and its level classes are genuine metaclasses in the abstract sense.

- `Examples.lean` — a worked Wikidata fragment (Douglas Adams / human / person / entity, the metaclass "organisms known by a particular common name", film) that passes every check, with inherited facts computed; a machine-checked witness that `instance of` is **not** transitive; validator rejections of wrong metaclass levels, of a class-hierarchy cycle, and of a violated disjointness declaration; a consistent import of a second ontology; two individually valid ontologies whose merge is rejected; and a single ontology carrying the meta-descriptions of two different ontologies at once.

- `Main.lean` — an overview of the modules plus a few runnable demonstrations.

Note on the examples: the identifiers follow Wikidata, but the fragment is a stylised excerpt, not a faithful dump; the theorems about it are statements about that fragment.
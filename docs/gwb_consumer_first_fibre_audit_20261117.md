# GWB: consumer-first SLR/SensibLaw/Agda/Lean convergence (17 November 2026)

Source: Wikipedia revision 1385850169; SHA-256 a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233.

## Existing owners: no new NLP or temporal algebra

* Golden Agda: DASHI/Core/ConsumerDescentMinimalObserverExact.agda,
  DASHI/Reasoning/SemanticConsumerRelativeClosureExact.agda,
  DASHI/Reasoning/AdaptiveSemanticReasoningLoopExact.agda,
  DASHI/Interop/SLRConsumerRequirementV2Exact.agda and
  DASHI/Interop/SLRGWBHeterogeneousChronologyCapstoneExact.agda.
* SLR Rust: crates/sl-consumer-residual provides typed SLRC v2 PNF-fragment
  versus evidence-coordinate needs; crates/sl-semantic-admission requires
  external resolution authority for semantic promotion. Neither substitutes
  an extracted predicate for occurrence truth.
* SensibLaw: src/policy/entity_resolution.py already owns P0b mention licensing,
  candidate/recurrence/coreference, local typing, PartialPNF and demands.
  src/pnf/semantic_fibres.py and integrated_semantic_producer.py own alternative
  fibres and joins. src/storage/postgres/consumer_sufficient_runtime_store.py
  owns consumer-specific H3/H6/H9 closure, residuals, revisions and reopening.
* ITIR-suite CHANGELOG.md and generic_world_model_compiler_convergence_20260716.md
  require a single generic compiler with GWB as a fixture, not a separate
  GWB-world semantic method.
* StatiBaker LOSS_PROFILES.md, TIME_HYGIENE.md and QUERY_SURFACE.md govern
  read-only observed timeline/carryover and explicitly lossy compression;
  they do not prove event identities or article truth.
* JMD Lean: RequestProject/Slr/DocumentQuerySound.lean has the conditional
  source-query factorization/consumer-closure theorem. Q207 KB query
  consequences remain independent of interpreting the Wikipedia article.

## SufficientConsumer(o,q) is query-specific

An observer O is sufficient for a query q when any two source/semantic states
with the same O have the SAME q answer. Equivalently, q factors through O.
This does NOT require all admissible readings to coincide. If two live
readings yield different q answers, the resulting collision names the
particular discriminator/residual. No mention-licence or parser success flag
by itself pays this universal obligation.

| Consumer | Adequate observer / required fibre distinctions | GWB supplied-record state |
|---|---|---|
| Source substring at span | Revision/digest, exact span/token surface | Exact source-backed token record |
| Name-shaped mentions | POS token lattice, recoverable spans, P0b mention licence | Canonical P0b code exists; direct replay adapter implemented, owner run pending |
| Which mentioned entities are people | Name/mention fibre plus person-vs-organisation type and permitted referent grouping | OPEN: NER absent from uploaded record; PROPN does not imply PERSON |
| Direct syntactic actor/patient candidates | Original predicate/head/dep edges and sentence span | Structural evidence available; not resolved semantic actor |
| Who did what (article-asserted) | PartialPNF roles, scoped assertion, alternatives/coreference or invariant answer across live readings | OPEN for unique referents; a set-valued query might close sooner |
| Four-digit years mentioned | Exact year source offsets and original parser-token coverage | 311 recoverable occurrences; no event date claim |
| When did event e occur according to source | Event/temporal attachment, reference, attribution and scope fibre | OPEN. Same sentence date is not attachment |
| Text order of candidate predicates | Source offsets and retained candidate IDs | 1467 adjacency edges; not event chronology |
| Account-relative order of events | Licensed temporal edges, event identity and same account/consistent scope | OPEN pending S28 H6 scoped evidence |
| What claims does article attribute | Modality, content clause, negation and reporting-source scope | Candidate clauses available; licensed semantic interpretation OPEN |
| Did an event happen in the world | Admitted occurrence evidence independent from parser and Wikidata co-mention | OPEN |
| Page/paragraph summary for q | Exactly those fibres and provenance needed to preserve q under hierarchical fusion | Generic Agda proof exists; concrete q instantiation OPEN |

SLRC v2 has two requirement classes. PNF fragments can be discharged by
matching PNF evidence. Source identity, same-object, authority, classification
and other substantive evidence coordinates cannot be discharged by parser
fragments. The consumer-specific H3/H6/H9 scheduler owns admission/reopening,
not the GWB text runner.

## Concrete GWB discriminator

In the 2003 Iraq sentence, original SLR tokens contain distinct dependent
predicates for ordered, citing, possessed and had. A consumer asking whether
the article *includes a claim about WMD possession* can have the same answer
across two live world interpretations (WMD present / WMD absent).
A consumer asking whether Iraq *actually possessed WMD* differs between those
interpretations, so the latter query cannot factor through that observation.
The parser still needs its reporting-scope semantics licensed to establish
the former query beyond the literal substring question.

In 'Bush married Laura Welch ... in 1977', the source year, married predicate,
and Bush/Welch dependency roles are observed. A consumer asking for the year
string closes before a consumer asking for an EVENT date: the 'in 1977'
temporal attachment must be retained and licensed first.

## This cut: direct existing-runtime reuse

tools/slr_existing_mention_fibre_handoff.py validates the uploaded SLR
source/text/token/dependency coordinates, then calls the EXISTING
SensibLaw build_mention_licensing_carrier(parsed_document=..., tokens=...).
No second spaCy parse, named-entity decision, new fibre algebra, or
identity promotion. A P0b carrier is not a query-specific semantic proof.

Run standalone from dashi_lean4:

    python3 tools/slr_existing_mention_fibre_handoff.py
      --source-text /path/to/article.txt
      --slr-record /path/to/slr-record.json
      --sensiblaw-root /path/to/SensibLaw
      --output /path/to/sensiblaw-p0b-mention-licences.json

Or during existing replay:

    SENSIBLAW_ROOT=/path/to/SensibLaw
      bash scripts/replay_gwb_article_from_files.sh /path/to/saved /path/to/out

## Remaining precise acceptance

1. Run P0b handoff with the canonical SensibLaw checkout and inspect exact
   mention/recurrence licences. The local wrapper alone has not run P0b.
2. Instantiate the existing PartialPNF and typed subject/demand constructors
   on this revision-pinned source for each requested query, not all possible
   document facts.
3. Compile SLRC v2 typed consumer requirements from those named queries,
   retaining PNF fragment and independent evidence-coordinate demands.
4. Run existing consumer-specific H3 -> H6 -> H9, record closure OR a pair
   of disagreeing live readings and a targeted discriminator; do not
   globally force identity convergence or a unique timeline.
5. Feed an actual reviewed/admitted semantic licence and fibre closure
   to JMD SourceQueryLicence; validate article query against the exact
   source revision and prover demand, not Q207 KB alone.
6. Instantiate q-indexed sentence->paragraph->article fusion (Agda golden)
   and check Lean with the repo's exact toolchain. The root lean-toolchain
   pins 4.35.0-rc3 while DASHI/output-final_aristotle/lean-toolchain
   pins 4.28.0: resolve the project build context before claiming a pass.

Local wrapper exercise on the provided 643-sentence, 17547-token GWB record:
original source/heads/coordinates pass, 7/7 deliberate tampering cases reject.
Canonical SensibLaw runtime and JMD Lean kernel are NOT tested here.

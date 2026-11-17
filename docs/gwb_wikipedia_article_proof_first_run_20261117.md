# First real GWB Wikipedia article proof run (SLR → JMD Lean)

**Target:** https://en.wikipedia.org/wiki/George_W._Bush ; page item Q207.
**Status:** source code written, not yet live-run/Lean kernel verified in this environment.

## What it actually does

1. Fetches the main English Wikipedia page with the MediaWiki parse API,
   saving the exact revision ID, returned HTML, extracted narrative plaintext,
   source text SHA-256 and section offsets.
2. Calls the **existing** `dashi_agda/tools/slr-discourse-reconstruct/
   slr_source_unit_pnf_batch.py` trained spaCy sentence/dependency producer.
   The generic producer was extended to retain its original PERSON/DATE/TIME
   NER spans as candidate-only observations (no identity or truth promotion).
3. Projects **existing SLR dependency rows** into syntactic action candidates
   (predicate, direct actor/patient dependencies), PERSON mentions, temporal
   expressions, year-index candidates and literal source-text order.
   Every association is explicitly a candidate. This is **not** a new NLP parser.
4. Executes `RequestProject.Slr.ArticleProof.verifyFiles` in JMD Lean,
   independently checking that event tokens and dependencies are actually
   present in the original SLR record, PERSON/DATE spans match the source,
   and the source text digest matches both SLR and the projection.
5. Runs JMD's existing **Q207 Wikidata getter**, its original `cmdLean`
   ontology-code generator with `--kernel`, calls `lake env lean` on the
   generated proof module, then runs JMD's original English Wikipedia
   `cmdScan` to collect article links/sources. **This JMD scan fetches an
   independent page snapshot and is not certified to share the pinned article
   revision used by the SLR source-unit producer.**

## Requirements

- `dashi_lean4` and `dashi_agda` repositories side by side, on exact heads
  containing this programme. `DASHI_AGDA_ROOT` overrides the latter path.
- `lake`/Lean pinned by the current `lean-toolchain` and `lakefile.toml`.
- `python3`, `sha256sum`, network access to en.wikipedia.org and wikidata.org.
- Python packages `spacy` and `beautifulsoup4`; trained English model:

```bash
python3 -m pip install spacy beautifulsoup4
python3 -m spacy download en_core_web_sm
```

## One-command run

From the root of `dashi_lean4`:

```bash
bash scripts/run_gwb_article_proof.sh
```

For other checkout layouts:

```bash
DASHI_AGDA_ROOT=/path/to/dashi_agda \
GWB_ARTICLE_OUT=/path/to/results \
bash scripts/run_gwb_article_proof.sh
```

## Replay the uploaded first-run evidence without spaCy

The initial real GWB record (enwiki revision `1385850169`) omitted
`named_entities`, causing its original PERSON and DATE summary fields to
remain empty even though the SLR dependency observations were sound.
The repaired pipeline **does not pretend** the missing NER field exists:
it separately emits parser-backed proper-noun tokens and literal four-digit
year spans. To continue into JMD Lean using the existing exact source:

```bash
# Directory contains article.txt, article.html and slr-record.json
bash scripts/replay_gwb_article_from_files.sh \
  /path/to/saved-gwb /path/to/gwb-replay
```

The saved HTML must reconstruct byte-for-byte the same article plaintext.
This preserves the original article section/paragraph boundaries rather
than replacing them with one synthetic paragraph. On the uploaded fixture,
there are **225 blocks (63 headings, 162 paragraphs)**, 643 SLR sentences,
2,620 proper-noun tokens and 311 literal-year matches. NER PERSON/DATE
claims remain unavailable until the updated trained SLR producer reruns.

The script validates the saved source, builds the JMD Wikidata executable,
checks the article parser observations in Lean, then fetches Q207 and
kernel-checks its independent ontology proof module. A JMD link scan is
still a separate live snapshot and is **not** thereby proven to have the
source revision's exact HTML.

## Troubleshooting and staged reruns

```bash
# Check Python projection/negative controls without model or network:
python3 tools/gwb_article_proof.py --self-check

# Run article acquisition + original SLR parser by itself:
python3 tools/gwb_article_proof.py \
  --agda-root ../dashi_agda --output-dir .gwb_article_proof

# Reopen article and original SLR evidence in JMD Lean without re-fetching:
lake exe wikidata gwb-article-check \
  .gwb_article_proof/article.txt \
  .gwb_article_proof/slr-record.json \
  .gwb_article_proof/article-candidates.json

# Replay a pinned revision (oldid) on the Python step:
python3 tools/gwb_article_proof.py \
  --agda-root ../dashi_agda --output-dir .gwb_article_proof \
  --revision REVID
```

Outputs under `.gwb_article_proof` include:

| Output | Content |
|---|---|
| `article.txt`, `article.html` | Saved page body and original HTML response |
| `slr-source-units.jsonl`, `slr-record.json` | Original SLR source-unit/PNF output |
| `article-candidates.json` | Mention/action/time/year/text-order candidate coordinates |
| `summary.md` | Compact first values and uncertainty notes |
| `gwb-q207.wdkb` | Existing JMD Wikidata Q207 ontology projection |
| `GwbArticleQ207Proof.lean` | JMD-generated theorem module, actually checked with `lake env lean` |
| `gwb-q207.scan` | JMD's existing linked-article/citation scan |

## Interpreting the output correctly

**Proved by the first-run Lean checker:** original SLR parser rows support
each emitted dependency-based role; emitted spans are exact substrings of
the saved Wikipedia revision; DATE/PERSON mentions are traceable to the
same trained-spaCy output; text-order edges correspond to source offsets.
The generated JMD ontology theorem separately proves consequences *of Q207
KB contents*, not the natural-language events in the article.

**Not proved:** that a parser-dependent actor is a fully resolved human;
that a predicate's source asserted occurrence; pronoun coreference; that
a DATE phrase timestamps a specific event; that source text order is world
event order; or that a Wikipedia assertion is historically correct.

A model cannot promote these by returning `kernel-certified` or `true`.
That is exactly the next semantic-licensing cut after examining real rows.

## First review queries after a successful run

- Which PERSON NER surfaces are mentioned and at what exact spans?
- Which original `nsubj`/`dobj`-connected action candidates mention Bush?
- Which DATE mentions appear, and which event candidates share sentences?
- How does the year-index order differ from source-text order?
- Which actor roles are unresolved, and which extracted clauses are embedded?
- Which candidates would change if identity, negation, modality, or attribution
  were considered? Preserve those fibres; do not claim automatic admission.

## Local verification boundary

The local working environment lacks trained `en_core_web_sm`, `lake`,
`lean`, and `cargo`. The Python runner includes `--self-check` with
adversarial source/head/span/promotion controls, but an actual live
Wikipedia→spaCy→Lean run must be performed on the pinned development machine.
Run the command above and use its real output as the basis of the next
semantic licence and chronology lemmas. Do not replace it with example facts.

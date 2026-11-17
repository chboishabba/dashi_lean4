# First real George W. Bush Wikipedia source/SLR values

## Exact source

- enwiki revision: **1385850169**
- source text SHA-256: `a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233`
- original SLR `en_core_web_sm` parser: **643 sentences / 17,547 tokens**
- original SLR parser receipt reports spaCy **3.8.18**
- original HTML-to-text structural projection: **225 blocks**, including
  **63 headings and 162 paragraphs**. Full reconstructed HTML plaintext
  exactly matches the uploaded 93,577-character source text.
- original source/PNF candidate stream: 643 candidate records
- computed direct role/action projection: **1,468 event/action candidates**
- **990** have a direct actor dependency, **767** a direct patient dependency;
  this is not referent resolution or semantic event identification
- **1,467** direct source-text ordering edges; NOT 1,467 event-chronology edges
- **52** SLR sentences flagged negated; **40** projected predicates have an
  immediate negation dependency. These differ because negation scope isn't
  yet resolved in the projection.

## Root cause found in supplied artifact

The uploaded `slr-record.json` from this source revision did **not** contain
`named_entities`. The first runner used `record.get('named_entities', [])`,
silently treating the absent NER field as an empty NER observation list.
Consequently the summary had **0 PERSON, 0 DATE/TIME and 0 timeline entries**.
This is missing output evidence, not a claim that the article lacks names
or dates. The newer `dashi_agda` source-unit producer now emits exact spaCy
NER spans; the first record was produced by an older checkout or older producer.

## Source-backed recovery without re-parsing

The repaired GWB runner works directly from the original stored SLR
dependency rows. It adds separate lexical carriers:

- **2,620** `pos=PROPN` token occurrences, each carrying its source span
  and original parser-dependency coordinate. These are **not PERSON NER**.
- **311** four-digit year mentions, each an exact source substring within
  an original spaCy token. This includes embedded years in compound tokens
  such as `1995–2000` and `2004–2005`.
- **311** year-index entries with co-sentential candidate event references.
  These remain **lexical co-occurrences**, not dates of admitted events.

The Lean checker now allows an explicitly absent NER field, rejects its
unacknowledged absence, and checks the proper-noun and lexical-year carriers
against exact source spans and original parser tokens.

## Replay this user's saved run, rather than re-fetching or re-parsing

Check out fresh heads of `chboishabba/dashi_lean4` and
`chboishabba/dashi_agda`. Put the supplied `article.txt` and
`slr-record.json` in one directory, then from `dashi_lean4`:

```bash
bash scripts/replay_gwb_article_from_files.sh /path/to/saved-gwb /path/to/gwb-replay
```

This performs: (1) model-free Python checks, (2) source-bound lexical and
dependency replay, (3) `lake build wikidata`, (4) JMD Lean source evidence
check, (5) JMD original Wikidata Q207 fetch + KB theorem generation and
real `lake env lean` proof-module checking, (6) JMD's independent Wikipedia
link/source scan. No spaCy model or Wikipedia article download is needed
for the SLR source/PNF part of replay. Q207 and JMD scan still require
network or cached results.

For a fresh actual PERSON/DATE NER run, pull the updated `dashi_agda` and
rerun `bash scripts/run_gwb_article_proof.sh` with `en_core_web_sm` installed.

## Current proof boundary

- Independently inspected uploaded source and all 643 sentence digests,
  17,547 token spans/head IDs: **zero mismatches**.
- A separate local Python replay checked 1,468 events and 1,467 source order
  edges and produced the lexical candidates described above.
- A separate local source-hierarchy audit passed **7/7** tests:
  exact paragraph/heading coverage and six adversarial boundary changes
  (gaps, overlaps, wrong headings, missing last block, forged kinds).
- A local baseline and ten adversarial cases rejected altered source hash,
  source revision, sentence hash, token head/surface, actor, text order and
  promotion flags.
- **No JMD `.wdkb`, `.scan`, generated Lean proof module or console log**
  was present among the uploaded artifacts. Therefore end-to-end JMD
  kernel execution has *not* been verified from this particular run.
- No arbitrary-language semantic admission, event identity, temporal edge
  admission, person coreference or historical truth theorem is claimed.

## High-alpha first semantic licence targets from actual values

1. `nsubj=Bush`, predicate `married`, direct patient token `Welch` in the
   sentence mentioning **1977**; resolve full name `Laura Welch` from
   source-bound compound/modifier dependencies, then test actor identity.
2. Predicate `ordered` with `invasion` as object and a **2003** year mention;
   prove date attachment and source assertion separately.
3. Embedded **'claims that it possessed weapons of mass destruction'**;
   avoid promoting nested claimed event content to historical occurrence.
4. **2001–2009** and **1995–2000** year ranges; recover interval semantics
   rather than producing two unqualified occurrences.
5. Explicit denials, corrections and disputed accounts; join only within
   compatible attribution and temporal scope.

Use the parser-backed real values before adding any new abstract carriers.

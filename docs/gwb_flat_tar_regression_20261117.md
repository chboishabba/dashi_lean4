# Exact flat GWB archive regression — 17 November 2026

Archive SHA-256: 6bbad0f9bcc2f0aa2e0e6f77f15692a945c1331a6337cfe202c19a58e2460f9e.
MediaWiki source revision: enwiki-revid:1385850169.

## Locally executed invariants

Direct archive extraction and independent source/PNF/P0b checks returned **zero invariant violations**.

| Source/observation invariant | Verified value |
|---|---:|
| Unicode source characters | 93,577 |
| Exact source/sentence digests | 643 sentences |
| Source-matching token spans, dependency heads | 17,547 |
| Event candidates regenerated from original predicates/roles/negation | 1,468 |
| Adjacent source-text order edges | 1,467 |
| Literal year spans within original tokens | 311 |
| Proper-noun parser tokens | 2,620 |
| Complete heading/paragraph source partition | 225 = 63 + 162 |
| P0b candidate-only licences | 16,034 |
| P0b source-matching, token-aligned materialised mentions | 11,975 |
| P0b suppressed token spans | 6,162 |
| Orphan P0b licences | 0 |

Breakdown of P0b licences: lexical_token 11,385; eventuality_annotation
2,197; named_entity_shape 1,786; numeric_literal 666.
Event candidate scope tags: unresolved-source-assertion 753;
unresolved-embedded-clause 715. Not an accepted semantic distinction.

## Critical canonical hash distinction

SLR hashes the raw UTF-8 article text:
a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233.
By contrast, SensibLaw P0b canonical_text_sha256 is
c1ae7a8b93b70050f27b64524211d624e3053b1b59f28491ca3db45320c985a1.
This TAR was created with a **legacy bug**: P0b used
_entity_resolution._canonical_digest(text), which hashes JSON-encoded text
instead of the raw UTF-8 source. Both digests reproduce from this historical
archive, but **only the raw UTF-8 digest is the correct source identity**.
After JSON transport is decoded, hashing its text bytes must equal SLR.

SensibLaw PR #515 corrects P0b and expansion source hashing to the raw
UTF-8 digest. Do not rewrite old carrier IDs in place: the historical
P0b record must be reissued from the same underlying source and parser
observations. The archive auditor reports its legacy hash explicitly
and rejects pretending it already follows the new canonical policy.

## Mutation regressions

Ten locally mutated checks rejected altered: source hash, sentence hash,
dependency head, token surface, event actor, event occurrence promotion,
year, article section, P0b mention text and P0b canonical hash.

## What the TAR cannot verify

The archive's original record reports parser_backend=spacy-trained,
model=en_core_web_sm, version=3.8.11, producer ABI
sensiblaw-integrated-semantic-producer-compatible-v1.
It is not an SLR Rust DB-native M12 receipt and contains no original
PostgreSQL parser-run/region, reviewed S28 event join, kernel log or
admitted consumer-relative semantic fibre.

Accordingly the TAR verifies text-bound parser/P0b candidate consistency,
not reviewed person identity, semantic actor status, event date attachment,
historical event occurrence or actual JMD kernel query closure.

The missing named_entities field explains zero original PERSON/DATE NER
rows. P0b named_entity_shape is a separate candidate licence type and
is not proof that the missing trained NER field existed.

## Repeat without invoking any producer

    python3 tools/audit_gwb_flat_archive.py gwb_article_proof.tar --json

The read-only Python standard-library code is an **auditor only**;
the production path is SLR Rust M12/S28 plus the existing typed
consumer-relative fibre machinery and JMD Lean. To compare source
observations to the Rust implementation, the exact original DB-native
run must be executed and its genuine receipts compared; do not invent IDs.

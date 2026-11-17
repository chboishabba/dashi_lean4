#!/usr/bin/env python3
"""Pass exact SLR parser observations to SensibLaw's canonical P0b carrier.

This is an interoperability adapter, NOT a mention detector, identity
resolver, temporal reasoner or a new semantic-fibre algebra. The actual owner
is SensibLaw/src/policy/entity_resolution.py:
  build_mention_licensing_carrier(parsed_document=..., tokens=...).

The supplied SLR document is validated against its original source and
parser heads. No spaCy model is loaded, no string matching promotes an entity,
and no claim/event truth is inferred.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import sys


def source_parser_replay(text: str, record: dict) -> tuple[dict, tuple]:
    """Repackage original tokens into the existing SensibLaw adapter contract."""
    sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
    manifest = record["manifestation"]
    if manifest.get("source_text_sha256") != sha:
        raise ValueError("source revision content hash differs from SLR manifest")
    if manifest.get("revision_ref") != record.get("revision_ref"):
        raise ValueError("source revision mismatch")
    if record.get("candidate_only") is not True or record.get("semantic_promotion") is not False:
        raise ValueError("parser result attempts semantic promotion")
    if record.get("parser_receipt", {}).get("dependency_capable") is not True:
        raise ValueError("requires the original dependency-capable parser")
    if manifest.get("character_count") != len(text):
        raise ValueError("source character count mismatch")

    sentences = []
    tokens = []
    ordinals = set()
    for sentence in record["pnf_candidates"]:
        a, b = int(sentence["source_span_start"]), int(sentence["source_span_end"])
        if not 0 <= a < b <= len(text):
            raise ValueError("out-of-range original sentence")
        if hashlib.sha256(text[a:b].encode("utf-8")).hexdigest() != sentence["sentence_text_sha256"]:
            raise ValueError("source sentence changed after parser run")
        if sentence.get("candidate_only") is not True or sentence.get("semantic_promotion") is not False:
            raise ValueError("promoted sentence candidate")
        rows = sentence["dependency_rows"]
        heads = {int(row["i"]) for row in rows}
        if len(heads) != len(rows):
            raise ValueError("duplicate original token ordinal")
        parsed_tokens = []
        for row in rows:
            start = int(row["idx"])
            surface = str(row["text"])
            end = start + len(surface)
            if not a <= start < end <= b or text[start:end] != surface:
                raise ValueError("token surface not supported by original source")
            if int(row["head_i"]) not in heads:
                raise ValueError("unresolved original dependency head")
            if (start, end) in ordinals:
                raise ValueError("duplicate source token interval")
            ordinals.add((start, end))
            parsed_tokens.append({
                "text": surface, "start": start, "end": end,
                "pos": row["pos"], "tag": row.get("tag", ""),
                "dep": row["dep"], "lemma": row["lemma"],
            })
            tokens.append((surface, start, end))
        sentences.append({"tokens": parsed_tokens})

    tokens.sort(key=lambda row: (row[1], row[2]))
    if any(a[2] > b[1] for a, b in zip(tokens, tokens[1:])):
        raise ValueError("overlapping original parser token intervals")
    if len(tokens) != record["parser_receipt"].get("token_count"):
        raise ValueError("original token count mismatch")
    if len(sentences) != record["parser_receipt"].get("sentence_count"):
        raise ValueError("original sentence count mismatch")
    return {"text": text, "sents": sentences}, tuple(tokens)


def handoff(*, source_text: Path, slr_record: Path, sensiblaw_root: Path,
            output: Path) -> dict:
    text = source_text.read_text(encoding="utf-8")
    record = json.loads(slr_record.read_text(encoding="utf-8"))
    parsed, tokens = source_parser_replay(text, record)
    root = sensiblaw_root.resolve()
    if not (root / "src/policy/entity_resolution.py").is_file():
        raise FileNotFoundError("canonical SensibLaw entity_resolution.py missing")
    # No parser call: pass the source's ORIGINAL token carrier explicitly.
    sys.path.insert(0, str(root))
    from src.policy.entity_resolution import build_mention_licensing_carrier

    carrier = build_mention_licensing_carrier(
        canonical_text=text,
        source_ref=record["source_unit_ref"],
        document_ref=record["parser_receipt"]["document_ref"],
        context_refs=(record["revision_ref"],),
        parsed_document=parsed,
        tokens=tokens,
    )
    if carrier["authority"] != "candidate_only":
        raise ValueError("mention carrier changed authority")
    if any(carrier.get(k) != "none" for k in
           ("resolution_effect", "promotion_effect", "execution_effect")):
        raise ValueError("mention carrier attempted resolution/promotion/execution")
    if carrier["lattice"]["token_count"] != len(tokens):
        raise ValueError("SensibLaw token lattice does not match supplied SLR tokens")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(carrier, sort_keys=True, indent=2) + "\n",
                      encoding="utf-8")
    return {"source_revision": record["revision_ref"],
            "source_sha256": record["manifestation"]["source_text_sha256"],
            "original_tokens": len(tokens),
            "original_sentences": len(parsed["sents"]),
            "sensiblaw_carrier_ref": carrier["carrier_ref"],
            "summary": carrier["summary"],
            "resolution_effect": "none",
            "semantic_consumer_sufficient": False,
            "note": "P0b mention licence is not consumer-relative semantic closure"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-text", type=Path, required=True)
    parser.add_argument("--slr-record", type=Path, required=True)
    parser.add_argument("--sensiblaw-root", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(handoff(source_text=args.source_text,
                             slr_record=args.slr_record,
                             sensiblaw_root=args.sensiblaw_root,
                             output=args.output), sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

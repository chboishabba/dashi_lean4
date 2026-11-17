"""Exact-source SLR -> existing SensibLaw P0b adapter tests.

These tests verify source/parser reconstruction WITHOUT reloading spaCy or
pretending a P0b mention candidate pays semantic/identity closure.
"""
import copy
import hashlib
import importlib.util
from pathlib import Path

import pytest

MODULE_PATH = Path(__file__).resolve().parents[1] / "slr_existing_mention_fibre_handoff.py"
spec = importlib.util.spec_from_file_location("slr_existing_mention_fibre_handoff", MODULE_PATH)
assert spec and spec.loader
adapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(adapter)


def fixture():
    text = "Bush married Laura Welch in 1977."
    def token(i, surface, dep, head, pos):
        return {"i": i, "idx": text.index(surface), "text": surface,
                "lemma": surface.lower(), "dep": dep, "head_i": head,
                "pos": pos}
    rows = [
        token(0, "Bush", "nsubj", 1, "PROPN"),
        token(1, "married", "ROOT", 1, "VERB"),
        token(2, "Laura", "compound", 3, "PROPN"),
        token(3, "Welch", "dobj", 1, "PROPN"),
        token(4, "in", "prep", 1, "ADP"),
        token(5, "1977", "pobj", 4, "NUM"),
        token(6, ".", "punct", 1, "PUNCT"),
    ]
    digest = lambda s: hashlib.sha256(s.encode("utf-8")).hexdigest()
    record = {
        "manifestation": {"source_text_sha256": digest(text),
                          "revision_ref": "enwiki-revid:fixture",
                          "character_count": len(text)},
        "revision_ref": "enwiki-revid:fixture",
        "candidate_only": True, "semantic_promotion": False,
        "parser_receipt": {"dependency_capable": True, "token_count": 7,
                           "sentence_count": 1},
        "pnf_candidates": [{
            "source_span_start": 0, "source_span_end": len(text),
            "sentence_text_sha256": digest(text),
            "candidate_only": True, "semantic_promotion": False,
            "dependency_rows": rows,
        }],
    }
    return text, record


def test_reuses_original_token_graph_without_a_parser():
    text, record = fixture()
    parsed, tokens = adapter.source_parser_replay(text, record)
    assert parsed["text"] == text
    assert len(parsed["sents"]) == 1
    assert len(tokens) == 7
    assert parsed["sents"][0]["tokens"][1]["dep"] == "ROOT"
    assert any(row[0] == "1977" for row in tokens)


@pytest.mark.parametrize("mutate", [
    lambda r: r["manifestation"].__setitem__("source_text_sha256", "0" * 64),
    lambda r: r["manifestation"].__setitem__("revision_ref", "other"),
    lambda r: r.__setitem__("semantic_promotion", True),
    lambda r: r["parser_receipt"].__setitem__("token_count", 6),
    lambda r: r["pnf_candidates"][0]["dependency_rows"][0].__setitem__("head_i", 99),
    lambda r: r["pnf_candidates"][0]["dependency_rows"][1].__setitem__("text", "called"),
    lambda r: r["pnf_candidates"][0].__setitem__("sentence_text_sha256", "0" * 64),
])
def test_rejects_forged_evidence(mutate):
    text, record = fixture()
    bad = copy.deepcopy(record)
    mutate(bad)
    with pytest.raises(ValueError):
        adapter.source_parser_replay(text, bad)

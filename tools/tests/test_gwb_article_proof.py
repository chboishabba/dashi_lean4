"""Model-free regression tests for the real GWB article SLR/JMD runner.

Run: python -m unittest discover -s tools/tests -p 'test_gwb_article_proof.py'
No trained spaCy model, network or Lean needed for these narrow tests.
"""
from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest

SCRIPT = Path(__file__).resolve().parents[1] / "gwb_article_proof.py"
spec = importlib.util.spec_from_file_location("gwb_article_proof", SCRIPT)
assert spec and spec.loader
pipeline = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pipeline)


class GwbArticleProjectionTests(unittest.TestCase):
    def test_existing_parser_projection_and_negative_controls(self):
        self.assertEqual(pipeline.self_check(), 0)

    def test_html_excludes_infobox_references_and_retains_headings(self):
        html = (
            '<div class="mw-parser-output">'
            '<table><tr><td>Fake event 1991</td></tr></table>'
            '<h2>Presidency</h2>'
            '<p>George W. Bush <sup class="reference">[2]</sup>'
            'became president in 2001.</p>'
            '<p>Later, he spoke.</p>'
            '</div>'
        )
        text, sections = pipeline.html_to_source(html)
        self.assertIn("George W. Bush", text)
        self.assertIn("2001", text)
        self.assertIn("Presidency", text)
        self.assertNotIn("Fake event 1991", text)
        self.assertNotIn("[2]", text)
        for block in sections:
            self.assertEqual(text[block["start_char"]:block["end_char"]],
                             text[block["start_char"]:block["end_char"]].strip())
        self.assertEqual(sections[0]["kind"], "heading")

    def test_old_slr_record_without_ner_still_has_parser_bound_years(self):
        text = "Bush served from 2001–2009."
        def token(i, surface, dep, head, pos):
            return {"i": i, "idx": text.index(surface), "text": surface,
                    "lemma": surface.lower(), "dep": dep,
                    "head_i": head, "pos": pos}
        record = {
            "schema": "slr-source-unit-pnf-record-v1",
            "source_unit_ref": "wikipedia:en:George_W._Bush:fixture",
            "revision_ref": "enwiki-revid:fixture",
            "manifestation": {"source_text_sha256": pipeline.digest(text)},
            "parser_receipt": {"dependency_capable": True},
            "candidate_only": True, "semantic_promotion": False,
            # Intentionally lacks named_entities: original uploaded format.
            "pnf_candidates": [{
                "claim_candidate_id": "source:fixture:event",
                "sentence_index": 0, "source_span_start": 0,
                "source_span_end": len(text),
                "sentence_text_sha256": pipeline.digest(text),
                "candidate_only": True, "semantic_promotion": False,
                "dependency_rows": [
                    token(0, "Bush", "nsubj", 1, "PROPN"),
                    token(1, "served", "ROOT", 1, "VERB"),
                    token(2, "2001–2009", "npadvmod", 1, "NUM"),
                ],
            }],
        }
        result = pipeline.derive_projection(record, text, [])
        self.assertFalse(result["ner_observations_present"])
        self.assertEqual(len(result["people_mentions"]), 0)
        self.assertEqual(len(result["literal_year_mentions"]), 2)
        self.assertEqual(len(result["timeline_candidates"]), 2)
        self.assertEqual(len(result["proper_noun_tokens"]), 1)
        self.assertEqual([y["year_candidate"] for y in result["timeline_candidates"]],
                         [2001, 2009])
        self.assertTrue(all(
            year["evidence_kind"] == "literal-year-inside-original-parser-token"
            and year["event_time_paid"] is False
            for year in result["literal_year_mentions"]
        ))

    def test_year_lexical_only(self):
        self.assertEqual(pipeline.YEAR.findall("2001 and 2009"), ["2001", "2009"])
        self.assertEqual(pipeline.YEAR.findall("circa 1962"), ["1962"])
        self.assertEqual(pipeline.YEAR.findall("19999"), [])

    def test_token_source_offsets_must_be_exact(self):
        text = "Alice called Bob."
        row = {"idx": 6, "text": "called", "i": 1, "lemma": "call",
               "dep": "ROOT", "head_i": 1, "pos": "VERB"}
        self.assertEqual(pipeline.tok_span(row, text)["surface"], "called")
        row["idx"] = 5
        with self.assertRaises(ValueError):
            pipeline.tok_span(row, text)


if __name__ == "__main__":
    unittest.main()

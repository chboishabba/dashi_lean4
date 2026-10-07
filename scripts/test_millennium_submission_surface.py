#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "ExternalClayNS" / "LeanDojoCComparatorBridge.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"


class MillenniumSubmissionSurfaceTests(unittest.TestCase):
    def test_ns_c_bridge_is_unconditional_exact_target(self):
        self.assertTrue(BRIDGE.exists(), "direct comparator-to-LeanDojo C bridge is missing")
        text = BRIDGE.read_text(encoding="utf-8")
        self.assertIn(
            "theorem leanDojoFeffermanC :\n    MillenniumNavierStokes.FeffermanC :=",
            text,
        )
        self.assertNotIn("LeanDojoCDStatementWeld", text)
        self.assertNotIn("(w :", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)

    def test_ns_frontier_can_only_be_green_from_exact_bridge(self):
        text = FRONTIER.read_text(encoding="utf-8")
        ns_start = text.index("problem := .navierStokes")
        ns_end = text.index("problem := .hodge", ns_start)
        ns = text[ns_start:ns_end]
        if "state := .greenExact" in ns:
            bridge = BRIDGE.read_text(encoding="utf-8")
            self.assertIn("#print axioms leanDojoFeffermanC", bridge)
            self.assertIn("theorem leanDojoFeffermanC :", bridge)


if __name__ == "__main__":
    unittest.main()

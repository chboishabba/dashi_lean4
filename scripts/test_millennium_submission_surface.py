#!/usr/bin/env python3
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]
BRIDGE = ROOT / "ExternalClayNS" / "LeanDojoCComparatorBridge.lean"
FRONTIER = ROOT / "MillenniumExternal" / "ExternalTargetFrontier.lean"


class MillenniumSubmissionSurfaceTests(unittest.TestCase):
    def test_ns_c_bridge_exposes_atomic_transport_frontier(self):
        self.assertTrue(BRIDGE.exists(), "direct comparator-to-LeanDojo C bridge is missing")
        text = BRIDGE.read_text(encoding="utf-8")
        for name in (
            "ComparatorInitialToLeanDojo",
            "ComparatorForceToLeanDojo",
            "LeanDojoSolutionToComparator",
            "LeanDojoCTransportFrontier",
            "leanDojoFeffermanC_of_transport",
        ):
            self.assertIn(name, text)
        self.assertNotIn("LeanDojoCDStatementWeld", text)
        self.assertNotIn("sorry", text)
        self.assertNotIn("axiom ", text)

    def test_ns_frontier_can_only_be_green_from_unconditional_exact_bridge(self):
        frontier = FRONTIER.read_text(encoding="utf-8")
        ns_start = frontier.index("problem := .navierStokes")
        ns_end = frontier.index("problem := .hodge", ns_start)
        ns = frontier[ns_start:ns_end]
        bridge = BRIDGE.read_text(encoding="utf-8")
        if "state := .greenExact" in ns:
            self.assertIn(
                "theorem leanDojoFeffermanC :\n    MillenniumNavierStokes.FeffermanC :=",
                bridge,
            )
            self.assertIn("#print axioms leanDojoFeffermanC", bridge)


if __name__ == "__main__":
    unittest.main()

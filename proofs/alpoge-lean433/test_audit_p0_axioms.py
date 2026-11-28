#!/usr/bin/env python3
"""Synthetic log fixtures, not a Lean kernel receipt."""
import unittest
from audit_p0_axioms import audit, UPSTREAM, ADAPTER, CLAY, ALLOWED


class AuditTest(unittest.TestCase):
    def test_positive(self):
        for targets in (UPSTREAM, ADAPTER, CLAY):
            for prefix in ("", "info: ", "file.lean:12:3: info: "):
                for axiom_text in ("depends on axioms: [propext, Classical.choice, Quot.sound]",
                                   "depends on axioms: [propext,\n Classical.choice, Quot.sound]",
                                   "does not depend on any axioms"):
                    with self.subTest(targets=targets, prefix=prefix, axiom_text=axiom_text):
                        log = "\r\n".join(f"{prefix}'{name}' {axiom_text}" for name in targets)
                        self.assertEqual(set(audit(log, targets)), set(targets))

    def test_negative(self):
        for targets in (UPSTREAM, ADAPTER, CLAY):
            lines = [f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
                     for name in targets]
            head, rest = lines[0], lines[1:]
            invalid = [rest, [head, head, *rest],
                       [head.replace("Quot.sound", "sorryAx"), *rest],
                       [head.replace("Quot.sound", "Custom.hypothesis"), *rest],
                       [head.replace("Quot.sound", "propext"), *rest],
                       [head.replace("Quot.sound", ""), *rest],
                       [head[:-1], *rest], ["warning: " + head, *rest],
                       [head.replace(targets[0], targets[0] + "X"), *rest],
                       [head.replace("depends on axioms:", "axioms of:"), *rest]]
            for i, bad in enumerate(invalid):
                with self.subTest(targets=targets, case=i):
                    with self.assertRaises(ValueError):
                        audit("\n".join(bad), targets)


if __name__ == "__main__":
    unittest.main()

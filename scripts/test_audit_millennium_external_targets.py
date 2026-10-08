#!/usr/bin/env python3
import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).with_name("audit_millennium_external_targets.py")


def load_module():
    spec = importlib.util.spec_from_file_location("millennium_audit", SCRIPT)
    if spec is None or spec.loader is None:
        raise RuntimeError("cannot load audit module")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GOOD = r'''
def p_versus_np : ClayProblem where
  statement_declaration := "Millennium.ClayPVersusNP"
  alternative_statement_declarations := ["Millennium.ClayPVersusNP.Formulations.NegativeBranch"]
  status := ProblemStatus.open_problem

def riemann_hypothesis : ClayProblem where
  statement_declaration := "Millennium.ClayRiemannHypothesis"
  prize_theorem_declaration := some "Millennium.clay_prize_riemann_hypothesis"
  status := ProblemStatus.open_problem

def navier_stokes : ClayProblem where
  statement_declaration := "MillenniumNavierStokes.FeffermanA"
  alternative_statement_declarations :=
    ["MillenniumNavierStokes.FeffermanB", "MillenniumNavierStokes.FeffermanC",
      "MillenniumNavierStokes.FeffermanD"]
  status := ProblemStatus.open_problem

def hodge_conjecture : ClayProblem where
  statement_declaration := "MillenniumHodge.ClayHodge"
  status := ProblemStatus.statement_incomplete

def birch_swinnerton_dyer : ClayProblem where
  statement_declaration :=
    "MillenniumBirchSwinnertonDyer.ClayBirchSwinnertonDyer"
  prize_theorem_declaration :=
    some "MillenniumBirchSwinnertonDyer.clay_prize_birch_swinnerton_dyer"
  status := ProblemStatus.open_problem

def yang_mills : ClayProblem where
  statement_declaration := "MillenniumYangMills.ClayYangMills"
  status := ProblemStatus.statement_incomplete

def poincare : ClayProblem where
  statement_declaration := "MillenniumPoincare.ClayPoincareConjecture"
  status := ProblemStatus.solved_problem
'''


class RegistryAuditTests(unittest.TestCase):
    def test_accepts_pinned_registry_surface(self):
        audit = load_module()
        audit.audit_registry_text(GOOD)

    def test_rejects_hodge_promotion_from_incomplete(self):
        audit = load_module()
        bad = GOOD.replace(
            "def hodge_conjecture : ClayProblem where\n  statement_declaration := \"MillenniumHodge.ClayHodge\"\n  status := ProblemStatus.statement_incomplete",
            "def hodge_conjecture : ClayProblem where\n  statement_declaration := \"MillenniumHodge.ClayHodge\"\n  status := ProblemStatus.open_problem",
        )
        with self.assertRaisesRegex(ValueError, "hodge_conjecture"):
            audit.audit_registry_text(bad)

    def test_rejects_missing_riemann_prize_declaration(self):
        audit = load_module()
        bad = GOOD.replace(
            '  prize_theorem_declaration := some "Millennium.clay_prize_riemann_hypothesis"\n',
            "",
        )
        with self.assertRaisesRegex(ValueError, "clay_prize_riemann_hypothesis"):
            audit.audit_registry_text(bad)


if __name__ == "__main__":
    unittest.main()

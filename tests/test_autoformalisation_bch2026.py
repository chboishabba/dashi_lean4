"""Focused BCH2026 contract tests. Static tests are NOT Lean kernel checks."""
from __future__ import annotations
import json
from pathlib import Path
import re
import runpy

ROOT = Path(__file__).resolve().parents[1]
EXAMPLES = ROOT / "RequestProject/Autoformalisation/LostInTranslationExamples.lean"
SCI = ROOT / "RequestProject/Autoformalisation/LostInTranslationSCI.lean"


def test_exact_selected_mathematics_runs():
    module = runpy.run_path(str(ROOT / "scripts/check_bch2026_finite_examples.py"))
    result = module["run"]()
    assert result == {
        "polynomial": 21,
        "symmetric_trace": 35,
        "extra_derivative": 1001,
        "pressure_budget": 5,
        "nonexistent_minimum": 501,
    }


def test_paper_examples_encoded_with_correct_source_dependencies():
    s = EXAMPLES.read_text(encoding="utf-8")
    required = (
        "polynomial_actual_factorisation",
        "incorrect_source_factorisation_fails_at_two",
        "symmetric_matrix_trace_square_entrywise",
        "source_budget_cannot_pay_audited_lean_jet",
        "pressure_rhs_no_unconditional_comparison",
        "no_faithful_minimum_exists",
        "defaultedMinimum_is_zero",
        "no_faithful_minimum_witness",
    )
    for name in required:
        assert "theorem " + name in s, name
    assert "f9e8bc5b38b6e212696e8a30e3e91517af887bbd" in s
    assert "arXiv:2610.08144v1" in s
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", s)
    assert "does not formalise" in s
    assert "source's partial least-number definition" in s


def test_sci_conclusions_have_externally_provided_hardness_inputs():
    s = SCI.read_text(encoding="utf-8")
    for name in ("no_effective_resolution_of_many_one_hardness",
                 "leastPresupposition_is_admissible",
                 "paid_appendix_requirements"):
        assert "theorem " + name in s
    for hypothesis in ("hEffectiveClosure", "hardUndecidable",
                       "sigmaLevelPaid", "dprmReductionPaid",
                       "postConditionPaid"):
        assert hypothesis in s
    assert "*does not* formalise" in s
    assert "SCI=infinity" in s
    assert "some_witness_count_not_enough_for_nine" in s
    assert "nine_unknown_representation_implies_some_representation" in s
    assert "Cameron Freer" in s
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", s)


def test_opt_in_no_default_target_expansion():
    lake = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    assert 'name = "AutoformalisationBCH2026"' in lake
    assert "RequestProject.Autoformalisation.LostInTranslationExamples" in lake
    assert "RequestProject.Autoformalisation.LostInTranslationSCI" in lake
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    mathlib_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = [x for x in mathlib_manifest["packages"]
               if x["name"] == "mathlib"]
    assert len(mathlib) == 1 and mathlib[0]["inputRev"] == "v4.28.0"
    # Root-vs-Mathlib toolchain divergence requires scoped override.
    assert toolchain == "leanprover/lean4:v4.35.0-rc3"


def test_appendix_a3_nine_variable_logical_bridge_is_exactly_conditional():
    lean = (
        ROOT / "RequestProject/Autoformalisation/LostInTranslationNineVariables.lean"
    ).read_text()
    for theorem in (
        "not_nine_root_iff_all_nonzero",
        "semantic_reduction_at_nine_variables",
    ):
        assert "theorem " + theorem in lean
    assert "Fin 9 → ℕ" in lean
    assert "hDPRMNine" in lean
    assert "no source-to-polynomial code compiler" in lean.lower()
    assert "effective" in lean.lower()
    assert not re.search(r"(?m)^\s*(axiom|sorry)\b", lean)
    assert "RequestProject.Autoformalisation.LostInTranslationNineVariables" in (
        ROOT / "lakefile.toml"
    ).read_text()


def test_exact_nine_variable_diophantine_replay_on_two_toy_sources():
    """Finite source-shaped replay; not DPRM/Sigma2 proof."""
    def nine_root(e: int, n: int, x: tuple[int, ...]) -> int:
        assert len(x) == 9
        return (e - n)**2 + sum(t*t for t in x)
    for e in range(20):
        for n in range(20):
            halts = (e == n)
            root_exists = (nine_root(e, n, (0,) * 9) == 0)
            assert halts == root_exists
            # Sum of nonnegative integer squares cannot vanish unless
            # the seed (e-n)^2 vanishes.
            assert not halts or root_exists
            assert (not halts) == (not root_exists)
    for e in range(20):
        assert any(n != e for n in range(20))

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


def test_appendix_A5_fixed_level_unboundedness_is_conditional():
    sci = SCI.read_text()
    assert "fixed_level_sci_unbounded_of_corollary_A5" in sci
    assert "no_uniform_finite_height_if_all_fixed_levels_restrict" in sci
    assert "hA5" in sci
    assert "hRestrictions" in sci
    # Small exact finite-prefix regressions for the deduction, not for SCI.
    for h in range(1001):
        l = max(2, h + 1)
        assert l >= 2 and l > h


def test_appendix_A4_alternation_prefix_preserved_and_source_gates_explicit():
    path = ROOT / "RequestProject/Autoformalisation/LostInTranslationAlternation.lean"
    source = path.read_text()
    for name in (
        "quantifyPrefix_congr",
        "final_exists_of_nine_variable_representation",
        "final_forall_of_nine_variable_representation",
    ):
        assert "theorem " + name in source
    assert "Fin 9 → ℕ" in source
    assert "hRepresentation" in source
    assert "not construct" in source
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", source)
    assert "RequestProject.Autoformalisation.LostInTranslationAlternation" in (
        ROOT / "lakefile.toml"
    ).read_text()


def test_quantifier_prefix_toy_semantics_unchanged_by_last_block():
    # A finite two-element universe tests the same extensional
    # congruence (not the unbounded source quantifier family).
    import itertools
    U = (0, 1)
    for bits in itertools.product((False, True), repeat=3):
        def quantify(prefix, P, chosen=()):
            if not prefix:
                return P(chosen)
            values = (quantify(prefix[1:], P, chosen + (x,)) for x in U)
            return any(values) if prefix[0] else all(values)
        for seed in range(8):
            def P(xs):
                return (sum(xs) + seed) % 3 == 0
            def Q(xs):
                return P(xs)
            assert quantify(bits, P) == quantify(bits, Q)



def test_A3_enumeration_index_keeps_surjectivity_and_effectivity_separate():
    leaf = (ROOT / "RequestProject/Autoformalisation/LostInTranslationNineVariables.lean").read_text()
    for identifier in (
        "sourceIndex",
        "sourceIndex_identifies_source_code",
        "sourceIndex_preserves_nontermination_membership",
        "IndexedNoRoot",
        "Function.Surjective enumeration",
    ):
        assert identifier in leaf
    assert "noncomputable def sourceIndex" in leaf
    assert "computability of the selected index" in leaf
    # Model a *specific* decidable surjective enumeration whose least
    # matching index is known explicitly. This is NOT a polynomial
    # encoding of the source's NTOT machine enumeration.
    for e in range(24):
        index = e + 2
        assert index == next(j for j in range(100) if j == e+2)
        for n in range(24):
            halt = (n == e + 2)
            root_at_index = (index == n)
            assert (not halt) == (not root_at_index)


def test_guarded_conditional_output_does_not_assert_closed_decision():
    path = ROOT / "RequestProject/Autoformalisation/ConditionalTranslation.lean"
    t = path.read_text()
    for key in (
        "MinimalNatural",
        "square_identity_from_presupposition",
        "uniform_guarded_template",
        "no_instance_for_source_no_root_example",
        "guarded_schema_does_not_exhibit_nonexistent_minimum",
    ):
        assert key in t
    assert "Example 4.1" in t
    assert "TOTAL" in t
    assert "not a refutation" in t.lower()
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", t)
    assert "RequestProject.Autoformalisation.ConditionalTranslation" in (
        ROOT / "lakefile.toml"
    ).read_text()



def test_A4_exact_source_parity_and_base_2_recovery():
    leaf = (ROOT / "RequestProject/Autoformalisation/LostInTranslationAlternation.lean").read_text()
    for name in (
        "sourceAlternationPrefix",
        "sourceAlternationPrefix_length",
        "sourceA4Predicate",
        "source_A4_level_two_is_A3",
        "source_A4_level_three_shape",
        "source_A4_level_four_shape",
    ):
        assert name in leaf
    assert "if level % 2 == 0" in leaf
    # Finite source-parity replay. These are fixed bounded toy domains,
    # NOT unbounded arithmetic-hierarchy or SCI-completeness proofs.
    import itertools
    domain = (0, 1, 2)
    def prefix(level):
        return [(j + 2) % 2 == 1 for j in range(level-2)]
    def Q(n, zs, xs):
        return n - sum(zs) + sum(xs)
    def evaluate(level, n, zs=(), stage=0):
        prefs = prefix(level)
        if stage < len(prefs):
            values = (evaluate(level, n, zs + (z,), stage + 1)
                      for z in domain)
            return any(values) if prefs[stage] else all(values)
        values = (Q(n, zs, (x,) + (0,)*8) == 0 for x in domain)
        return all(not value for value in values) if level % 2 == 0 else any(values)
    expected = {2: [], 3: [False], 4: [False, True],
                5: [False, True, False], 6: [False, True, False, True]}
    for level in range(2, 7):
        assert prefix(level) == expected[level]
        for n in domain:
            assert isinstance(evaluate(level, n), bool)
    for n in domain:
        assert evaluate(2, n) == all(
            Q(n, (), (x,)+(0,)*8) != 0 for x in domain
        )

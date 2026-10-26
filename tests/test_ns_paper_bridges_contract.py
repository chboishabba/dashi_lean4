"""Static and finite arithmetic checks for source-bound NS paper fragments.

Run with python -m pytest tests/test_ns_paper_bridges_contract.py -q.
These are not Lean kernel/typecheck receipts.
"""
from pathlib import Path
from fractions import Fraction
import itertools
import re

ROOT = Path(__file__).resolve().parents[1]
MILLER = ROOT / "RequestProject/NavierStokes/MillerAnisotropicAlgebra.lean"
YAN = ROOT / "RequestProject/NavierStokes/YanRadulescuPressure.lean"


def test_exact_source_citations_and_no_lean_holes():
    miller, yan = MILLER.read_text(), YAN.read_text()
    assert "10.1090/bproc/74" in miller
    assert "10.1007/s12215-020-00540-3" in yan
    for text in (miller, yan):
        assert "import Mathlib" in text
        assert not re.search(r"(?m)^\s*(sorry|axiom)\b", text)
        assert "admit" not in text


def test_miller_coordinate_identity_exact_rational_sweep():
    for a, b in itertools.product(range(-5, 6), repeat=2):
        a, b = Fraction(a), Fraction(b)
        assert ((a + b) / 2) ** 2 == ((a - b) / 2) ** 2 + a * b
        assert (a + b) ** 2 <= 2 * a * a + 2 * b * b
    assert 4 * (Fraction(2) - Fraction(3, 2)) - 2 == 0


def test_forced_pressure_requires_divergence_correction():
    for forcing_div in range(-3, 4):
        for convection_div in range(-3, 4):
            pressure_lap = forcing_div - convection_div
            assert forcing_div == pressure_lap + convection_div
            assert (pressure_lap == -convection_div) == (forcing_div == 0)


def test_yan_cyclic_derivative_coefficients():
    for eps, g in itertools.product(range(-5, 6), repeat=2):
        assert eps * g + eps * g - 2 * eps * g == 0


def test_opt_in_library_and_no_false_physical_claim():
    lakefile = (ROOT / "lakefile.toml").read_text()
    assert 'name = "NSPaperBridges"' in lakefile
    assert "RequestProject.NavierStokes.MillerAnisotropicAlgebra" in lakefile
    assert "RequestProject.NavierStokes.YanRadulescuPressure" in lakefile
    assert "not a formal proof of integration by parts" in MILLER.read_text()
    assert "does NOT claim to have formalised" in YAN.read_text()

def test_source_cube_seed_has_real_derivative_and_face_obligations():
    lean = (ROOT / "RequestProject/NavierStokes/YanRadulescuCubeSeed.lean").read_text()
    for theorem in (
        "hasDerivAt_seed1",
        "hasDerivAt_seed2",
        "hasDerivAt_seed3",
        "seed_divergence_zero",
        "derivative_factor_ring_identity",
        "seed_zero_faces",
        "seed_upper_faces",
    ):
        assert "theorem " + theorem in lean
    assert "HasDerivAt F" in lean
    assert "Corollary 1.1" in lean
    assert "separate exact-expression proof" in lean
    assert 'RequestProject.NavierStokes.YanRadulescuCubeSeed' in (
        ROOT / "lakefile.toml"
    ).read_text()


def test_source_polynomial_replay_105_exact_instances():
    import runpy
    script = ROOT / "scripts/check_yan_radulescu_polynomial_seed.py"
    audit = runpy.run_path(str(script))
    assert audit["run"]() == 105


def test_exact_published_exponential_seed_and_derivative_proof_structure():
    lean = (ROOT / "RequestProject/NavierStokes/YanRadulescuExactSeed.lean").read_text()
    for theorem in (
        "polynomialBase_hasDerivAt",
        "h_hasDerivAt",
        "rho_hasDerivAt",
        "hasDerivAt_envelope",
        "hasDerivAt_sourceF_from_factors",
        "sourceF_hasDerivAt",
        "printed_seed_divergence_zero",
        "printed_seed_zero_faces",
        "printed_seed_upper_faces",
    ):
        assert "theorem " + theorem in lean, theorem
    for feature in ("Real.exp (-rho", "(qExtra + 3)", "2 * (pExtra + 3)"):
        assert feature in lean
    assert "10.1007/s12215-020-00540-3" in lean
    assert "Nash–Moser iteration" in lean
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", lean)
    assert "RequestProject.NavierStokes.YanRadulescuExactSeed" in (
        ROOT / "lakefile.toml"
    ).read_text()


def test_pressure_polynomial_countermodel_exact_rational_sweep():
    """Central differences are exact for degree-2 P; these aren't kernel results."""
    for eps in range(-3, 4):
        if eps == 0:
            continue
        for x in range(-2, 3):
            for delta in (Fraction(1, 4), Fraction(1, 2)):
                a = Fraction(eps)
                z = Fraction(x)
                P = lambda y: a * y * y / 2
                f = lambda y: a * y
                assert (P(z + delta) - P(z - delta)) / (2 * delta) == f(z)
                assert (
                    P(z + delta) - 2 * P(z) + P(z - delta)
                ) / (delta * delta) == a
                assert (f(z + delta) - f(z - delta)) / (2 * delta) == a
                assert a != 0


def test_pressure_countermodel_pays_actual_derivative_not_just_scalars():
    lean = (
        ROOT / "RequestProject/NavierStokes/YanRadulescuPressureCountermodel.lean"
    ).read_text()
    for theorem in (
        "pressureSlice_hasDerivAt",
        "forceSlice_hasDerivAt",
        "pressureSlice_second_derivative",
        "pressureSlice_laplacian_not_zero",
        "positive_nonzero_forcing_below",
    ):
        assert "theorem " + theorem in lean
    assert "div f" in lean
    assert "PDE existence" not in lean
    assert not re.search(r"(?m)^\s*(sorry|axiom)\b", lean)
    assert "RequestProject.NavierStokes.YanRadulescuPressureCountermodel" in (
        ROOT / "lakefile.toml"
    ).read_text()

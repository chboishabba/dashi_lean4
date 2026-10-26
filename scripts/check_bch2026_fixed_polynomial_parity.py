"""Exact integer-polynomial parity replay for BCH2026 Appendix A.4.

Source: Bastounis, Circelli, Hansen, arXiv:2610.08144v1 (2026-10-06).
This tests a FIXED polynomial with integer coefficients, not an
oracle-valued Q(xs,z). The coefficient tuple (a,b,c,d) is held fixed
throughout each quantifier evaluation, including n and witness search.

All 9 final witnesses are searched over {0,1}^9 ONLY. Therefore this
is a finite adversarial replay of quantifier syntax; it is not the
unbounded Diophantine theorem, a proof of Sigma_l completeness or SCI.
"""
from __future__ import annotations
from itertools import product
from typing import Iterable

DOM = (0, 1)
FINAL_WITNESSES = tuple(product(DOM, repeat=9))


def a4_prefix(level: int) -> tuple[bool, ...]:
    if level < 2:
        raise ValueError("A.4 requires l>=2")
    return tuple((j % 2) == 1 for j in range(2, level))


def eval_fixed_polynomial(n: int, zs: tuple[int, ...],
                          x: tuple[int, ...], coeff: tuple[int, ...]) -> int:
    a, b, c, d = coeff
    if len(x) != 9:
        raise ValueError("exactly nine final variables")
    # Multivariate polynomial with fixed integral coefficients in n,
    # intermediate variables and nine root variables.
    return a*n + b*sum(zs) + c*sum(x) + d


def source_quantified(level: int, n: int,
                      coeff: tuple[int, ...]) -> bool:
    prefix = a4_prefix(level)

    def evaluate(stage: int, zs: tuple[int, ...]) -> bool:
        if stage == len(prefix):
            if len(zs) != level - 2:
                raise ValueError("Malformed source quantifier prefix")
            roots = (
                eval_fixed_polynomial(n, zs, x, coeff) == 0
                for x in FINAL_WITNESSES
            )
            return all(not root for root in roots) if level % 2 == 0 else any(roots)
        branches = (evaluate(stage+1, zs+(z,)) for z in DOM)
        return any(branches) if prefix[stage] else all(branches)

    return evaluate(0, ())


def check() -> dict[str, int]:
    if not __debug__:
        raise RuntimeError("Cannot trust optimized Python arithmetic assertions")
    seen = 0
    shapes = 0
    # 5 levels, 4 inputs, 6 coefficient tuples = 120 exact fixtures.
    coeffs = (
        (1, 0, 1, 0), (1, -1, 1, 0), (1, 1, -1, 0),
        (0, 1, 1, -1), (-1, 2, 1, 1), (0, 0, 0, 1),
    )
    for level in range(2, 7):
        prefix = a4_prefix(level)
        assert len(prefix) == level - 2
        assert prefix == tuple(j % 2 == 1 for j in range(2, level))
        shapes += 1
        for n in range(4):
            for coeff in coeffs:
                observed = source_quantified(level, n, coeff)
                assert type(observed) is bool
                if level == 2:
                    expected = all(
                        eval_fixed_polynomial(n, (), x, coeff) != 0
                        for x in FINAL_WITNESSES
                    )
                    assert observed == expected
                seen += 1
    result = {"fixed_polynomial_fixtures": seen,
              "quantifier_shapes": shapes}
    print("PASS", result)
    return result


if __name__ == "__main__":
    check()

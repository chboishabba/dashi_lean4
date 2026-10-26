"""Exact finite replay of BCH2026 Examples 2.1/2.2/3.1/3.3/4.3.

Original authors: Alexander Bastounis, Fabian Circelli, Anders C. Hansen,
arXiv:2610.08144v1 (2026-10-06). This is DASHI's selected finite
independent reconstruction, not a proof of the paper's SCI=A.4 result,
not a Lean kernel receipt and not a proof about OpenAI's whole PDE.

Run: python scripts/check_bch2026_finite_examples.py
"""
from __future__ import annotations

from fractions import Fraction as Q


def run() -> dict[str, int]:
    if not __debug__:
        raise RuntimeError("BCH finite audit refuses Python -O: assertions would be stripped")
    counts: dict[str, int] = {}

    # Example 2.1: the NL polynomial theorem is correct while the
    # proposed NL factorisation (x-1)(x+1)^2 is incorrect.
    for x in range(-1, 20):
        lhs = x**3 - x**2 - x + 1
        assert lhs == (x-1)**2*(x+1)
        assert lhs >= 0
    assert (2**3 - 2**2 - 2 + 1) != (2-1)*(2+1)**2
    counts["polynomial"] = 21

    # Example 2.2: direct symmetric matrix proof is a DIFFERENT
    # argument from orthogonal diagonalisation; same theorem conclusion.
    matrix_count = 0
    for n in range(1, 6):
        for seed in range(-3, 4):
            A = [[Q((i+1)*(j+1)+seed) for j in range(n)]
                 for i in range(n)]
            assert all(A[i][j] == A[j][i]
                       for i in range(n) for j in range(n))
            trace_square = sum(A[i][j]*A[j][i]
                               for i in range(n) for j in range(n))
            sum_squares = sum(A[i][j]**2
                              for i in range(n) for j in range(n))
            assert trace_square == sum_squares and trace_square >= 0
            matrix_count += 1
    counts["symmetric_trace"] = matrix_count

    # Example 3.1: exact natural-number derivative debt.
    for m in range(1001):
        assert m+4 < m+5
        assert not (m+5 <= m+4)
    counts["extra_derivative"] = 1001

    # Example 3.3: synthetic independent RHS coordinates at
    # R=1, B_R=0. This is NOT a valid real NS-field countermodel.
    for A in (Q(0), Q(1, 10), Q(1), Q(7), Q(1000)):
        original_budget = Q(0)
        historical_lean_budget = A+1
        assert historical_lean_budget > original_budget
    counts["pressure_budget"] = 5

    # Example 4.3: at each n, (n,0) solves x1+x2-n=0.
    for n in range(501):
        assert n+0-n == 0
    # In Mathlib Nat.sInf(empty) is zero; the source's partial
    # minimum does NOT exist. The identity with an invented
    # default 1 is algebraically valid but semantically irrelevant.
    default_r = Q(1)
    assert (default_r+1)**2 == default_r**2 + 2*default_r + 1
    counts["nonexistent_minimum"] = 501

    print("PASS", counts, "total", sum(counts.values()))
    return counts


if __name__ == "__main__":
    run()

#!/usr/bin/env python3
"""Exact rational tests of 4D SU(2) Q8 boundary-Wilson and residual RP.

This is an independent finite-subgroup diagnostic, NOT a Lean kernel check or
an application to the selected CMP119 effective density.  Q8 is embedded
in the actual unit-quaternion SU(2), and the crossing plaquette uses the
relative trace scalar(U * inverse(V)).  Positive polynomial truncations of
exp(beta * dot) have an exact positive-feature expansion for beta>=0.

The full SU(2) exponential Wilson kernel requires an independent infinite-
series/character-positivity theorem; finite Q8 PSD checks do not prove it.
"""

from fractions import Fraction as F
from itertools import product
from math import factorial

ZERO, ONE = F(0), F(1)


def dot(x, y):
    return sum((a * b for a, b in zip(x, y)), ZERO)


def psd_exact(mat):
    """Rational symmetric Schur-complement PSD check (handles null pivots)."""
    a = [list(row) for row in mat]
    n = len(a)
    assert all(a[i][j] == a[j][i] for i in range(n) for j in range(n))
    for k in range(n):
        pivot = a[k][k]
        if pivot < 0:
            return False
        if pivot == 0:
            if any(a[k][j] for j in range(k + 1, n)):
                return False
            continue
        for i in range(k + 1, n):
            for j in range(i, n):
                val = a[i][j] - a[i][k] * a[k][j] / pivot
                a[i][j] = val
                a[j][i] = val
        for i in range(k + 1, n):
            a[k][i] = a[i][k] = ZERO
    return True


def q8():
    return tuple(
        tuple(sign if i == axis else ZERO for i in range(4))
        for axis, sign in product(range(4), (ONE, -ONE))
    )


def taylor(derivative, x, order):
    return sum(
        (derivative**k * x**k / factorial(k)
         for k in range(order + 1)), ZERO
    )


def gram(f, kernel):
    return sum(
        (f[i] * kernel[i][j] * f[j]
         for i in range(len(f)) for j in range(len(f))), ZERO
    )


def audit():
    q = q8()
    assert len(set(q)) == 8
    # Real trace of quaternion U*V^{-1} is the genuine SU(2) dot.
    assert set(dot(u, v) for u in q for v in q) == {-ONE, ZERO, ONE}
    for beta in (F(0), F(1, 8), F(1, 2), F(1), F(3), F(9)):
        linear = [[ONE + beta * dot(u, v) for v in q] for u in q]
        assert psd_exact(linear)
        for order in (0, 1, 2, 3, 4, 6, 8):
            crossing = [[taylor(beta, dot(u, v), order) for v in q]
                        for u in q]
            assert psd_exact(crossing), (beta, order)
            # Nontrivial cross-plane positive-feature residual and
            # reflected half weights preserve positive Gram directions.
            features = [
                [u[i] for u in q] for i in range(4)
            ] + [[sum((u[i]**2 for i in range(2)), ZERO) for u in q]]
            weights = [F(1, 7), F(1, 3), F(2), F(1, 5), F(3, 4)]
            residual = [[sum((weights[k] * f[i] * f[j]
                              for k, f in enumerate(features)), ZERO)
                         for j in range(8)] for i in range(8)]
            half = [F(i + 1, i + 3) for i in range(8)]
            complete = [
                [half[i] * crossing[i][j] * residual[i][j] * half[j]
                 for j in range(8)] for i in range(8)
            ]
            assert psd_exact(complete), (beta, order, "feature cross")
    # Strictly positive Gibbs entries and arbitrarily small cross
    # perturbations do not guarantee reflection positivity.
    for eps in (F(1), F(1, 100), F(1, 10_000_000)):
        perturbed = [[ONE, ONE + eps], [ONE + eps, ONE]]
        assert min(v for row in perturbed for v in row) > ZERO
        assert gram([ONE, -ONE], perturbed) == -2 * eps
        assert not psd_exact(perturbed)
    # Finite density comparison e.g. across selected sectors:
    # a pointwise residual likelihood ratio r in [1/C,C] yields
    # normalized positive-probe comparison <= C^2.
    for _ in range(8):
        base = [F(i + 1, 18) for i in range(8)]
        r = [F((i % 3) + 1, 3) for i in range(8)]
        full = [base[i] * r[i] for i in range(8)]
        probe = [F(i**2, 17) for i in range(8)]
        m0 = sum((p * f for p, f in zip(base, probe)), ZERO)/sum(base)
        m1 = sum((p * f for p, f in zip(full, probe)), ZERO)/sum(full)
        C = F(3)
        assert m1 <= C**2 * m0
        assert m0 <= C**2 * m1
    print("PASS Q8 exact RP: first-order Wilson crossing and 7 Taylor orders")
    print("PASS six beta choices; positive cross features plus half weights")
    print("PASS arbitrarily small positive-Gibbs/negative-Gram counterexamples")
    print("PASS exact finite full/Wilson normalized-observable comparisons")
    print("NOT PROVED: CMP119 source identification, continuum estimates, full SU2 exponential RP")


if __name__ == "__main__":
    audit()

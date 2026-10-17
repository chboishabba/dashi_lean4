#!/usr/bin/env python3
"""Finite preflight for the projective T5/E8 geometry obstruction.

Not kernel evidence.  Exhausts all 27 symmetric C5-invariant bilinear forms on
F3^5, on the 120 non-diagonal projective five-trit points, and checks whether
either B=0 or B!=0 is 56-regular.  It also independently enumerates the E8
root-line nonorthogonality graph and checks its strongly regular parameters.
"""

from collections import Counter
from fractions import Fraction
import itertools
import json

TRITS = (-1, 0, 1)


def neg(v):
    return tuple(-x for x in v)


def t5_projective_points():
    rel = [x for x in itertools.product(TRITS, repeat=5)
           if not (x[0] == x[1] == x[2] == x[3] == x[4])]
    return sorted({min(x, neg(x)) for x in rel})


def e8_roots():
    roots = []
    for i, j in itertools.combinations(range(8), 2):
        for a, b in itertools.product((-2, 2), repeat=2):
            v = [0] * 8
            v[i], v[j] = a, b
            roots.append(tuple(Fraction(x) for x in v))
    for s in itertools.product((-1, 1), repeat=8):
        if sum(x < 0 for x in s) % 2 == 0:
            roots.append(tuple(Fraction(x) for x in s))
    return roots


def dot(x, y):
    return sum(a * b for a, b in zip(x, y))


def bcirc(x, y, coeffs):
    a, b, c = coeffs
    total = 0
    for i in range(5):
        for j in range(5):
            d = (j - i) % 5
            k = a if d == 0 else b if d in (1, 4) else c
            total += k * (x[i] % 3) * (y[j] % 3)
    return total % 3


def main():
    points = t5_projective_points()
    assert len(points) == 120

    degree56 = []
    spectra = {}
    for coeffs in itertools.product(range(3), repeat=3):
        for zero_relation in (True, False):
            degrees = []
            for x in points:
                degree = 0
                for y in points:
                    if x == y:
                        continue
                    is_zero = bcirc(x, y, coeffs) == 0
                    degree += int(is_zero == zero_relation)
                degrees.append(degree)
            spectra[(coeffs, zero_relation)] = Counter(degrees)
            if all(d == 56 for d in degrees):
                degree56.append((coeffs, zero_relation))
    assert not degree56

    roots = e8_roots()
    lines = sorted({min(r, neg(r)) for r in roots})
    assert len(lines) == 120
    adj = {r: set() for r in lines}
    for i, r in enumerate(lines):
        for s in lines[i + 1:]:
            if dot(r, s) != 0:
                adj[r].add(s)
                adj[s].add(r)
    assert all(len(adj[r]) == 56 for r in lines)

    adjacent_common = set()
    nonadjacent_common = set()
    for i, r in enumerate(lines):
        for s in lines[i + 1:]:
            common = len(adj[r] & adj[s])
            if s in adj[r]:
                adjacent_common.add(common)
            else:
                nonadjacent_common.add(common)
    assert adjacent_common == {28}
    assert nonadjacent_common == {24}

    print(json.dumps({
        "projective_t5_points": 120,
        "symmetric_circulant_forms": 27,
        "zero_or_nonzero_relations_tested": 54,
        "degree_56_candidates": 0,
        "e8_root_lines": 120,
        "e8_root_line_graph": {"k": 56, "lambda": 28, "mu": 24},
        "simple_c5_invariant_bilinear_geometry_survives": False,
        "kernel_evidence": False,
    }, indent=2))


if __name__ == "__main__":
    main()

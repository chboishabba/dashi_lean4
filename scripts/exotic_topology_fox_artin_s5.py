#!/usr/bin/env python3
"""Exact S5 witness from Fox--Artin (1948), Example 1.1*, p.983, (2_n*).

The paper's three-periodic cycle images satisfy
  a_n a_(n+1)^2 a_(n+2)
    = a_(n+1) a_(n+2) a_(n+1)^(-1) a_n a_(n+1).
This independent check is a presentation-level finite certificate,
NOT a proof that the presented group equals pi1 of the physical
embedded-arc complement; the geometric directed-colimit weld is open.
DOI: 10.2307/1969408.
"""
import json


def cycle(xs):
    p = list(range(1, 6))
    for x, y in zip(xs, xs[1:] + xs[:1]):
        p[x - 1] = y
    return tuple(p)


def mul(p, q):
    return tuple(p[q[i] - 1] for i in range(5))


def inverse(p):
    return tuple(p.index(i + 1) + 1 for i in range(5))


def compose(*perms):
    r = (1, 2, 3, 4, 5)
    for p in perms:
        r = mul(r, p)
    return r


IMAGES = tuple(cycle(xs) for xs in
               ((1, 2, 3, 4, 5), (1, 2, 5, 3, 4), (1, 2, 4, 5, 3)))


def a(n):
    return IMAGES[n % 3]


def relator(n):
    x, y, z = a(n), a(n + 1), a(n + 2)
    return compose(x, y, y, z), compose(y, z, inverse(y), x, y)


def audit():
    # Only 3 residue cases are needed; the broad range is an independent
    # periodic-index regression and includes negative source indices.
    assert all(lhs == rhs for lhs, rhs in map(relator, range(-301, 302)))
    assert all(p != (1, 2, 3, 4, 5) for p in IMAGES)
    assert all(compose(p, p, p, p, p) == (1, 2, 3, 4, 5) for p in IMAGES)
    return {
        "source": "Fox--Artin (1948), Example 1.1*, page 983",
        "periodic_generator_images": [list(p) for p in IMAGES],
        "checked_index_range": [-301, 301],
        "three_residue_relators": True,
        "nontrivial_S5_model": True,
        "actual_complement_pi1_identification": False,
        "wildness_from_this_script": False,
        "separate_examples": {
            "1.1*": "non-simply-connected complement",
            "1.2": "wild arc with open-3-cell complement",
            "1.3": "simply-connected complement not open-3-cell"
        }
    }


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2, sort_keys=True))

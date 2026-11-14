#!/usr/bin/env python3
"""Exact finite Q2-square-class certificate on original E: y^2=x^3-x.

This is a mathematically genuine candidate lower-bound computation on the
ACTUAL original local Kummer values: 4 original rational E[2] torsion
points and x=39, y=4*sqrt(3705), a genuine Q2 point (3705 ≡ 1 mod 8).
All units and 2-valuations use exact rational arithmetic.

The original Lean repo proves LocalKummerImage(2) is a subgroup of
the actual PadicSquareClass pair; therefore these five genuine local
points generate at least eight distinct image classes, conditional on
faithful admission of the standard 2-adic square criterion and local
Kummer quotient identity in the selected Lean carrier.

This is NOT a Lean kernel proof of the Q2 point, a complete enumeration
of the local image, continuous H1 compatibility, Sha or BSD.
"""
from fractions import Fraction
import json

def v2_odd(n):
    assert n != 0
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    return v, n

def cls(q):
    q = Fraction(q)
    vn, un = v2_odd(q.numerator)
    vd, ud = v2_odd(q.denominator)
    return ((vn - vd) & 1, (un * pow(ud % 8, -1, 8)) % 8)

def mul(a, b):
    return ((a[0] ^ b[0]), (a[1] * b[1]) % 8)

def prod(a, b):
    return (mul(a[0], b[0]), mul(a[1], b[1]))

def original_curve_kummer_candidates():
    torsion = {
        "O": (Fraction(1), Fraction(1)),
        "(0,0)": (Fraction(-1), Fraction(-1)),
        "(1,0)": (Fraction(1), Fraction(2)),
        "(-1,0)": (Fraction(-1), Fraction(-2)),
    }
    x = Fraction(39)
    rhs = x * (x - 1) * (x + 1)
    assert rhs == 16 * 3705
    assert 3705 % 8 == 1
    # 2-adic square criterion: odd unit u is square iff u ≡ 1 mod 8.
    # Hence P=(39,4 sqrt(3705)) is a genuine ordinary E(Q2) point.
    P = (x, x-1)
    T = {name: (cls(a), cls(b)) for name,(a,b) in torsion.items()}
    p = (cls(P[0]), cls(P[1]))
    assert p == ((0, 7), (1, 3))  # Kummer [-1], [-10].
    assert len(set(T.values())) == 4
    image = set(T.values()) | {prod(p, t) for t in T.values()}
    assert len(image) == 8
    assert p not in set(T.values())
    assert all(first[0] == 0 for first,second in image)
    def fmt(pair):
        return [f"valuation_parity={pbit},odd_unit_mod8={unit}" for pbit,unit in pair]
    return {
        "schema":"bsd-q2-original-local-kummer-eight-exact-v1",
        "curve":"y^2=x^3-x",
        "original_local_point_x":"39",
        "original_local_point_y":"4*sqrt_2adic(3705)",
        "actual_RHS":str(rhs),
        "Q2_unit_square_criterion": "3705 mod8=1",
        "Kummer_original_coordinates":"[x],[x-1]",
        "original_torsion_classes":{key:fmt(value) for key,value in T.items()},
        "nontorsion_39_class":fmt(p),
        "eight_distinct_Q2_squareclass_pairs": [fmt(c) for c in sorted(image)],
        "cardinality_lower_bound":len(image),
        "class_result":"PASS",
        "Lean_Q2_actual_point_constructed":False,
        "Lean_complete_local_Kummer_image":False,
        "Lean_compatibility_with_continuous_H1":False,
        "bsd_clay_proved":False,
    }

if __name__=="__main__":
    print(json.dumps(original_curve_kummer_candidates(),indent=2))

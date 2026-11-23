#!/usr/bin/env python3
"""Same j=0 curve Hasse-source regression (exact, finite, not a Lean proof).

Independent of the original ray/Euler scripts: this checks only the new
norm/trace-to-Hasse and local denominator seam on y^2=x^3+1.
"""
from fractions import Fraction
from math import isqrt
from sympy import symbols, expand, primerange

a, b = symbols("a b", integer=True)
assert expand(4*(a*a - a*b + b*b) - (2*a-b)**2) == 3*b*b

count = 0
for p in primerange(5, 601):
    # #E(Fp) = p+1+sum_x chi(x^3+1); a_p = -sum_x chi.
    chi_sum = 0
    for x in range(p):
        z = (x*x*x + 1) % p
        if z:
            chi_sum += 1 if pow(z, (p-1)//2, p) == 1 else -1
    t = -chi_sum
    assert t*t <= 4*p, (p, t)
    assert 1 - Fraction(t, p*p) + Fraction(1, p**3) > 0
    if p % 3 == 2:
        assert t == 0
    else:
        R = 2*isqrt(p)+5
        assert any(u*u-u*v+v*v == p and abs(2*u-v) == abs(t)
                   for u in range(-R, R+1)
                   for v in range(-R, R+1)), (p, t)
    count += 1

assert count == 107, count
# At sigma>3/2 the Hasse majorant is 2*p^(1/2-sigma)
# + p^(1-2*sigma). Its two prime-indexed terms are summable
# because both exponents are below -1.
print("PASS: symbolic Eisenstein 4*norm-trace^2 = 3b^2")
print(f"PASS: {count}/{count} original j=0 Hasse and local s=2 Euler checks")
print("NOTICE: finite exact regression is not Lean kernel certification")

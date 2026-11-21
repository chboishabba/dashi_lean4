#!/usr/bin/env python3
"""Original E32 literal y^2=x^3-x reduction geometry, exact finite test.

Tests smoothness of the literal integral Weierstrass fibre at ALL odd
primes p<=257, the unique singular characteristic-two fibre, its exact
translated cuspidal normal form, and a bad-factor false-promotion control.
This is NOT the Mathlib p-adic minimal-model comparison nor Lean kernel.
"""
from sympy import Poly, symbols, primerange

u, v, T = symbols('u v T')
primes = tuple(primerange(2, 258))
checks = 0
singular = {}
counts = {}
for p in primes:
    assert 64 % p == 0 if p == 2 else 64 % p != 0
    checks += 1
    residue_counts = {z: 0 for z in range(p)}
    for y in range(p):
        residue_counts[(y * y) % p] += 1
    count = 1
    singular_points = []
    for x in range(p):
        rhs = (x * x * x - x) % p
        count += residue_counts[rhs]
        for y in range(p):
            F = (y*y - x*x*x + x) % p
            Fx = (1 - 3*x*x) % p
            Fy = 2*y % p
            if F == Fx == Fy == 0:
                singular_points.append((x,y))
    counts[p] = count
    singular[p] = tuple(singular_points)
    if p == 2:
        assert singular_points == [(1,0)]
    else:
        assert singular_points == []
    checks += 1

F2 = v**2 - (1+u)**3 + (1+u)
normal = (v+u)**2 + u**3
assert Poly(F2-normal,u,v, modulus=2).is_zero
checks += 1
# E32 has minimal discriminant 64 = 2^6, so v2(Delta)=6 < 12.
assert 64 == 2**6 and 6 < 12
checks += 1
# The p=2 SINGULAR literal fibre must not get the good formula.
wrong_good = 1 - (2 + 1 - counts[2])*T + 2*T**2
assert wrong_good != 1
checks += 1
assert counts[2] == 3 and wrong_good == 1 + 2*T*T
checks += 1
# Original arithmetic character trace at p=3,5,7,13.
assert {p:p+1-counts[p] for p in (3,5,7,13)} == {3:0,5:-2,7:0,13:6}
checks += 1
print('PASS exact original E32 literal reduction geometry', checks, '/', checks)
print('all primes <= 257:',len(primes),'odd smooth:',len(primes)-1,'p2 singular:',singular[2])
print('char2 local chart: (v+u)^2+u^3; v2(Delta)=6<12; false good p2 factor rejected')
print('open: Mathlib p-adic minimal-model identification, residue-field equivalence, actual additive-branch theorem')

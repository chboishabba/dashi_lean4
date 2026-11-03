#!/usr/bin/env python3
"""Exact finite regression for pure-imaginary Bishop/Round11 Cauchy coefficients.

Not a formal all-n proof or a Lean/Agda kernel receipt. The exact
Fraction arithmetic tests factorial indices and alternating parity.
"""
from fractions import Fraction
from math import comb, factorial
import json

def phase(n: int) -> tuple[int, int]:
    return ((1, 0), (0, 1), (-1, 0), (0, -1))[n % 4]

def imag_exp_coeff(x: Fraction, n: int) -> tuple[Fraction, Fraction]:
    q = x**n / factorial(n)
    a, b = phase(n)
    return a*q, b*q

def cmul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]

def add(a, b):
    return a[0]+b[0], a[1]+b[1]

def check(max_degree=48, max_choose_degree=256):
    pairs = [
        (Fraction(0), Fraction(0)),
        (Fraction(1), Fraction(0)),
        (Fraction(-1), Fraction(0)),
        (Fraction(1, 2), Fraction(-2, 3)),
        (Fraction(1, 5), Fraction(1, 239)),
        (Fraction(3, 7), Fraction(-5, 11)),
        (Fraction(-2), Fraction(3)),
    ]
    for n in range(max_choose_degree + 1):
        for k in range(n + 1):
            assert comb(n, k)*factorial(k)*factorial(n-k) == factorial(n)
    for x, y in pairs:
        for n in range(max_degree + 1):
            partial = (Fraction(0), Fraction(0))
            for k in range(n + 1):
                partial = add(
                    partial,
                    cmul(imag_exp_coeff(x, k), imag_exp_coeff(y, n-k)),
                )
            assert partial == imag_exp_coeff(x+y, n), (x, y, n)
            a, b = imag_exp_coeff(x, n)
            if n % 2 == 0:
                assert b == 0 and a == (-1)**(n//2)*x**n/factorial(n)
            else:
                assert a == 0 and b == (-1)**((n-1)//2)*x**n/factorial(n)
    return {
        "result": "PASS",
        "finite_complex_cauchy_cases": len(pairs)*(max_degree+1),
        "binomial_factorial_cases": (max_choose_degree+1)*(max_choose_degree+2)//2,
        "max_complex_degree": max_degree,
        "max_binomial_degree": max_choose_degree,
        "method": "exact Python fractions; no floating point",
        "kernel_receipt": False,
        "proof_for_all_n": False,
    }

if __name__ == "__main__":
    print(json.dumps(check(), sort_keys=True))

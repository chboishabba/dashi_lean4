"""Exact 3D forced steady pressure-consistency check (not a PDE proof).

Primary source: Weiping Yan & Vicenţiu D. Rădulescu,
DOI 10.1007/s12215-020-00540-3, equations (1.1)/(1.3).
DASHI adversarial witness: U=0, P=epsilon*x1^2/2,
f=(epsilon*x1,0,0) on a bounded cube. For epsilon != 0:
-ν ΔU + (U·∇)U + ∇P = f, div(U)=0, U|boundary=0,
but ΔP=div(f)=epsilon != 0.
This does not settle whether extra source assumptions could repair (1.3).
Executed symbolic checks do not certify the Lean PDE theorem.
"""
from __future__ import annotations

import sympy as s


def run():
    x1, x2, x3, eps, nu = s.symbols(
        "x1 x2 x3 epsilon nu", real=True
    )
    X = (x1, x2, x3)
    U = s.Matrix([0, 0, 0])
    P = eps * x1**2 / 2
    f = s.Matrix([eps * x1, 0, 0])
    gradient_pressure = s.Matrix([s.diff(P, xi) for xi in X])
    divergence_u = sum(s.diff(U[i], X[i]) for i in range(3))
    divergence_f = sum(s.diff(f[i], X[i]) for i in range(3))
    laplace_p = sum(s.diff(P, xi, 2) for xi in X)
    laplace_u = s.Matrix([
        sum(s.diff(U[i], xi, 2) for xi in X)
        for i in range(3)
    ])
    convection = s.Matrix([
        sum(U[j] * s.diff(U[i], X[j]) for j in range(3))
        for i in range(3)
    ])
    residual = -nu * laplace_u + convection + gradient_pressure - f
    assert all(s.simplify(z) == 0 for z in residual)
    assert s.simplify(divergence_u) == 0
    assert s.simplify(laplace_p - divergence_f) == 0
    assert s.simplify(laplace_p - eps) == 0
    assert s.simplify(divergence_f - eps) == 0
    # The source formula with an absent div(f) requires laplace_p == 0
    # for U==0, but the selected nonzero epsilon violates it.
    for epsilon in (s.Rational(1, 1000), s.Rational(-1, 10000),
                    s.Rational(1, 1000000)):
        assert s.simplify(laplace_p.subs(eps, epsilon)) != 0
        assert all(s.simplify(z.subs(eps, epsilon)) == 0
                   for z in residual)
    print("PASS: exact 3D momentum, div(U), Delta(P)=div(f), "
          "and 3 nonzero forcing amplitudes")
    return 3


if __name__ == "__main__":
    run()

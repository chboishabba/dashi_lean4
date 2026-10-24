#!/usr/bin/env python3
"""Exact rational related-triple recovery for Griess1990's Peirce tensor.

Original mathematical sources: Hurwitz composition algebras; Griess (1990)
J. Algebra 131, 281-293; Alsaody--Gille (2019) octonion isotopes and triality;
Barry--Tignol (2023) rational trialitarian triples. Existing source-object
owners: Lean PR #52 Peirce frame, native rational H3(O), octonion multiplication.

This executable constructs a Q-rational product isomorphism between the
EXISTING source τ-real Peirce model and the EXISTING native rational
Cayley--Dickson H3(O), fixing the three diagonal frame idempotents. It checks
512/512 independent cross-slot coefficients, 729/729 full Jordan basis
products, the unit, and the source trace pairing. A SymPy proof-by-finite
calculation is not Lean kernel verification or a classification theorem.
"""
from pathlib import Path
from itertools import product
import runpy
import sympy as sp

def recover(mu, q, chart, native_mul):
    """Given a positive Q-normed composition of three 8D spaces with common
    q, recover explicit rational (g0,g1,g2) with
           g2(mu(x,y)) = native_mul(g0(x),g1(y)).
    Assert the complete polynomial composition identities before recovery.
    """
    I = sp.eye(8)
    e = [I[:, i] for i in range(8)]
    assert chart.T * chart == q
    inner = lambda x, y: (x.T * q * y)[0]
    a = chart.inv() * e[0]
    b = a
    assert inner(a, a) == inner(b, b) == 1

    Ls = [sp.Matrix.hstack(*[mu(e[i], e[j]) for j in range(8)])
          for i in range(8)]
    for i in range(8):
        for k in range(i, 8):
            assert Ls[i].T * q * Ls[k] + Ls[k].T * q * Ls[i] == (
                2 * q[i, k] * q
            ), (i, k)

    c = mu(a, b)
    assert inner(c, c) == 1
    right = sp.Matrix.hstack(*[mu(e[i], b) for i in range(8)])
    left = sp.Matrix.hstack(*[mu(a, e[i]) for i in range(8)])
    assert right.T * q * right == q and left.T * q * left == q
    rinv = right.inv()
    linv = left.inv()
    star = lambda x, y: mu(rinv * x, linv * y)
    assert all(star(c, e[i]) == e[i] and star(e[i], c) == e[i]
               for i in range(8))

    # Rational metric Householder extends the selected unit to a frame.
    c0 = chart * c
    v0 = c0 - e[0]
    H = I if v0 == sp.zeros(8, 1) else I - 2*v0*v0.T/(v0.T*v0)[0]
    assert H.T * H == I and H * e[0] == c0
    f = [chart.inv() * H * ei for ei in e]
    assert sp.Matrix.hstack(*f).T * q * sp.Matrix.hstack(*f) == I

    u, v = f[1], f[2]
    uv = star(u, v)
    assert inner(uv, uv) == 1
    assert all(inner(uv, z) == 0 for z in (c, u, v))
    r = f[3] - uv
    J = I if r == sp.zeros(8, 1) else I - 2*r*(r.T*q)/inner(r, r)
    assert J.T * q * J == q and J * f[3] == uv
    w = J * f[4]
    assert all(inner(w, z) == 0 for z in (c, u, v, uv))
    D = sp.Matrix.hstack(c, u, v, uv, w,
                         star(u, w), star(v, w), star(uv, w))
    assert D.T * q * D == I
    phi = D.inv()

    # Complete native Cayley--Dickson multiplication-table check.
    for i, j in product(range(8), repeat=2):
        assert phi * star(D[:, i], D[:, j]) == sp.Matrix(
            native_mul(e[i], e[j])
        ), ('Cayley table', i, j)

    g0, g1, g2 = phi * right, phi * left, phi
    assert all(M.T * M == q for M in (g0, g1, g2))
    for i, j in product(range(8), repeat=2):
        assert g2 * mu(e[i], e[j]) == sp.Matrix(
            native_mul(g0 * e[i], g1 * e[j])
        ), ('related triple', i, j)
    return g0, g1, g2

def test_synthetic():
    """Independent rational, nontrivially rotated octonionic composition."""
    def qmul(a, b):
        x,y,z,t=a; u,v,w,r=b
        return (x*u-y*v-z*w-t*r, x*v+y*u+z*r-t*w,
                x*w-y*r+z*u+t*v, x*r+y*w-z*v+t*u)
    def qc(a): return (a[0],-a[1],-a[2],-a[3])
    def qa(a,b): return tuple(x+y for x,y in zip(a,b))
    def qs(a,b): return tuple(x-y for x,y in zip(a,b))
    def octmul(a,b):
        x,y=list(a[:4]),list(a[4:]); u,v=list(b[:4]),list(b[4:])
        return qs(qmul(x,u), qmul(qc(v),y)) + qa(
            qmul(v,x), qmul(y,qc(u)))
    I=sp.eye(8)
    def rot(i,j):
        M=I.copy()
        M[i,i]=sp.Rational(3,5); M[j,j]=sp.Rational(3,5)
        M[i,j]=-sp.Rational(4,5); M[j,i]=sp.Rational(4,5)
        return M
    A,B,C=rot(0,6),rot(1,4),rot(2,7)
    mu=lambda x,y:C.T*sp.Matrix(octmul(A*x,B*y))
    maps=recover(mu,I,I,octmul)
    assert all(M.T*M==I for M in maps)
    print('PASS synthetic rational related triple and 64 native products')

def test_repository():
    p=runpy.run_path(str(Path(__file__).with_name(
        'check_griess1990_native_albert_rational_peirce_isometry.py')))
    B, sourceprod = p['B'], p['prod']
    slots=[p['S01'],p['S12'],p['S02']]
    q=p['G']/2; W=p['W']
    assert W.T*W==q
    S=[[[sp.Rational(3)*B(sourceprod(slots[0][i],slots[1][j]),
                         slots[2][k])[0] for k in range(8)]
        for j in range(8)] for i in range(8)]
    invq=q.inv()
    def mu(x,y):
        return invq*sp.Matrix([
            sum((x[i]*y[j]*S[i][j][k]
                 for i,j in product(range(8),repeat=2)),sp.Rational(0))
            for k in range(8)])
    def native_mul(x,y):
        return tuple(map(sp.Rational,
                         p['octmul'](tuple(x),tuple(y))))
    g0,g1,g2=recover(mu,q,W,native_mul)

    for i,j,k in product(range(8),repeat=3):
        got=sp.Matrix(native_mul(g0[:,i],g1[:,j]))
        assert (got.T*g2[:,k])[0]==S[i][j][k]
    print('PASS 512/512 Griess1990 source triality coefficients')

    # Transfer on ALL THREE source Peirce slots, not just the selected pair.
    change=sp.eye(27)
    Winv=W.inv()
    for start,F in ((3,g0),(11,g2),(19,g1)):
        block=F*Winv
        for i,j in product(range(8),repeat=2):
            change[start+i,start+j]=block[i,j]
    oldmap=p['mapped']
    nativeJordan=p['jordanNative']
    basis=p['srcbasis']
    assert len(basis)==27
    newmap=lambda v:change*oldmap(v)
    for i,j in product(range(27),repeat=2):
        lhs=newmap(sourceprod(basis[i],basis[j]))
        rhs=nativeJordan(newmap(basis[i]),newmap(basis[j]))
        assert lhs==rhs, ('FULL JORDAN',i,j,lhs-rhs)
    assert newmap(p['m']['unit'])==sp.Matrix([1,1,1]+[0]*24)
    gram=p['nativeGram']
    for i,j in product(range(27),repeat=2):
        assert (newmap(basis[i]).T*gram*newmap(basis[j]))[0] == (
            sp.Rational(3)*B(basis[i],basis[j])[0])
    print('PASS 729/729 full Griess1990 -> native rational H3(O) Jordan products')
    print('PASS unit and trace-pair preservation on 27D basis')
    print('Q-rational Peirce-slot matrices, order (01,12,02):')
    for i,M in enumerate((g0,g1,g2)):
        print('slot',i,'=',M)
    print('SOURCE-WRITTEN exact Python; no Lean kernel receipt')

if __name__=='__main__':
    test_synthetic()
    test_repository()

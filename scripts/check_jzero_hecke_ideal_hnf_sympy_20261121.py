#!/usr/bin/env python3
"""SymPy exact: true integral-ideal HNF, Euclidean generator and CM ray value.

Eisenstein ideals are Z² lattices. Build (z) by columns z, omega*z;
recover a generator from the HNF columns by Euclidean gcd. Multiply
ideals using all four products of their HNF basis vectors (NOT merely
multiplying hand-chosen generators). Require principal norm and
ray-normalized character multiplicativity. Exact finite regression
only; no kernel/CI or global analytic L-series claim.
"""
from itertools import product
from math import gcd
from fractions import Fraction
from sympy import Matrix, symbols, expand, __version__
from sympy.matrices.normalforms import hermite_normal_form

UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d,a*d+b*c-b*d
def norm(z):
    a,b=z
    return a*a-a*b+b*b
def conj(z):return z[0]-z[1],-z[1]
def key(z):return z[0]%2,z[1]%2,(z[0]+z[1])%3
def coprime(z):return z!=(0,0) and gcd(norm(z),6)==1
def normalize(z):
    assert coprime(z)
    solutions=[mul(u,z) for u in UNITS if key(mul(u,z))==(1,0,1)]
    assert len(solutions)==1
    return solutions[0]
def lattice(z):
    a,b=z
    return hermite_normal_form(Matrix([[a,-b],[b,a-b]]))
def rounded(q):
    return (2*q.numerator+q.denominator)//(2*q.denominator)
def divrem(x,y):
    n=norm(y)
    assert n>0
    t=mul(x,conj(y))
    q=(rounded(Fraction(t[0],n)),rounded(Fraction(t[1],n)))
    v=mul(q,y)
    r=(x[0]-v[0],x[1]-v[1])
    assert norm(r)<n
    return r
def egcd(x,y):
    while y!=(0,0):x,y=y,divrem(x,y)
    return x
def ideal_generator(H):
    x=(int(H[0,0]),int(H[1,0]))
    y=(int(H[0,1]),int(H[1,1]))
    z=egcd(x,y)
    assert norm(z)==int(H.det()) and lattice(z)==H
    return z
def psi(H):
    return normalize(ideal_generator(H))
def multiply_ideals(H,K):
    cols=[]
    for i,j in product(range(2),repeat=2):
        x=(int(H[0,i]),int(H[1,i]))
        y=(int(K[0,j]),int(K[1,j]))
        cols.append(Matrix(mul(x,y)))
    return hermite_normal_form(Matrix.hstack(*cols))
def main():
    a,b,c,d=symbols('a b c d',integer=True)
    q=(a*c-b*d,a*d+b*c-b*d)
    assert expand(norm(q)-norm((a,b))*norm((c,d)))==0
    elements=[(a,b) for a,b in product(range(-6,7),repeat=2) if coprime((a,b))]
    ideals={tuple(lattice(z)):lattice(z) for z in elements}
    for z in elements:
        H=lattice(z)
        assert psi(H)==normalize(z)
        for u in UNITS:
            assert lattice(mul(u,z))==H
            assert normalize(mul(u,z))==normalize(z)
    assert len(elements)==80 and len(ideals)==20
    tests=0
    for H,K in product(ideals.values(),repeat=2):
        HK=multiply_ideals(H,K)
        assert HK==lattice(mul(ideal_generator(H),ideal_generator(K)))
        assert int(HK.det())==int(H.det()*K.det())
        assert psi(HK)==mul(psi(H),psi(K))
        tests+=1
    choices=0
    for z in elements[:64]:
        H=lattice(z)
        for u in UNITS:
            assert lattice(mul(u,z))==H and psi(H)==normalize(mul(u,z))
            choices+=1
    print('SymPy',__version__)
    print('PASS symbolic Eisenstein norm multiplicativity')
    print(f'PASS {len(elements)} generators represented by {len(ideals)} exact ideal HNFs')
    print(f'PASS {tests} actual ideal-lattice product, norm and ray-character comparisons')
    print(f'PASS {choices} unit-associate independence controls')
    print('OPEN fractional ideal domain, conductor minimality, infinity type, bad primes 2/3, global L-series')
if __name__=='__main__':main()

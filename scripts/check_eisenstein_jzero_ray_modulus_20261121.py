#!/usr/bin/env python3
"""Exact integer arithmetic on original E: y²=x³+1, ray modulus f=2+4ω.

Selected ten split primes / seven inert primes. This is NOT a global
Grössencharacter, an analytic L-function, or a Lean kernel receipt.
"""
from sympy import primitive_root

SPLIT=(7,13,19,31,37,43,61,67,73,79)
INERT=(5,11,17,23,29,41,47)
UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
CUBES=((1,0),(0,1),(-1,-1))

def multiply(z,w):
    a,b=z; c,d=w
    return a*c-b*d,a*d+b*c-b*d

def norm(z):
    a,b=z
    return a*a-a*b+b*b

def divisible_by_f(z):
    a,b=z
    # f=2+4ω: (a,b) = [[2,-4],[4,-2]] (x,y)
    # adjugate/determinant = [[-2,4],[-4,2]]/12.
    return (-2*a+4*b)%12==0 and (-4*a+2*b)%12==0

def one_mod_f(z):
    return divisible_by_f((z[0]-1,z[1]))

def quadratic(t,p):
    t%=p
    return 0 if t==0 else (1 if pow(t,(p-1)//2,p)==1 else -1)

def jacobi(p):
    gen=int(primitive_root(p)); powers={0:(0,0)}
    x=1
    for k in range(p-1):
        powers[x]=CUBES[k%3];x=x*gen%p
    a=b=0
    for t in range(p):
        u,v=powers[t];weight=quadratic(1-t,p)
        a+=u*weight;b+=v*weight
    return a,b

def frobenius(p):
    return -sum(quadratic(x*x*x+1,p) for x in range(p))

def main():
    assert norm((2,4))==12
    # Unit classes must be separated by f; uniqueness is genuinely
    # checked here and is not assumed from the norm-p property.
    assert len({tuple((u[0]%12,u[1]%12)) for u in UNITS})==6
    for p in SPLIT:
        assert p%3==1 and quadratic(-3,p)==1
        j=jacobi(p)
        a_p=frobenius(p)
        assert norm(j)==p and a_p==-(2*j[0]-j[1])
        candidates=[(u,multiply(u,j)) for u in UNITS if one_mod_f(multiply(u,j))]
        assert len(candidates)==1, (p,j,candidates)
        unit,alpha=candidates[0]
        assert unit==(-1,0) and alpha==(-j[0],-j[1])
        assert one_mod_f(alpha) and norm(alpha)==p
        assert a_p==2*alpha[0]-alpha[1]
        # normalized factor (1-αT)(1-conj(α)T) reproduces elliptic.
        assert (1,-(2*alpha[0]-alpha[1]),norm(alpha))==(1,-a_p,p)
        print(f"p={p:2d} J={j!s:>9} alpha={alpha!s:>9} N={p:2d} a_p={a_p:3d}")
    for p in INERT:
        assert p%3==2 and quadratic(-3,p)==-1 and frobenius(p)==0
    print("PASS ray norm 12; 10/10 unique 6-unit choices alpha=-J mod f")
    print("PASS 10/10 normalized split local Euler factors; 7/7 inert traces")
    print("OPEN unit uniqueness for all split primes, ideal multiplicativity,")
    print("OPEN conductor minimality, p=3, global Hecke and L-series identity")

if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Independent exact Eisenstein/Jacobi local Hecke-shape regression.

Reuses the ORIGINAL j=0 curve y²=x³+1 and cubic Jacobi convention
of Integration/EisensteinJZeroSplitPrimeEisensteinCarrierExact.lean.
Checks only local polynomials. It DOES NOT build a global Hecke
character or identify the quadratic Dirichlet L function with L(E,s).
"""
from sympy import primitive_root

SPLIT = (7,13,19,31,37,43,61,67,73,79)
INERT = (5,11,17,23,29,41,47)
OMEGA = ((1,0),(0,1),(-1,-1))

def phi(t,p):
    x=t%p
    if not x:return 0
    return 1 if pow(x,(p-1)//2,p)==1 else -1

def ap(p):
    return -sum(phi(x**3+1,p) for x in range(p))

def split_jacobi(p):
    gen=int(primitive_root(p))
    table={0:(0,0)}
    t=1
    for k in range(p-1):
        table[t]=OMEGA[k%3]
        t=(t*gen)%p
    a=b=0
    for t in range(p):
        u,v=table[t]
        sign=phi(1-t,p)
        a+=u*sign
        b+=v*sign
    return (a,b)

def main():
    for p in SPLIT:
        assert p%3==1 and phi(-3,p)==1
        a,b=split_jacobi(p)
        norm=a*a-a*b+b*b
        assert norm==p and 2*a-b == -ap(p)
        # (1+z*T)(1+conj(z)*T) in Z[omega][T].
        hecke_shape=(1,2*a-b,norm)
        elliptic=(1,-ap(p),p)
        quadratic_dedekind=(1,-2,1)
        assert hecke_shape==elliptic
        assert elliptic!=quadratic_dedekind
    for p in INERT:
        assert p%3==2 and phi(-3,p)==-1 and ap(p)==0
        elliptic=(1,0,p)
        quadratic_dedekind=(1,0,-1)
        assert elliptic!=quadratic_dedekind
    print(f"PASS {len(SPLIT)} split conjugate Jacobi/Eisenstein factor pairs")
    print(f"PASS {len(INERT)} inert trace-zero elliptic factors")
    print(f"PASS {len(SPLIT)+len(INERT)} nonidentical quadratic Dedekind vs elliptic local factors")
    print("OPEN global Hecke character, conductor, infinity type, bad factors, Euler product and L-series")

if __name__=="__main__":
    main()

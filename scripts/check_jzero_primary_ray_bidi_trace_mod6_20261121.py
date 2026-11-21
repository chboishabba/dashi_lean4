#!/usr/bin/env python3
"""Exact j=0 original primary↔ray and six-unit acceptance.

For all p>3, p<2000 (301 primes), count E:y²=x³+1 via χ₂ and
assert #E(F_p) divisible by 6. On all 148 split primes, enumerate ALL
12 norm-p Eisenstein elements and all 6 unit choices; compare the
ORIGINAL #73 predicate IsJZeroPrimary to congruence modulo 2+4ω.

This is exhaustive for the finite tested interval only: no Lean kernel
receipt and no universal proof of divisibility of #E(F_p) by 6.
"""
from math import isqrt

UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))

def primes_below(limit):
    for p in range(5,limit):
        if all(p%d for d in range(2,isqrt(p)+1)):
            yield p

def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d, a*d+b*c-b*d

def norm(z):
    a,b=z
    return a*a-a*b+b*b

def ray_one(z):
    a=z[0]-1; b=z[1]
    return ((-2*a+4*b)%12==0 and (-4*a+2*b)%12==0)

def primary(z):
    a,b=z
    return b%2==0 and (2*a-b-2)%3==0

def quadratic(t,p):
    t%=p
    return 0 if t==0 else (1 if pow(t,(p-1)//2,p)==1 else -1)

def frobenius(p):
    return -sum(quadratic(x*x*x+1,p) for x in range(p))

def norm_shell(p):
    # |a|,|b|≤sqrt(4p/3), derivable from norm-p coercivity.
    bnd=isqrt(4*p//3)+3
    return [(a,b) for a in range(-bnd,bnd+1)
                  for b in range(-bnd,bnd+1) if norm((a,b))==p]

def main():
    count=split=elements=0
    for p in primes_below(2000):
        trace=frobenius(p)
        assert (p+1-trace)%6==0,(p,trace)
        count+=1
        if p%3==2:
            assert trace==0,(p,trace)
            continue
        split+=1
        assert trace%6==2,(p,trace)
        shell=norm_shell(p)
        assert len(shell)==12,(p,len(shell))
        for z in shell:
            assert primary(z)==ray_one(z),(p,z)
            choices=[u for u in UNITS if ray_one(mul(u,z))]
            assert len(choices)==1,(p,z,choices)
            elements+=1
    assert count==301 and split==148 and elements==1776,(count,split,elements)
    print(f"PASS {count}/301 finite prime field point counts: 6 divides #E(F_p)")
    print(f"PASS {split}/148 split traces a_p ≡ 2 (mod 6)")
    print(f"PASS {elements}/1776 original norm-p elements: primary iff ray-one")
    print(f"PASS {elements}/1776 unique 6-unit ray normalizers")
    print("OPEN all-prime finite-field 6-torsion and original #69 Jacobi↔#73 source merge")
    print("OPEN local Lean kernel acceptance, actual Hecke ideal character, global L-series")

if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""Exact commuting square/cube and CRT unit decomposition for Eisenstein CM.

Weld to original O_K = Z[omega], omega^2 + omega + 1 = 0,
ray modulus f = 2 sqrt(-3) = 2+4 omega.

Complete 12-element quotient CRT R/(f) = F4 x F3;
its 6 units = C3 x C2 and equal the images of original mu6.
For u in mu6, u = u^3 u^4 (because 3+4 = 7 = 1 mod 6).
The cube projects into sign C2, fourth power into cubic C3;
the two actions commute. Their quotient components are separate:
   u^3 = 1 mod 2, and u^4 = 1 mod sqrt(-3).

Finite exact model of all residue classes and all six units, as well as
selected integral principal ray normalizations. No Lean kernel or GRH claim.
"""
from itertools import product
from math import gcd
from sympy import symbols, expand, __version__

UNIT_CODES = ((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
ONE=(1,0)
MOD=(2,4)

def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d, a*d+b*c-b*d

def power(z,n):
    q=ONE
    while n:
        if n&1:q=mul(q,z)
        z=mul(z,z);n>>=1
    return q

def norm(z):
    a,b=z;return a*a-a*b+b*b

def res(z):
    a,b=z
    return a%2,b%2,(a+b)%3

def mul_res(x,y):
    # F4: omega^2 = omega + 1 mod 2; F3: omega = 1
    a,b,t=x;c,d,s=y
    return ((a*c-b*d)%2,(a*d+b*c-b*d)%2,(t*s)%3)

def rpow(x,n):
    q=res(ONE)
    for _ in range(n):q=mul_res(q,x)
    return q

def ray_one(z):
    return res(z)==res(ONE)

def is_coprime(z):
    return gcd(norm(z),6)==1

def normalizer(z):
    assert is_coprime(z)
    candidates=[u for u in UNIT_CODES if ray_one(mul(u,z))]
    assert len(candidates)==1,(z,candidates)
    return candidates[0]

def main():
    x,y,z,w=symbols('x y z w',integer=True)
    A=x*z-y*w; B=x*w+y*z-y*w
    assert expand(A*A-A*B+B*B-(x*x-x*y+y*y)*(z*z-z*w+w*w))==0
    # Linear CRT variables: a+b mod 3 is a ring map due to omega -> 1.
    assert expand(A+B-(x+y)*(z+w))==-3*y*w
    reps={res((a,b)):(a,b) for a,b in product(range(6),repeat=2)}
    assert len(reps)==12
    for rx,ry in product(reps,repeat=2):
        assert mul_res(rx,ry)==res(mul(reps[rx],reps[ry]))
    # Complete quotient unit classification, not sampling.
    allres=tuple(sorted(reps))
    quot_units=[r for r in allres if any(mul_res(r,s)==res(ONE) for s in allres)]
    assert len(quot_units)==6
    assert set(quot_units)=={res(u) for u in UNIT_CODES}
    # Exact C2 x C3 image of the six actual source units.
    classes2=set();classes3=set()
    for u in UNIT_CODES:
        assert power(u,6)==ONE
        sign=power(u,3); cubic=power(u,4)
        assert power(sign,2)==ONE
        assert power(cubic,3)==ONE
        assert mul(sign,cubic)==u and mul(cubic,sign)==u
        assert power(power(u,2),3)==power(power(u,3),2)==ONE
        # Canonical projection: sign invisible in F4, cubic invisible in F3.
        assert res(sign)[:2]==res(ONE)[:2]
        assert res(cubic)[2]==1
        # Projections commute, preserving multiplicative character.
        assert power(mul(sign,cubic),6)==ONE
        classes2.add(sign);classes3.add(cubic)
    assert len(classes2)==2 and len(classes3)==3
    for u,v in product(UNIT_CODES,repeat=2):
        assert power(mul(u,v),3)==mul(power(u,3),power(v,3))
        assert power(mul(u,v),4)==mul(power(u,4),power(v,4))
        assert mul(power(u,3),power(v,4))==mul(power(v,4),power(u,3))
    # Both quotient coordinates must be taken simultaneously; dropping
    # either conductor factor loses one of two group components.
    two_kernel={u for u in UNIT_CODES if res(u)[:2]==res(ONE)[:2]}
    three_kernel={u for u in UNIT_CODES if res(u)[2]==res(ONE)[2]}
    full_kernel={u for u in UNIT_CODES if res(u)==res(ONE)}
    assert two_kernel=={ONE,(-1,0)}
    assert three_kernel=={ONE,(0,1),(-1,-1)}
    assert full_kernel=={ONE}
    # The six-unit action on coprime Z[omega] representatives has a
    # unique inverse CRT unit, and the C2/C3 components commute.
    accepted=0
    for a,b in product(range(-12,13),repeat=2):
        q=(a,b)
        if not is_coprime(q):continue
        u=normalizer(q)
        sign,cubic=power(u,3),power(u,4)
        assert mul(mul(sign,cubic),q)==mul(mul(cubic,sign),q)
        assert ray_one(mul(mul(sign,cubic),q))
        # Solve the F4 and F3 unit constraints separately.
        ru=res(q)
        assert mul_res(res(cubic),ru)[:2]==res(ONE)[:2]
        assert mul_res(res(sign),ru)[2]==1
        accepted+=1
    print('SymPy',__version__)
    print('PASS 12 quotient CRT classes, 144 exact ring products, 6 quotient units')
    print('PASS 6/6 Eisenstein units: u=u^3*u^4=u^4*u^3, C2 x C3')
    print('PASS 36/36 two-unit ordered commutation and multiplicative projection pairs')
    print('PASS all conductor kernels: mod 2 loses sign; mod sqrt(-3) loses cubic')
    print(f'PASS {accepted} coprime integer generators with commuting CRT normalization')
    print('OPEN: full same-object ideal character proof, conductor exponents, analytic L-series')

if __name__=='__main__':main()

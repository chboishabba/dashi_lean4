#!/usr/bin/env python3
"""Exact SymPy/integers: O_K/(2sqrt(-3)) = F4 x F3 and ray normalization.

O_K=Z[omega], omega^2+omega+1=0. f=2+4omega, norm(f)=12.
Residue key (a%2,b%2,(a+b)%3) is the explicit CRT quotient map.

This is a complete finite quotient certificate plus bounded exact tests,
NOT Lean kernel acceptance, NOR a global Hecke ideal character/L-series.
"""
from itertools import product
from math import gcd
from sympy import symbols, expand, primerange, primitive_root, __version__ as sympy_version

F=(2,4)
UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
OMEGA=((1,0),(0,1),(-1,-1))

def add(z,w):
    return z[0]+w[0],z[1]+w[1]

def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d,a*d+b*c-b*d

def norm(z):
    a,b=z
    return a*a-a*b+b*b

def key(z):
    a,b=z
    return a%2,b%2,(a+b)%3

def ray_one(z):
    return key(z)==key((1,0))

def coprime(z):
    return gcd(norm(z),6)==1

def quotient_by_f(z):
    a,b=z
    x,y=-2*a+4*b,-4*a+2*b
    if x%12 or y%12:return None
    q=x//12,y//12
    assert mul(F,q)==z
    return q

def normalize(z):
    assert coprime(z),(z,norm(z))
    candidates=[u for u in UNITS if ray_one(mul(u,z))]
    assert len(candidates)==1,(z,candidates)
    return mul(candidates[0],z),candidates[0]

def quadratic(x,p):
    x%=p
    return 0 if x==0 else (1 if pow(x,(p-1)//2,p)==1 else -1)

def jacobi(p):
    g=int(primitive_root(p));psi={0:(0,0)};x=1
    for j in range(p-1):
        psi[x]=OMEGA[j%3];x=x*g%p
    a=b=0
    for t in range(p):
        u,v=psi[t];q=quadratic(1-t,p)
        a+=q*u;b+=q*v
    return a,b

def main():
    a,b,c,d=symbols("a b c d",integer=True)
    prod=(a*c-b*d,a*d+b*c-b*d)
    assert expand(norm(prod)-norm((a,b))*norm((c,d)))==0
    assert expand(prod[0]+prod[1]-(a+b)*(c+d))==-3*b*d
    classes=set(product(range(2),range(2),range(3)))
    reps={key((a,b)):(a,b) for a,b in product(range(6),repeat=2)}
    assert len(classes)==12 and set(reps)==classes
    for z,w in product(reps.values(),repeat=2):
        zz=add(z,mul(F,(1,-2)));ww=add(w,mul(F,(2,3)))
        assert key(zz)==key(z) and key(ww)==key(w)
        assert key(mul(zz,ww))==key(mul(z,w))
    unit_classes={key(u) for u in UNITS}
    residue_units={key(z) for z in reps.values() if coprime(z)}
    assert len(unit_classes)==6 and unit_classes==residue_units
    for z in reps.values():
        if coprime(z):normalize(z)
    candidates=[(a,b) for a,b in product(range(-12,13),repeat=2)
                if coprime((a,b))]
    for z in candidates:
        normal,_=normalize(z)
        assert ray_one(normal) and norm(normal)==norm(z)
        assert quotient_by_f((normal[0]-1,normal[1])) is not None
        for u in UNITS:
            assert normalize(mul(u,z))[0]==normal
    subset=candidates[::max(1,len(candidates)//120)]
    pairs=0
    for z,w in product(subset,repeat=2):
        assert normalize(mul(z,w))[0]==mul(normalize(z)[0],normalize(w)[0])
        pairs+=1
    split=0
    for p in primerange(7,2000):
        if p%3!=1:continue
        split+=1
        j=jacobi(int(p))
        assert norm(j)==p
        normal,u=normalize(j)
        assert u==(-1,0) and normal==(-j[0],-j[1])
    assert split==148
    for z in ((2,0),(1,2),(3,0),(2,4)):
        assert not coprime(z)
    print("SymPy",sympy_version)
    print("PASS 12/12 quotient elements and 6/6 unit classes (F4 x F3)")
    print("PASS 144/144 quotient multiplication pairs under shifted representatives")
    print(f"PASS {len(candidates)} coprime generator unit normalizations")
    print(f"PASS {pairs} exact ordered generator-pair multiplicativity checks")
    print(f"PASS {split}/148 canonical split Jacobi values normalized by -1")
    print("PASS negative controls: norms divisible by 2 or 3 excluded")
    print("OPEN: actual all-ideal character, infinity type, conductor proof, L-series")

if __name__=="__main__":main()

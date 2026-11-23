#!/usr/bin/env python3
"""Exhaust 28 one-plane SO(8) rotations under BOTH frozen original
coordinate target norm ||T||²=507/8 and target coordinate overlap=121/16.
Exact elimination over Q of rational tangent-half-angle parameter t
finds no one-plane solution. Multi-plane Spin8 maps are NOT excluded.
Original source Griess (1990), existing Lean #52 selected Albert map.
"""
from itertools import combinations,product
from fractions import Fraction as F
from pathlib import Path
import runpy,sympy as s
p=runpy.run_path(str(Path(__file__).with_name(
    "check_griess1990_native_albert_rational_peirce_isometry.py")))
a,b,c=p["S01"],p["S12"],p["S02"]
X,Y,Z=p["X01"],p["X12"],p["X02"]
mul,B,omul=p["prod"],p["B"],p["octmul"]
src=[];tar=[];V=[];W=[]
for i,j,k in product(range(8),repeat=3):
    v=omul(X[i],Y[j]);w=Z[k]
    src.append(F(3*B(mul(a[i],b[j]),c[k])[0]))
    tar.append(sum((x*y for x,y in zip(v,w)),F(0)))
    V.append(v);W.append(w)
dot=lambda u,v:sum((x*y for x,y in zip(u,v)),F(0))
t=s.symbols("t");co=(1-t*t)/(1+t*t);si=2*t/(1+t*t)
found=[]
for x,y in combinations(range(8),2):
    A=[v[x]*w[x]+v[y]*w[y] for v,w in zip(V,W)]
    D=[v[y]*w[x]-v[x]*w[y] for v,w in zip(V,W)]
    dn=(2*(co-1)*dot(tar,A)+2*si*dot(tar,D)+
        (co-1)**2*dot(A,A)+2*(co-1)*si*dot(A,D)+si**2*dot(D,D))
    dc=(co-1)*dot(src,A)+si*dot(src,D)+s.Rational(5,16)
    pn=s.Poly(s.together(dn).as_numer_denom()[0],t,domain=s.QQ)
    pc=s.Poly(s.together(dc).as_numer_denom()[0],t,domain=s.QQ)
    if s.gcd(pn,pc).degree()>0:found.append((x,y))
assert not found
print("PASS 28 exact one-plane SO8 elimination tests: no simultaneous frozen raw norm and overlap 121/16")
print("DOES NOT EXCLUDE two-plane rotations, entire SO8, or source canonical Spin8 triality")

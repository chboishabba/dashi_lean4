#!/usr/bin/env python3
"""Exact Griess original punctured 27 -> Albert26 rational C13 intertwiner.

External mathematics: R. L. Griess Jr., J Algebra 131 (1990), 281-293,
DOI 10.1016/0021-8693(90)90176-O; Maschke and cyclotomic C13 theory.
DASHI reuses its PREEXISTING native rational traceless Albert26
operator matrix. No invented octonion or fake same-graph action.
Exact computation is NOT a Lean/Agda kernel proof.

Usage: python checker.py griess1990_order13_traceless26_certificate.json
"""
from pathlib import Path
from itertools import product
import json,sys
import sympy as s
if len(sys.argv)!=2:raise SystemExit('usage: checker.py native_albert26_certificate.json')
data=json.loads(Path(sys.argv[1]).read_text())
B=s.Matrix([[s.Rational(t) for t in row]
            for row in data['native_albert26_traceless_order13_matrix']])
I=s.eye(26)
assert B.shape==(26,26) and B**13==I
def shear(x,i,j):
    y=list(x);y[i]=(y[i]+y[j])%3
    return tuple(y)
def actor(x):
    for i,j in ((0,1),(1,2),(2,0)):x=shear(x,i,j)
    return x
remaining={x for x in product(range(3),repeat=3) if x!=(0,0,0)}
orbits=[]
while remaining:
    start=min(remaining);x=start;cyc=[]
    while x not in cyc:
        cyc.append(x);x=actor(x)
    assert x==start and len(cyc)==13
    remaining.difference_update(cyc)
    orbits.append(cyc)
assert len(orbits)==2 and orbits[0][0]==(0,0,1)
assert orbits[1][0]==(0,0,2)
def cyclic_columns(i):
    v=I[:,i];cols=[]
    for k in range(13):
        cols.append(v);v=B*v
    assert v==I[:,i]
    return cols
X=s.Matrix.hstack(*(cyclic_columns(0)+cyclic_columns(1)))
P=s.zeros(26)
for offset in (0,13):
    for k in range(13):P[offset+(k+1)%13,offset+k]=1
assert B*X==X*P and P**13==I
assert X.det()==-s.Rational(729,4096)
assert s.trace(B)==s.trace(P)==0
tampered=B.copy();tampered[0,0]+=1
assert tampered*X!=X*P
print('PASS original punctured27 grade 26 exactly two source order13 cycles')
print('PASS literal native Albert tracezero26 BX=XP, determinant -729/4096')
print('PASS negative control: altered B does not intertwine')
print('NOT an isomorphism of original P3^3 adjacency or Albert Jordan multiplication')
print('NOT kernel-checked')

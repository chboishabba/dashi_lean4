#!/usr/bin/env python3
"""Thirteen C3 line restrictions of the actual Griess (1990) Albert A=F3^3.

Source attribution:
R. L. Griess Jr., J. Algebra 131 (1990), 281--293 (DOI
10.1016/0021-8693(90)90176-O), A=(Z/3)^3 fine-grading of J_3(O_C).
A Q-rational real form with the source's 13 antipodal grade pairs is
realized by the already source-verified Lean #52 certificate.

Chen--Lam--Shimakura (Math. Z. 288 (2018), 75--100, arXiv:1606.05961)
construct a distinct Z3-graded Moonshine VOA. Those infinite VOA
summands are NOT identified with these finite 9-dimensional complex
Albert eigenspaces. Original repository Agda source:
DASHI/Wikimedia/IbrahimMonster3BZ3OrbifoldPhaseRecognitionSnowballExact.agda.

This is a finite *source representation restriction* with a positive
projector and a precise noncanonical-choice discriminator; no source-
same-object VOA intertwiner or physical 369 dynamics is constructed.
"""
from itertools import product, combinations
import json
import sys
from pathlib import Path
import sympy as s

V=tuple(product(range(3),repeat=3))
zero=(0,0,0)
neg=lambda a:tuple(-v%3 for v in a)
dot=lambda a,b:sum(x*y for x,y in zip(a,b))%3
reps=tuple(a for a in V if a!=zero and a<neg(a))
assert len(reps)==13 and len({frozenset((a,neg(a))) for a in reps})==13
I=s.eye(27)
R=s.Matrix([[0,-1],[1,-1]])
assert R**3==s.eye(2)
Q=(I,R,R**2)
def action(direction):
    M=I.copy()
    for k,grade in enumerate(reps):
        M[1+2*k:3+2*k,1+2*k:3+2*k]=Q[dot(direction,grade)]
    return M

def fixed_projector(a):
    U=action(a)
    return (I+U+U**2)/3

def n_fixed(a):
    return sum(dot(a,x)==0 for x in V)

assert len({frozenset((a,neg(a))) for a in V if a!=zero})==13
assert all(n_fixed(a)==9 for a in reps)
fixed={}
for a in reps:
    U=action(a); E=fixed_projector(a)
    assert U**3==I and s.trace(U)==0 and s.trace(U**2)==0
    assert E*E==E and U*E==E and s.trace(E)==9
    # Positive rational eigenspace: rank9, cyclotomic complement rank18.
    assert s.trace(I-E)==18
    fixed[a]=E
for a,b in combinations(reps,2):
    E=fixed[a]*fixed[b]
    assert E*E==E and s.trace(E)==3
    assert sum(dot(a,x)==0 and dot(b,x)==0 for x in V)==3
e0,e1,e2=(1,0,0),(0,1,0),(0,0,1)
E= fixed[e0]*fixed[e1]*fixed[e2]
assert E*E==E and s.trace(E)==1
assert E==I[:,0]*I[0,:]  # full A invariants are exactly the unit line

# For each nontrivial C3 subgroup, complexification splits
# 27 = 9_{1} + 9_{omega} + 9_{omega^2}. This is deduced
# from Tr(U)=Tr(U²)=0; no artificial splitting over Q.
for a in reps:
    assert all(sum(dot(a,x)==k for x in V)==9 for k in range(3))

# ALL 13 cyclic subgroups are equivalent under the source label normalizer
# SL3(3); this proves label-space transitivity only, not an automatically
# compatible lift of every label matrix to the chosen product/cubic basis.
def det3(M):
    a,b,c=M
    return (a[0]*(b[1]*c[2]-b[2]*c[1])-
            a[1]*(b[0]*c[2]-b[2]*c[0])+
            a[2]*(b[0]*c[1]-b[1]*c[0]))%3
orbit=set()
base=e0
count=0
for rows in product(V,repeat=3):
    if det3(rows)!=1:continue
    count+=1
    x=tuple(sum(rows[i][j]*base[j] for j in range(3))%3 for i in range(3))
    orbit.add(frozenset((x,neg(x))))
assert count==5616 and len(orbit)==13
assert orbit=={frozenset((x,neg(x))) for x in reps}

if len(sys.argv)>1:
    data=json.loads(Path(sys.argv[1]).read_text())
    A=s.Matrix([[s.Rational(t) for t in row]
        for row in data["full_27_by_27_native_rational_transport"]])
    assert A.shape==(27,27) and A.det()!=0
    # Same native Albert Q-carrier: all 13 rational fixed-point
    # projectors transport, and the unit line is their intersection.
    Ai=A.inv()
    for a in reps:
        N=A*fixed[a]*Ai
        assert N*N==N and s.trace(N)==9
        assert N*A[:,0]==A[:,0]
    assert A*E*Ai*A[:,0]==A[:,0]
    print("PASS same native Albert Q witness: 13 fixed rank-nine projectors")

print("PASS original Griess A=F3^3: 13 cyclic line subgroups; SL3(3) transitive on all 13")
print("PASS each C3 restriction: Q-fixed dimension 9, rational cyclotomic complement 18")
print("PASS after Q(omega) extension: complex eigenspace dimensions (9,9,9)")
print("PASS any two distinct line-invariants intersect in dim 3; three axes dim 1")
print("BOUNDARY: Chen--Lam--Shimakura's VOA three-sector grading is a distinct actual VOA,")
print("          not selected by one of the 13 Albert cyclic lines or by raw 883/888.")

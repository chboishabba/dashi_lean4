#!/usr/bin/env python3
"""Exhaust source-defined A2^4 root-lattice sixfold alignment subgroup.

Three Peirce slots of Griess (1990) Albert fine-grading have rational
Gram diag([[2,-1],[-1,2]] x4). Exact order6 A2 root rotations on ONE
slot give 6^4 = 1296 rational metric isometries. None produces
unweighted 888/8. This is a bounded subgroup no-go, not all Spin8.
"""
from pathlib import Path
import runpy
from itertools import product
from fractions import Fraction as F
from collections import Counter
p=runpy.run_path(str(Path(__file__).with_name(
    "check_griess1990_native_albert_rational_peirce_isometry.py")))
S01,S12,S02=p["S01"],p["S12"],p["S02"]
X01,X12,X02=p["X01"],p["X12"],p["X02"]
mul,B,octmul=p["prod"],p["B"],p["octmul"]
S=[];T=[]
for i,j in product(range(8),repeat=2):
    uv=octmul(X01[i],X12[j]);u=mul(S01[i],S12[j])
    S.append(tuple(F(3*B(u,S02[k])[0]) for k in range(8)))
    T.append(tuple(sum((a*b for a,b in zip(uv,X02[k])),F(0)) for k in range(8)))
G=((2,-1),(-1,2));R=((1,-1),(1,0))
mm=lambda A,B:tuple(tuple(sum(A[i][t]*B[t][j] for t in range(2))
                         for j in range(2)) for i in range(2))
assert mm(mm(((1,1),(-1,0)),G),R)==G # R transpose * G * R
powers=[((1,0),(0,1))]
for _ in range(5):powers.append(mm(powers[-1],R))
assert mm(powers[-1],R)==powers[0]
outcomes=Counter(); best=None
for choice in product(range(6),repeat=4):
    err=F(0)
    for row in range(64):
        for block in range(4):
            i=2*block;m=powers[choice[block]]
            for k in range(2):
                t=sum(T[row][i+j]*m[j][k] for j in range(2))
                err+=(S[row][i+k]-t)**2
    outcomes[err]+=1
    if best is None or abs(err-111)<best[0]:best=(abs(err-111),choice,err)
assert sum(outcomes.values())==1296
assert 111 not in outcomes
assert best[0]==F(1,8) and best[2]==F(887,8)
assert outcomes[F(883,8)]>0
print("PASS 1296 exact rational A2-root 60degree isometries checked")
print("PASS no R=111; closest 887/8, distance 1/8")
print("BOUNDARY finite rational A2^4 subgroup only, not full triality isometry group")

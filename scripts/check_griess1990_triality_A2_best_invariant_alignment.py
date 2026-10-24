#!/usr/bin/env python3
"""Optimal metric-corrected triality overlap in the finite rational A2^4
root-rotation subgroup (6^4 = 1296 choices) on a single Peirce slot.
Uses ORIGINAL source Griess1990 and native rational-octonion product
from the existing Lean #52 executable. No full Spin8 isomorphism claimed.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import runpy
p=runpy.run_path(str(Path(__file__).with_name(
    "check_griess1990_native_albert_rational_peirce_isometry.py")))
S01,S12,S02=p["S01"],p["S12"],p["S02"]
X01,X12,X02=p["X01"],p["X12"],p["X02"]
mul,B,octmul=p["prod"],p["B"],p["octmul"]
S={};T={}
for i,j,k in product(range(8),repeat=3):
    S[i,j,k]=F(3*B(mul(S01[i],S12[j]),S02[k])[0])
    T[i,j,k]=sum((a*b for a,b in zip(octmul(X01[i],X12[j]),X02[k])),F(0))
def mates(i):return ((i,F(2,3)),(i^1,F(1,3)))
raised={}
for i,j,k in product(range(8),repeat=3):
    raised[i,j,k]=sum((u*v*w*S[a,b,c] for a,u in mates(i)
                        for b,v in mates(j) for c,w in mates(k)),F(0))
K=[[sum((raised[i,j,k]*T[i,j,l] for i,j in product(range(8),repeat=2)),F(0))
    for k in range(8)] for l in range(8)]
G2=((2,-1),(-1,2));R=((1,-1),(1,0))
mul2=lambda A,B:tuple(tuple(sum(A[i][v]*B[v][j] for v in range(2))
                          for j in range(2)) for i in range(2))
assert mul2(mul2(((1,1),(-1,0)),G2),R)==G2
P=[((1,0),(0,1))]
for _ in range(5):P.append(mul2(P[-1],R))
assert mul2(P[-1],R)==P[0]
choices=[]
for g in range(4):
    results=[]
    for n,m in enumerate(P):
        overlap=sum((m[l][k]*K[2*g+l][2*g+k]
                   for l,k in product(range(2),repeat=2)),F(0))
        results.append((overlap,n))
    choices.append(max(results))
original_overlap=sum((K[k][k] for k in range(8)),F(0))
max_overlap=sum((v for v,n in choices),F(0))
assert original_overlap==F(3,4)
assert max_overlap==1
assert tuple(n for v,n in choices)==(5,1,1,5)
print("PASS 6^4 finite rational A2^4 search has exact separated optimum")
print("initial natural Gram-metric squared residual 29/2")
print("best subgroup Gram-metric squared residual",16-2*max_overlap)
print("best rational 60-degree lattice rotation powers",tuple(n for v,n in choices))
print("NO full Spin8/Albert product map or physically canonical 888 selected")

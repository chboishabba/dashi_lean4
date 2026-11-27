#!/usr/bin/env python3
"""Exact native rational-Albert Jordan Hamiltonian and S3 automorphism shadow.

The source implementations are Integration/RationalAlbertNative.lean and
Integration/RationalAlbertS3Native.lean. The diagonal selected Hamiltonian
h=(1,0,-1) multiplies each offdiagonal octonionic 8-slot by (d_i+d_j)/2,
so this is a source-precise coordinate evaluation. Python PASS is NOT
Lean/Lake kernel proof, Monster VOA mode, F4 classification or physics.
"""
from collections import Counter
import sympy as s

d=(s.Integer(1),s.Integer(0),s.Integer(-1))
weights=list(d)+[(d[1]+d[2])/2]*8+[(d[2]+d[0])/2]*8+[(d[0]+d[1])/2]*8
L=s.diag(*weights)
cycle={0:1,1:2,2:0}
for block in range(3):
    for j in range(8):
        cycle[3+8*block+j]=3+8*((block+1)%3)+j
P=s.zeros(27)
for old,new in cycle.items():P[new,old]=1
h=s.Matrix([1,0,-1]+[0]*24)
C=P*L-L*P
assert L==L.T and P.T*P==s.eye(27) and P**3==s.eye(27)
assert Counter(weights)==Counter({s.Integer(1):1,s.Integer(-1):1,
    s.Rational(1,2):8,s.Rational(-1,2):8,s.Integer(0):9})
assert P*h!=h and h.dot(h)==2
assert C.rank()==27 and s.trace(C.T*C)==18
assert (P*L*P.T).eigenvals()==L.eigenvals()
print("PASS actual source selected Albert L_h spectrum, traceform amplitude=2")
print("PASS native S3 cycle conjugates spectrum; commutator rank27, squared norm18")
print("LIMIT: no Lean kernel, Monster VOA, selected physical Hamiltonian or gravity bridge")

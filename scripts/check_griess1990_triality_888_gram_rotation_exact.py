#!/usr/bin/env python3
"""Exact Gram-correct triality tensor norm and the 883/8 -> 888/8 rotation.

Original: R. L. Griess Jr, J. Algebra 131 (1990), 281-293.
Native rational Albert and selected Peirce map: existing Lean PR #52.
Run the SAME repo owner; do not synthesize an unrelated 27D product.
R_coordinate=sum (S-T)^2 is not a basis-invariant trilinear norm.
The source-induced tensor norm uses G^-1 on each A2^4 Peirce factor.
"""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import runpy
import sympy as s

p=runpy.run_path(str(Path(__file__).with_name(
    "check_griess1990_native_albert_rational_peirce_isometry.py")))
S01,S12,S02=p["S01"],p["S12"],p["S02"]
X01,X12,X02=p["X01"],p["X12"],p["X02"]
prod,B,octmul=p["prod"],p["B"],p["octmul"]
S={};T={};A={};D={}
for i,j,k in product(range(8),repeat=3):
    xy=prod(S01[i],S12[j]); y=octmul(X01[i],X12[j]);z=X02[k]
    S[i,j,k]=F(3*B(xy,S02[k])[0])
    T[i,j,k]=sum((a*b for a,b in zip(y,z)),F(0))
    A[i,j,k]=y[0]*z[0]+y[6]*z[6]
    D[i,j,k]=y[6]*z[0]-y[0]*z[6]
def simple(f,g):return sum((f[a]*g[a] for a in f),F(0))
ss,tt,st=simple(S,S),simple(T,T),simple(S,T)
assert (ss,tt,st)==(F(251,4),F(507,8),F(63,8))
assert ss+tt-2*st==F(883,8)
def metric(f,g):
    out=F(0)
    for i,j,k in product(range(8),repeat=3):
        v=f[i,j,k]
        if not v:continue
        for a,wa in ((i,F(2,3)),(i^1,F(1,3))):
            for b,wb in ((j,F(2,3)),(j^1,F(1,3))):
                for c,wc in ((k,F(2,3)),(k^1,F(1,3))):
                    out+=v*wa*wb*wc*g[a,b,c]
    return out
ms,mt,mo=metric(S,S),metric(T,T),metric(S,T)
assert (ms,mt,mo)==(8,8,F(3,4))
assert ms+mt-2*mo==F(29,2)
# Rotate target coordinate plane (0,6) in the third 8D Peirce slot.
# This real SO8 move preserves the native positive octonion metric but
# mixes Q-valued coordinates with sqrt(3) at angle 60 degrees.
c,si=s.symbols("c si")
target2=(tt+2*(c-1)*simple(T,A)+2*si*simple(T,D)+
        (c-1)**2*simple(A,A)+2*(c-1)*si*simple(A,D)+si**2*simple(D,D))
overlap=st+(c-1)*simple(S,A)+si*simple(S,D)
res=s.expand(ss+target2-2*overlap)
res_circle=s.simplify(res.subs(si**2,1-c**2))
assert s.expand(res_circle-(893-10*c)/8)==0
at={c:s.Rational(1,2),si:s.sqrt(3)/2}
assert s.simplify(res.subs(at))==111
assert s.simplify(target2.subs(at))==s.Rational(509,8)+s.sqrt(3)/8
assert s.simplify(overlap.subs(at))==s.Rational(123,16)+s.sqrt(3)/16
assert s.simplify(target2.subs(at))!=tt
# Correct metric contraction remains intrinsically normalized, not 111.
ma,md=metric(S,A),metric(S,D)
assert (ma,md)==(F(-1,8),F(-1,24))
weighted_overlap=s.simplify(mo+(s.Rational(1,2)-1)*s.Rational(ma)
                            +s.sqrt(3)/2*s.Rational(md))
weighted_residual=s.simplify(16-2*weighted_overlap)
assert weighted_residual==s.Rational(115,8)+s.sqrt(3)/24
print("PASS coordinate residual 883/8 -> exactly 888/8 at selected SO8 60-degree rotation")
print("PASS 60-degree transform changes coordinate target norm and overlap")
print("PASS natural G^-1 tensor norms both 8; original weighted residual 29/2")
print("PASS weighted residual at 60deg =",weighted_residual,"(not 111)")
print("NOT source-derived canonical triality; NOT rational original-Q slot map")

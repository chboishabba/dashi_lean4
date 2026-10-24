#!/usr/bin/env python3
"""Exact 27D REAL trace-isometry from Griess1990 Albert homogeneous basis
to native rational octonionic H3(O) coordinate basis, with product audit.
Runs the existing source checker in this SAME repository. Original Jordan
source: Griess (1990); native rational Albert: Lean PR #52. New isometry
uses rational E8 A2^4 root frame and order8 Hadamard; preserves trace,
unit, positive metric, full Peirce 3+8+8+8 and each H2(O) same-slot
Jordan product. The cross-slot TRIALITY tensor is a checked open seam.
Python/SymPy is NOT a Lean kernel proof of a full Albert isomorphism.
"""
from pathlib import Path
from itertools import product,combinations
from fractions import Fraction as F
import runpy
import sympy as s
m=runpy.run_path(str(Path(__file__).with_name('check_griess1990_albert_peirce_rh_frame.py')))
X=m['X'];z=m['z'];idx=m['idx'];neg=m['neg'];Z=m['zero'];one=m['one']
w=m['w'];B=m['B'];bv=m['bv'];frame=m['frame'];P=m['P']
tau=m['tau'];combine=m['combine'];scale=m['scale'];prod=m['prod']
reps=tuple(x for x in X if x!=z and x<neg(x));assert len(reps)==13
rb=[bv(z)]
for a in reps:
  rb += [combine(bv(a),bv(neg(a))),
         combine(scale(w[1],bv(a)),scale(w[2],bv(neg(a))))]
assert len(rb)==27 and all(tau(v)==v for v in rb)
def co(v):
  assert tau(v)==v
  assert v[idx[z]][1]==0
  out=[v[idx[z]][0]]
  for a in reps:out.extend(v[idx[a]])
  return s.Matrix(out)
slots={}
for i,j in combinations(range(3),2):
  cols=[];vv=[]
  for v in rb:
    p=P[('O',i,j)](v);c=co(p)
    if s.Matrix.hstack(*cols,c).rank()>len(cols):
      cols.append(c);vv.append(p)
  assert len(vv)==8
  gram=s.Matrix(8,8,lambda k,l:s.Rational(3)*B(vv[k],vv[l])[0])
  goal=s.Matrix(8,8,lambda k,l:2 if k==l else (-1 if k//2==l//2 else 0))
  assert gram==goal
  slots[i,j]=vv
# E8 has 240 rational root vectors; greedily find an A2^4 root subsystem.
roots=[]
for i,j in combinations(range(8),2):
  for a,b in product((-1,1),repeat=2):
    r=[F(0)]*8;r[i]=F(a);r[j]=F(b);roots.append(tuple(r))
for signs in product((-1,1),repeat=8):
  if sum(a<0 for a in signs)%2==0:roots.append(tuple(F(a,2) for a in signs))
assert len(roots)==240
dot=lambda a,b:sum(u*v for u,v in zip(a,b))
u=(F(1),F(-1),F(0),F(0),F(0),F(0),F(0),F(0))
v=(F(0),F(1),F(-1),F(0),F(0),F(0),F(0),F(0))
chosen=[u,v]
for _ in range(3):
  pool=[a for a in roots if all(dot(a,b)==0 for b in chosen)]
  pair=next((a,b) for a in pool for b in pool if dot(a,b)==-1)
  chosen.extend(pair)
G=s.Matrix(8,8,lambda k,l:2 if k==l else (-1 if k//2==l//2 else 0))
R=s.Matrix.hstack(*[s.Matrix(r) for r in chosen])
assert R.T*R==G
had=s.Matrix([[(-1)**bin(i&j).count('1') for j in range(8)] for i in range(8)])
assert had.T*had==8*s.eye(8)
W=had*R/4
assert W.T*(2*s.eye(8))*W==G
srcbasis=frame[:]
for ij in combinations(range(3),2):srcbasis+=slots[ij]
S=s.Matrix.hstack(*[co(v) for v in srcbasis])
assert S.det()!=0
N=s.zeros(27)
for i in range(3):N[i,i]=1
for slot in range(3):
  for i in range(8):
    for j in range(8):N[3+8*slot+i,3+8*slot+j]=W[i,j]
T=N*S.inv()
def mapped(v):return T*co(v)
nativeGram=s.diag(*([1]*3+[2]*24))
for i,j in product(range(27),repeat=2):
  a,b=srcbasis[i],srcbasis[j]
  assert (mapped(a).T*nativeGram*mapped(b))[0]==3*B(a,b)[0]
assert mapped(m['bv'](z))==s.Matrix([1,1,1]+[0]*24)
# Actual native rational Cayley-Dickson octonion product (not a tensor toy).
Qzero=(F(0),)*4;Ozero=(F(0),)*8;Oone=(F(1),)+(F(0),)*7
def qmul(a,b):
  x,y,z,t=a;u,v,w,r=b
  return (x*u-y*v-z*w-t*r,x*v+y*u+z*r-t*w,
          x*w-y*r+z*u+t*v,x*r+y*w-z*v+t*u)
def qc(a):return (a[0],-a[1],-a[2],-a[3])
def qadd(a,b):return tuple(u+v for u,v in zip(a,b))
def qsub(a,b):return tuple(u-v for u,v in zip(a,b))
def octmul(a,b):
  x,y=a[:4],a[4:];u,v=b[:4],b[4:]
  return qsub(qmul(x,u),qmul(qc(v),y))+qadd(qmul(v,x),qmul(y,qc(u)))
def octconj(a):return qc(a[:4])+tuple(-v for v in a[4:])
def octadd(a,b):return tuple(u+v for u,v in zip(a,b))
def octscale(r,a):return tuple(r*u for u in a)
def hermitian(v):
  q=[F(a) for a in v]
  M=[[Ozero for _ in range(3)] for _ in range(3)]
  for i in range(3):M[i][i]=octscale(q[i],Oone)
  for slot,(i,j) in enumerate(combinations(range(3),2)):
    w=tuple(q[3+8*slot+k] for k in range(8))
    M[i][j]=w;M[j][i]=octconj(w)
  return M
def jordanNative(v,w):
  A=hermitian(v);B=hermitian(w)
  C=[[Ozero for _ in range(3)] for _ in range(3)]
  for i,j in product(range(3),repeat=2):
    out=Ozero
    for k in range(3):
      out=octadd(out,octadd(octmul(A[i][k],B[k][j]),octmul(B[i][k],A[k][j])))
    C[i][j]=octscale(F(1,2),out)
  out=[C[i][i][0] for i in range(3)]
  for i,j in combinations(range(3),2):out.extend(C[i][j])
  return s.Matrix(out)
for ij in combinations(range(3),2):
  subset=frame+slots[ij]
  for a,b in product(subset,repeat=2):
    assert mapped(prod(a,b))==jordanNative(mapped(a),mapped(b))
# Product across DIFFERENT Peirce slots depends on triality, and the
# independently chosen rational Gram isometry does NOT force it.
a=slots[0,1][0];b=slots[1,2][0]
residual=mapped(prod(a,b))-jordanNative(mapped(a),mapped(b))
r2=(residual.T*nativeGram*residual)[0]
assert r2==1
print('PASS actual Griess1990/Lean rational 27D linear + trace + real Peirce isometry')
print('PASS native Cayley-Dickson product on all 3 diagonal+8-slot subalgebras')
print('PASS exact E8 rational A2^4/Hadamard isometry, no sqrt2 extension')
print('TRIALITY NEGATIVE CONTROL: cross-slot product residual squared norm =',r2)
print('OPEN full product-compatible 8x8x8 triality map; no Monster VOA or RH result')

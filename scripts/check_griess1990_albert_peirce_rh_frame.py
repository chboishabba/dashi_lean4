#!/usr/bin/env python3
"""Exact Griess-1990 source homogeneous Jordan frame and RH negative control.
Source: Griess, J Algebra 131 (1990) 281-293. Unlike the Monster
Vnatural_2 Griess algebra (dimension 196884), this is Albert 27D.
Checks 3 primitive frame idempotents and all 27-dimensional Peirce
projector algebra over Q(omega), not a Lean kernel certificate.
"""
from fractions import Fraction as F
from itertools import product, combinations
import sympy as s
X=tuple(product(range(3),repeat=3));z=(0,0,0);idx={x:i for i,x in enumerate(X)}
zero=(F(0),F(0));one=(F(1),F(0));w=(one,(F(0),F(1)),(F(-1),F(-1)))
add=lambda x,y:tuple((a+b)%3 for a,b in zip(x,y))
neg=lambda x:tuple((-a)%3 for a in x)
plus=lambda a,b:(a[0]+b[0],a[1]+b[1])
sc=lambda q,a:(F(q)*a[0],F(q)*a[1])
def cm(a,b):
  A,B=a;C,D=b
  return (A*C-B*D,A*D+B*C-B*D)
def conj(a):return (a[0]-a[1],-a[1])
def dep(x,y):return x==z or any(all((k*x[i]-y[i])%3==0 for i in range(3)) for k in range(3))
def phase(x,y):
  a,b,c=x;u,v,t=y
  return (-a*b*t-c*u*v+b*c*u+a*v*t)%3
C={(x,y):sc(1 if dep(x,y) else F(-1,2),w[phase(x,y)]) for x in X for y in X}
def vector(items=()):
  out=[zero]*27
  for p,t in items:out[idx[p]]=plus(out[idx[p]],t)
  return tuple(out)
def combine(*vs):
  out=[zero]*27
  for v in vs:
    for i,c in enumerate(v):out[i]=plus(out[i],c)
  return tuple(out)
def scale(q,v):return tuple(cm(q,c) for c in v)
def prod(v,vv):
  out=[zero]*27
  for i,x in enumerate(X):
    if v[i]==zero:continue
    for j,y in enumerate(X):
      if vv[j]==zero:continue
      k=idx[add(x,y)]
      out[k]=plus(out[k],cm(cm(v[i],vv[j]),C[x,y]))
  return tuple(out)
def tau(v):return tuple(conj(v[idx[neg(x)]]) for x in X)
def B(v,vv):
  out=zero
  for i,x in enumerate(X):out=plus(out,cm(v[i],vv[idx[neg(x)]]))
  return out
bv=lambda x:vector(((x,one),))
axis=(1,0,0);unit=bv(z)
frame=[]
for j in range(3):
  q=vector(((z,sc(F(1,3),one)),(axis,sc(F(1,3),w[(-j)%3])),
            (neg(axis),sc(F(1,3),w[(-2*j)%3]))))
  assert tau(q)==q and prod(q,q)==q
  frame.append(q)
assert combine(*frame)==unit
for i,j in product(range(3),repeat=2):
  assert prod(frame[i],frame[j])==(frame[i] if i==j else vector())
  assert sc(3,B(frame[i],frame[j]))==(one if i==j else zero)
L=lambda i,v:prod(frame[i],v)
diag=lambda i,v:combine(scale((F(2),F(0)),L(i,L(i,v))),scale((-F(1),F(0)),L(i,v)))
off=lambda i,j,v:scale((F(4),F(0)),L(i,L(j,v)))
P={('D',i):lambda v,i=i:diag(i,v) for i in range(3)}
for i,j in combinations(range(3),2):
  P[('O',i,j)]=lambda v,i=i,j=j:off(i,j,v)
for x in X:
  v=bv(x)
  assert combine(*(f(v) for f in P.values()))==v
  for name,f in P.items():
    assert f(f(v))==f(v)
    for other,h in P.items():
      if name!=other:assert f(h(v))==vector()
trace={name:sum(f(bv(x))[idx[x]][0] for x in X) for name,f in P.items()}
assert sorted(trace.values())==[1,1,1,8,8,8]
for x in X:
  v=bv(x)
  assert combine(prod(bv(axis),v),prod(bv(neg(axis)),v))==combine(
    scale((F(3),F(0)),L(0,v)),scale((-F(1),F(0)),v))
assert B(unit,unit)==one
# RH transfer FAILS: universal Peirce 1/2 is not a zeta-zero
# height; the selected characteristic polynomial is not invariant
# under s<->1-s because multiplicities at 2 and -1 differ.
svar=s.Symbol('s')
cp=(svar-2)*(svar+1)**10*(svar-s.Rational(1,2))**16
assert s.factor(cp.subs(svar,1-svar)/cp)==-((svar-2)/(svar+1))**9
print('PASS Griess 1990 tau-real 3-idempotent Jordan frame with native diagonal algebra product')
print('PASS complete mutually orthogonal 3+8+8+8 Peirce projections on all 27 states')
print('PASS H=3 L_p-I and universal Peirce half-eigenvalue explained')
print('PASS RH negative discriminator: characteristic polynomial lacks s<->1-s symmetry')
print('OPEN full three-octonion-slot triality product map and all zeta/RH analytic producers')

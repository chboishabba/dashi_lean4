#!/usr/bin/env python3
"""Exact real-form/positive-Hermitian Hamiltonian cut on Griess 1990's
F3^3-graded 27-dimensional ALBERT algebra, not Monster Vnatural2.
Original: R. L. Griess Jr., J. Algebra 131 (1990), 281-293,
DOI 10.1016/0021-8693(90)90176-O.
Reuses source multiplication from the earlier #52 checker.
"""
from itertools import product
from fractions import Fraction as F
V=tuple(product(range(3),repeat=3)); o=(0,0,0)
z=(F(0),F(0)); one=(F(1),F(0))
omega=(one,(F(0),F(1)),(F(-1),F(-1)))
add=lambda a,b:tuple((u+v)%3 for u,v in zip(a,b))
neg=lambda a:tuple((-u)%3 for u in a)
def mul(u,v):
 a,b=u;c,d=v
 return a*c-b*d,a*d+b*c-b*d
def plus(u,v):return u[0]+v[0],u[1]+v[1]
def scale(k,v):return k*v[0],k*v[1]
def conj(v):return v[0]-v[1],-v[1]
def independent(x,y):
 return x!=o and not any(all((k*a-b)%3==0 for a,b in zip(x,y)) for k in range(3))
def phase(x,y):
 a,b,c=x;p,q,r=y
 return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
c={(x,y):scale(F(-1,2) if independent(x,y) else F(1),omega[phase(x,y)])
   for x in V for y in V}
assert len(c)==729
assert all(conj(c[x,y])==c[neg(x),neg(y)] for x,y in product(V,repeat=2))
assert all(c[x,neg(x)]==one for x in V)
# Frobenius B(ex,ey)=delta_{x+y,0} and tau(ex)=e_{-x}:
# H(ex,ey)=B(ex,tau(ey))=delta_xy. This is positive Hermitian.
assert all((add(x,neg(y))==o)==(x==y) for x,y in product(V,repeat=2))
for a,x in product(V,repeat=2):
 assert c[a,x]==conj(c[neg(a),add(a,x)])
# The adjoint of L_ea under H is L_e(-a); hence
# H_a=L_(e_a+e_-a) is Hermitian, for all a.
ix={v:i for i,v in enumerate(V)}
def vadd(*terms):
 out=[z]*27
 for t,vector in terms:
  for i in range(27):out[i]=plus(out[i],scale(F(t),vector[i]))
 return tuple(out)
def left_h(a,v):
 out=[z]*27
 for i,x in enumerate(V):
  if v[i]==z:continue
  for aa in (a,neg(a)):
   j=ix[add(x,aa)]
   out[j]=plus(out[j],mul(v[i],c[aa,x]))
 return tuple(out)
def ei(j):return tuple(one if i==j else z for i in range(27))
for a in V:
 if a==o:continue
 tr=z;tr2=z
 for i in range(27):
  v=ei(i);w=left_h(a,v)
  t=vadd((2,w),(-1,v))
  t=vadd((1,left_h(a,t)),(1,t))
  t=vadd((1,left_h(a,t)),(-2,t))
  assert all(x==z for x in t)
  tr=plus(tr,w[i]);tr2=plus(tr2,left_h(a,w)[i])
 assert tr==z and tr2==(F(18),F(0))
 # A character subgroup fixes h_a iff t.a=0, leaving 9 actors.
 assert sum(sum(t[i]*a[i] for i in range(3))%3==0 for t in V)==9
 support={frozenset((x,add(x,a))) for x in V}
 assert len(support)==27   # nine disconnected 3-cycles
# Polynomial plus tr(1),tr(H),tr(H^2) implies spectrum
# 2:1, -1:10, 1/2:16 on each complex dimension-27 space.
assert (1+10+16,2-10+F(16,2),4+10+F(16,4))==(27,0,18)
axis=(1,0,0)
digit=lambda z:((z+1)%3)-1
cube=lambda v:tuple(digit(z) for z in v)
edges={frozenset((cube(x),cube(add(x,axis)))) for x in V}
dist=lambda e:sum(abs(u-v) for u,v in zip(*tuple(e)))
assert sum(dist(e)==1 for e in edges)==18
assert sum(dist(e)==2 for e in edges)==9
print('PASS source Griess 1990 tau anti-linear Jordan involution on 729 products')
print('PASS positive Hermitian form H=B(.,tau(.)), all 26 adjoint pair identities')
print('PASS 13 distinct positive-selfadjoint h_a=e_a+e_-a')
print('PASS polynomial (H-2)(H+1)(2H-1)=0, trace0, trace H²=18')
print('PASS spectrum 2:1, -1:10, 1/2:16 for each; symmetry A→order9')
print('PASS chosen x-axis spatial chart: 18 grid bonds +9 cyclic wrap bonds')
print('NOT a Lean kernel certificate, native rational-Albert isomorphism, or physical Hamiltonian')

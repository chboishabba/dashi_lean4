#!/usr/bin/env python3
"""Source-specific exact homogeneous Albert multiplication of Griess 1990.

R. L. Griess Jr., J. Algebra 131 (1990) 281-293,
DOI 10.1016/0021-8693(90)90176-O.
The complex 27-dimensional Albert algebra admits an A=(Z/3)^3
one-dimensional-character grading. The source's multiplication is
e_x e_y=(-2)^(-c(x,y))*omega^g(x,y)*e_(x+y),
where c=1 for independent x,y, otherwise 0 and omega^2+omega+1=0.

This exhaustive exact check uses Q(omega); it does NOT build the
native compact rational H3(O_Q) basis intertwiner, the different Monster
Griess Vnatural2 product, physical Cube27 locality, or gravity.
"""
from itertools import product,combinations_with_replacement
from fractions import Fraction as Q
from collections import Counter

F=tuple(product(range(3),repeat=3))
ZERO=(Q(0),Q(0));ONE=(Q(1),Q(0));origin=(0,0,0)
omega=((Q(1),Q(0)),(Q(0),Q(1)),(Q(-1),Q(-1)))
def va(x,y):return tuple((a+b)%3 for a,b in zip(x,y))
def plus(x,y):return x[0]+y[0],x[1]+y[1]
def minus(x,y):return x[0]-y[0],x[1]-y[1]
def mul(x,y):
 a,b=x;c,d=y
 return a*c-b*d,a*d+b*c-b*d
def independent(x,y):
 return x!=origin and not any(all((k*a-b)%3==0
                          for a,b in zip(x,y)) for k in range(3))
def g(x,y):
 a,b,c=x;p,q,r=y
 return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
coeff={}
for x in F:
 for y in F:
  factor=Q(-1,2) if independent(x,y) else Q(1)
  coeff[x,y]=tuple(factor*c for c in omega[g(x,y)])
assert len(coeff)==729
assert all(coeff[x,y]==coeff[y,x] for x in F for y in F)
assert all(coeff[origin,x]==ONE for x in F)
assert all(coeff[x,y]!=ZERO for x in F for y in F)

# Frobenius invariance <ex ey,ez>=<ex,ey ez> on all 27^3 triples
# follows from the exact e_origin coefficient of product.
for x in F:
 for y in F:
  for z in F:
   if va(va(x,y),z)==origin:
    assert mul(coeff[x,y],coeff[va(x,y),z])==mul(
      coeff[y,z],coeff[x,va(y,z)])

# FULL polarization of the Jordan polynomial identity:
# ((X^2 Y) X) - (X^2 (Y X))=0 is cubic X, linear Y.
# Test all multisets of 3 basis X-coordinates, and every basis Y.
def difference(a,b,c,y):
 ab=va(a,b)
 l=mul(coeff[ab,y],coeff[va(ab,y),c])
 r=mul(coeff[y,c],coeff[ab,va(y,c)])
 return mul(coeff[a,b],minus(l,r))
checks=0
for triple in combinations_with_replacement(F,3):
 for y in F:
  total=ZERO
  for c in set(triple):
   ab=list(triple);ab.remove(c)
   a,b=ab
   delta=difference(a,b,c,y)
   weight=2 if a!=b else 1
   total=plus(total,(weight*delta[0],weight*delta[1]))
  assert total==ZERO,(triple,y,total)
  checks+=1
assert checks==98658

# The actual source-homogeneous left Jordan operator L_(e_a) shifts
# x->x+a. For each of 26 nonzero a there are exactly nine 3-cycles:
# one cube product +1, eight products -1/8.
for a in F:
 if a==origin:continue
 unseen=set(F);products=[]
 while unseen:
  q=min(unseen);orb=[]
  while q not in orb:
   orb.append(q);unseen.remove(q);q=va(q,a)
  assert len(orb)==3
  p=ONE
  for x in orb:p=mul(p,coeff[a,x])
  products.append(p)
 assert Counter(products)=={ONE:1,(Q(-1,8),Q(0)):8}

a,b,c=(1,0,0),(0,1,0),(2,2,0)
assert mul(coeff[a,b],coeff[va(a,b),c])==(Q(-1,2),Q(0))
u,v=(0,0,1),(0,1,0)
assert mul(coeff[u,u],coeff[va(u,u),v])==(Q(-1,2),Q(0))
assert mul(coeff[u,v],coeff[u,va(u,v)])==(Q(1,4),Q(0))
print("PASS 27 homogeneous characters and all 729 nonzero Griess1990 products")
print("PASS all 19683 Frobenius invariance and 98658 polarized Jordan checks")
print("PASS all nonzero homogeneous multiplication operators: 1 triple-cycle at +1; 8 at -1/8")
print("PASS explicit nonzero cubic and nonassociative witness; not a physical Hamiltonian")

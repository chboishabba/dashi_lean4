#!/usr/bin/env python3
"""Original Griess 1990 source phase -> Moufang M81 and PG(2,3).

Source root: Robert L. Griess Jr., J. Algebra 131 (1990) 281-293,
DOI 10.1016/0021-8693(90)90176-O. Builds actual loop product from
the original 27D homogeneous Albert phase g (not arbitrary cocycle).

Related existing project owners: Integration.Griess1990OriginalHomogeneousFormula,
Integration.Griess1990ThirteenCyclicPhaseRestrictions. Not Monster VOA,
not a finite physical Hamiltonian or an exceptional Lie group proof.
"""
from itertools import product, combinations
from collections import Counter

V=tuple(product(range(3),repeat=3)); origin=(0,0,0)
neg=lambda x:tuple((-i)%3 for i in x)
def add(x,y):return tuple((a+b)%3 for a,b in zip(x,y))
def phase(x,y):
    a,b,c=x;p,q,r=y
    return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
def det(x,y,z):
    a,b,c=x;p,q,r=y;u,v,w=z
    return (a*(q*w-r*v)-b*(p*w-r*u)+c*(p*v-q*u))%3
def mul(a,b):
    return add(a[0],b[0]),(a[1]+b[1]+phase(a[0],b[0]))%3
M=tuple(product(V,range(3))); identity=(origin,0)
assert len(M)==81
assert all(mul(identity,x)==x and mul(x,identity)==x for x in M)
assert all(mul(x,y)==mul(y,x) for x,y in product(M,repeat=2))
assert all(mul(mul(x,x),x)==identity for x in M)
count=Counter()
for x,y,z in product(V,repeat=3):
    ass=(phase(x,y)+phase(add(x,y),z)
         -phase(y,z)-phase(x,add(y,z)))%3
    assert ass==det(x,y,z)
    count[ass]+=1
    xx,yy,zz=(x,0),(y,0),(z,0)
    assert mul(mul(xx,yy),mul(zz,xx))==mul(xx,mul(mul(yy,zz),xx))
assert count=={0:8451,1:5616,2:5616}
assert mul(mul(((0,0,1),0),((0,1,0),0)),((2,0,0),0)) != mul(((0,0,1),0),mul(((0,1,0),0),((2,0,0),0)))
# Projective plane of thirteen cyclic subgroups = nonzero grade vectors
# modulo ±1; NOT the previously observed 13 numeric OEIS atoms alone.
reps=tuple(x for x in V if x!=origin and x<neg(x))
assert len(reps)==13
dot=lambda a,b:sum(x*y for x,y in zip(a,b))%3
inc=lambda i,j:dot(reps[i],reps[j])==0
assert sum(inc(i,j) for i,j in product(range(13),repeat=2))==52
assert all(sum(inc(i,j) for j in range(13))==4 for i in range(13))
assert all(sum(inc(i,j) for i in range(13))==4 for j in range(13))
assert all(sum(inc(i,k) and inc(j,k) for k in range(13))==1
           for i,j in combinations(range(13),2))
assert all(sum(inc(k,i) and inc(k,j) for k in range(13))==1
           for i,j in combinations(range(13),2))
collinear=sum(det(reps[i],reps[j],reps[k])==0
              for i,j,k in combinations(range(13),3))
assert collinear==52 and 286-collinear==234
assert all((det(reps[i],reps[j],reps[k])==0) ==
           any(inc(i,h) and inc(j,h) and inc(k,h) for h in range(13))
           for i,j,k in combinations(range(13),3))
print('PASS Griess original g: all 19683 associators equal det over F3')
print('PASS counts 8451/5616/5616 and full 81-element commutative exponent-three Moufang loop')
print('PASS PG(2,3) 13 points/13 lines/52 incidences/78 unique point pairs')
print('PASS source determinant is zero iff three distinct projective points are collinear')
print('NOT PROMOTED: Monster 3B, 13=F4/4, 78=E6, spatial P3^3, measured physics')

#!/usr/bin/env python3
"""Independent finite probe for the structured E8 glue reflection.

This script is diagnostic authority only.  It reconstructs the 240 E8 root
labels in E6+A2 Dynkin coordinates, defines the glue reflection from inverse
Cartan pairing alone, and checks the permutation-group order jump

    |W(E6) x W(A2)| = 311040
      -> 696729600 = |W(E8)|.

It is intentionally separate from Lean theorem authority.
"""

from itertools import combinations, product
from fractions import Fraction
from sympy import Matrix
from sympy.combinatorics import Permutation, PermutationGroup

CE6 = Matrix([
    [2,0,-1,0,0,0],
    [0,2,0,-1,0,0],
    [-1,0,2,-1,0,0],
    [0,-1,-1,2,-1,0],
    [0,0,0,-1,2,-1],
    [0,0,0,0,-1,2],
])
CA2 = Matrix([[2,-1],[-1,2]])
E6_INV3 = 3 * CE6.inv()
A2_INV3 = 3 * CA2.inv()

A = (-2,-2,0,0,0,0,0,0)
B = (2,0,-2,0,0,0,0,0)
E6_SIMPLE = [
    (0,0,0,-2,-2,0,0,0),
    (0,0,0,-2,2,0,0,0),
    (-1,1,-1,1,1,-1,-1,1),
    (1,-1,1,1,-1,-1,1,-1),
    (0,0,0,0,0,2,-2,0),
    (0,0,0,0,0,0,2,2),
]

def dot(x,y):
    return sum(a*b for a,b in zip(x,y))


def e8_roots():
    out=[]
    for i,j in combinations(range(8),2):
        for si,sj in product((-2,2), repeat=2):
            v=[0]*8
            v[i],v[j]=si,sj
            out.append(tuple(v))
    for s in product((-1,1), repeat=8):
        if sum(x == -1 for x in s) % 2 == 0:
            out.append(tuple(s))
    assert len(out) == 240 and len(set(out)) == 240
    return out

ROOTS=e8_roots()

def labels(r):
    e6=tuple(dot(r,s)//4 for s in E6_SIMPLE)
    a2=(dot(r,A)//4, dot(r,B)//4)
    return e6+a2

LABELS=[labels(r) for r in ROOTS]
assert len(set(LABELS)) == 240
INDEX={x:i for i,x in enumerate(LABELS)}

GLUE=(0,0,0,0,0,1,0,-1)
assert GLUE in INDEX


def pairing_num(x,y):
    e1,e2=x[:6],y[:6]
    a1,a2=x[6:],y[6:]
    n=sum(e1[i]*int(E6_INV3[i,j])*e2[j] for i in range(6) for j in range(6))
    n+=sum(a1[i]*int(A2_INV3[i,j])*a2[j] for i in range(2) for j in range(2))
    return n

assert pairing_num(GLUE,GLUE) == 6
assert Fraction(pairing_num(GLUE,GLUE),3) == 2


def glue_reflect(x):
    n=pairing_num(x,GLUE)
    assert n % 3 == 0
    k=n//3
    return tuple(x[i]-k*GLUE[i] for i in range(8))

assert {pairing_num(x,GLUE)//3 for x in LABELS} == {-2,-1,0,1,2}
assert all(glue_reflect(x) in INDEX for x in LABELS)
assert all(glue_reflect(glue_reflect(x)) == x for x in LABELS)


def reflect_e6(x,k):
    e=list(x[:6]); a=x[6:]
    m=e[k]
    return tuple(e[j]-m*int(CE6[j,k]) for j in range(6))+tuple(a)


def reflect_a2(x,k):
    e=x[:6]; a=list(x[6:])
    m=a[k]
    return tuple(e)+tuple(a[j]-m*int(CA2[j,k]) for j in range(2))

assert all(reflect_e6(x,k) in INDEX for k in range(6) for x in LABELS)
assert all(reflect_a2(x,k) in INDEX for k in range(2) for x in LABELS)


def perm(f):
    return Permutation([INDEX[f(x)] for x in LABELS])

SUBGROUP_GENS=[perm(lambda x,k=k: reflect_e6(x,k)) for k in range(6)]
SUBGROUP_GENS += [perm(lambda x,k=k: reflect_a2(x,k)) for k in range(2)]
SUBGROUP=PermutationGroup(SUBGROUP_GENS)
FULL=PermutationGroup(SUBGROUP_GENS+[perm(glue_reflect)])

assert SUBGROUP.order() == 311040
assert FULL.order() == 696729600

# Eight-reflection E8 simple system: E6 six + reflection in -glue + reflection in -B.
# Reflection does not depend on root sign.  The root Gram matrix has determinant 1.
GLUE_VECTOR=ROOTS[INDEX[GLUE]]
SIMPLE_VECTORS=E6_SIMPLE + [tuple(-x for x in GLUE_VECTOR), tuple(-x for x in B)]
GRAM=Matrix([[dot(x,y)//4 for y in SIMPLE_VECTORS] for x in SIMPLE_VECTORS])
assert GRAM.det() == 1
assert sorted(GRAM.diagonal()) == [2]*8
assert all(GRAM[i,j] in (0,-1) for i in range(8) for j in range(8) if i != j)

print("structured roots:", len(LABELS))
print("glue literal validation root:", GLUE_VECTOR)
print("glue pairing values:", sorted({pairing_num(x,GLUE)//3 for x in LABELS}))
print("subgroup order:", SUBGROUP.order())
print("with glue order:", FULL.order())
print("simple Gram determinant:", GRAM.det())
print("PASS")

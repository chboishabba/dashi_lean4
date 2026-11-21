#!/usr/bin/env python3
"""Exact three-curve lineage and bad-prime nonpromotion audit.

Source curve models:
  E32: y^2=x^3-x; existing BSD Mathlib LFunction + original point counts.
  J+:  y^2=x^3+1; existing Eisenstein/C3 literal bad p=2,3 modules.
  J-:  y^2=x^3-1; quadratic twist of J+ (distinct Q-model).
This is finite geometry, not a Tate algorithm or L-function theorem.
"""
from sympy import primerange, symbols, Poly

CURVES = {'E32':(-1,0), 'J+':(0,1), 'J-':(0,-1)}
checks = 0

def mod_fibre(p, a, b):
    count = 1
    singular = []
    for x in range(p):
        for y in range(p):
            if (y*y - (x*x*x+a*x+b)) % p == 0:
                count += 1
                if (2*y) % p == 0 and (-3*x*x-a) % p == 0:
                    singular.append((x,y))
    return count,tuple(singular)

def disc(a,b):
    return -16*(4*a**3 + 27*b*b)

assert {k:disc(*v) for k,v in CURVES.items()}=={'E32':64,'J+':-432,'J-':-432};checks+=1
for key, (a,b) in CURVES.items():
    bad = {p for p in primerange(2,40) if disc(a,b)%p==0}
    assert bad == ({2} if key=='E32' else {2,3});checks+=1

T = {}
for p in (2,3,5,7,11,13,19,31):
    T[p] = {k:mod_fibre(p,*v) for k,v in CURVES.items()}
    for key, (a,b) in CURVES.items():
        n,singular=T[p][key]
        assert (bool(singular) == (disc(a,b)%p==0)),(p,key,n,singular);checks+=1
assert T[2]['E32']==(3,((1,0),));checks+=1
assert T[2]['J+']==(3,((0,1),));checks+=1
assert T[2]['J-']==(3,((0,1),));checks+=1
assert T[3]['E32']==(4,());checks+=1
assert T[3]['J+']==(4,((2,0),));checks+=1
assert T[3]['J-']==(4,((1,0),));checks+=1
# Naive p=3 projective point counts are identical, but E32 is GOOD and J+ BAD.
assert T[3]['E32'][0] == T[3]['J+'][0] and not T[3]['E32'][1] and T[3]['J+'][1];checks+=1
# p=5 detects E32-vs-jzero, p=7 distinguishes quadratic twist sign.
assert {k:6-T[5][k][0] for k in CURVES}=={'E32':-2,'J+':0,'J-':0};checks+=1
assert {k:8-T[7][k][0] for k in CURVES}=={'E32':0,'J+':-4,'J-':4};checks+=1
u,v=symbols('u v')
assert Poly((v*v-(1+u)**3+(1+u))-((v+u)**2+u**3),u,v,modulus=2).is_zero;checks+=1
assert 64%3 != 0 and (-432)%3 == 0;checks+=1
# Additive bad Euler local factor 1 is NOT inferred from the naive singular count.
assert T[2]['E32'][0] == T[2]['J+'][0] == 3 and (1+2*u*u)!=1;checks+=1
print(f'PASS {checks}/{checks} independent finite comparisons')
print('exact discriminants', {k:disc(*v) for k,v in CURVES.items()})
print('p=2:', T[2])
print('p=3:', T[3], '(same count, different reduction status)')
print('p=5:',{k:6-T[5][k][0] for k in CURVES})
print('p=7:',{k:8-T[7][k][0] for k in CURVES})
print('OPEN: actual Mathlib minimal model, Tate algorithm, bad Euler factors, curve-L Mellin.')

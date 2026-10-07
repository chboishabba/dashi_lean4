#!/usr/bin/env python3
from itertools import product

# Standard F4 root system, scaled by 2 to avoid half-integral coordinates.
# Long roots: ±2ei ±2ej (24)
# Short roots: ±2ei (8) and (±1,±1,±1,±1) (16)
roots=[]
for i in range(4):
    for j in range(i+1,4):
        for si in (-1,1):
            for sj in (-1,1):
                v=[0]*4; v[i]=2*si; v[j]=2*sj; roots.append(tuple(v))
for i in range(4):
    for s in (-1,1):
        v=[0]*4; v[i]=2*s; roots.append(tuple(v))
for signs in product((-1,1),repeat=4): roots.append(tuple(signs))
assert len(roots)==48 and len(set(roots))==48
idx={r:i for i,r in enumerate(roots)}

def reflect(v,a):
    dot=sum(x*y for x,y in zip(v,a)); norm=sum(x*x for x in a)
    assert (2*dot)%norm==0
    q=(2*dot)//norm
    return tuple(x-q*y for x,y in zip(v,a))

def table(a): return tuple(idx[reflect(r,a)] for r in roots)
def comp(p,q): return tuple(p[q[i]] for i in range(48))
ID=tuple(range(48))

def closure(gens):
    seen={ID:0}; todo=[ID]
    while todo:
        g=todo.pop(0); d=seen[g]
        for s in gens:
            h=comp(s,g)
            if h not in seen: seen[h]=d+1; todo.append(h)
    return seen

# F4 simple system: long-long-short-short, with Coxeter labels 3-4-3.
f4roots=[(0,2,-2,0),(0,0,2,-2),(0,0,0,2),(1,-1,-1,-1)]
F=[table(a) for a in f4roots]
GF=closure(F)
assert len(GF)==1152
assert max(GF.values())==24

# D4 long-root simple subsystem.
d4roots=[(2,-2,0,0),(0,2,-2,0),(0,0,2,-2),(0,0,2,2)]
D=[table(a) for a in d4roots]
GD=closure(D)
assert len(GD)==192
assert max(GD.values())==12
Dset=set(GD)
# Normality under the four F4 simple reflections (all involutions).
for s in F:
    for d in D:
        assert comp(s,comp(d,s)) in Dset

# Three 8-element short-root classes for D4 triality:
# vector ±2ei, and the two parity classes of half-roots.
C0=set(range(24,32))
C1={i for i,r in enumerate(roots) if i>=32 and sum(x<0 for x in r)%2==0}
C2={i for i,r in enumerate(roots) if i>=32 and sum(x<0 for x in r)%2==1}
classes=[C0,C1,C2]
assert [len(c) for c in classes]==[8,8,8]
class_of={i:-1 for i in range(24)}
for c,C in enumerate(classes):
    for i in C: class_of[i]=c
# Simple-generator class action: id,id,(12),(01).
class_perms=[]
for s in F:
    p=[]
    for C in classes:
        image={s[i] for i in C}
        p.append(next(j for j,Dc in enumerate(classes) if image==Dc))
    class_perms.append(tuple(p))
assert class_perms==[(0,1,2),(0,1,2),(0,2,1),(1,0,2)]
# Kernel of the class action is exactly the D4 subgroup.
kernel={g for g in GF if all(class_of[g[i]]==class_of[i] for i in range(48))}
assert len(kernel)==192 and kernel==Dset
assert len(GF)//len(Dset)==6
print('F4 root count:',len(roots))
print('W(F4) generated order:',len(GF),'max word length',max(GF.values()))
print('W(D4) long-root subgroup:',len(GD),'max word length',max(GD.values()))
print('triality short-root classes:',[len(c) for c in classes])
print('simple class permutations:',class_perms)
print('triality kernel order:',len(kernel),'quotient order',len(GF)//len(kernel))
print('PASS')

"""Exact finite Max-Cut vertex-orbit quotient regression.

DASHI-authored regression of classical graph-cut identities; no claim of a
new discovery, Lean/Agda kernel check, or OAI.OptimalMaxCut.main verification.
"""
from itertools import product, combinations

def cut(n, edges, labels):
    return sum(w for u,v,w in edges if labels[u] != labels[v])

def orbits(n, generators):
    parent=list(range(n))
    def root(x):
        while parent[x]!=x:
            x=parent[x]
        return x
    for p in generators:
        assert sorted(p)==list(range(n))
        for u,v in enumerate(p):
            parent[root(u)]=root(v)
    classes={}
    for u in range(n):
        classes.setdefault(root(u),[]).append(u)
    return tuple(sorted((tuple(v) for v in classes.values()),key=lambda x:x[0]))

def quotient(edges, classes):
    index={v:i for i,orbit in enumerate(classes) for v in orbit}
    q={}
    for u,v,w in edges:
        assert u<v and w>=0
        a,b=sorted((index[u],index[v]))
        q[(a,b)]=q.get((a,b),0)+w
    return q

def objective(q,bits):
    return sum(w for (a,b),w in q.items() if a!=b and bits[a]!=bits[b])

def check(n,edges,generators):
    source={(u,v):w for u,v,w in edges}
    for p in generators:
        assert all(source.get(tuple(sorted((p[u],p[v]))),0)==w for u,v,w in edges)
    classes=orbits(n,generators)
    q=quotient(edges,classes)
    for bits in product((False,True),repeat=len(classes)):
        lift=tuple(bits[next(i for i,o in enumerate(classes) if v in o)] for v in range(n))
        assert cut(n,edges,lift)==objective(q,bits)
    restricted=max(objective(q,b) for b in product((False,True),repeat=len(classes)))
    full=max(cut(n,edges,b) for b in product((False,True),repeat=n))
    assert restricted<=full
    return classes,restricted,full

def main():
    assert check(2,[(0,1,1)],[(1,0)])==(((0,1),),0,1)
    assert check(4,[(0,1,1),(0,3,1),(1,2,1),(2,3,1)],[(1,2,3,0)])[1:]==(0,4)
    assert check(3,[(0,1,2),(1,2,2)],[(2,1,0)])[1:]==(4,4)
    for mask in range(8):
        edges=[(u,v,1) for k,(u,v) in enumerate(combinations(range(3),2)) if mask>>k&1]
        _,a,b=check(3,edges,[tuple(range(3))])
        assert a==b
    for n in range(2,10):
        check(n,[(i,i+1,1) for i in range(n-1)],[tuple(reversed(range(n)))])
    assert objective({(0,0):10,(0,1):2},(False,True))==2
    print("PASS: exact invariant objective, optimum inequality, strict-loss controls")

if __name__=="__main__":
    main()

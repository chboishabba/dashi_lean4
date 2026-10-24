#!/usr/bin/env python3
"""Griess (1990) A=F3^3 *actual* rational Albert Jordan automorphism cut.

First builds/consumes the existing PR #52 explicit 27D rational isomorphism
by calling its canonical generator; then transports the original 27-character
source action to the literal native Lean RationalAlbert coordinates.
Original author: Robert L. Griess Jr., J. Algebra 131 (1990), 281-293.

This acts on homogeneous *characters*, not the spatial P3^3 nearest-neighbor
graph, the 196884D Monster weight-two algebra, or a physical Hamiltonian.
Exact SymPy is not Lean/Agda kernel verification.
"""
import json,subprocess,sys,tempfile
from itertools import product
from pathlib import Path
import sympy as s
import runpy
here=Path(__file__).resolve().parent

# Reuse the canonical PR generator rather than inventing another octonion
# product or another 27D source model.
with tempfile.TemporaryDirectory() as d:
    cert=Path(d)/"rational_related_triple.json"
    subprocess.run([sys.executable,str(here/
        "check_griess1990_triality_rational_related_triple_recovery.py"),
        "--certificate",str(cert)],check=True,capture_output=True,text=True)
    data=json.loads(cert.read_text())
A=s.Matrix([[s.Rational(t) for t in row]
    for row in data["native_27x27_map"]])
assert A.shape==(27,27) and A.det()!=0
Ai=A.inv()
I=s.eye(27)
P1=s.Matrix([[0,-1],[1,-1]]); P2=P1*P1
assert P1**3==s.eye(2)
source=runpy.run_path(str(here/
    "check_griess1990_albert_peirce_rh_frame.py"))
reps=tuple(x for x in source["X"] if x!=source["z"] and
           x<source["neg"](x))
assert len(reps)==13
def sourceAction(q):
    M=s.eye(27)
    for k,a in enumerate(reps):
        t=sum(q[i]*a[i] for i in range(3))%3
        R=(s.eye(2),P1,P2)[t]
        M[1+2*k:3+2*k,1+2*k:3+2*k]=R
    return M
generators=[sourceAction(tuple(int(i==k) for i in range(3)))
            for k in range(3)]
assert all(G**3==I and G[:,0]==I[:,0] for G in generators)
assert all(g*h==h*g for g,h in product(generators,repeat=2))
for q in product(range(3),repeat=3):
    M=sourceAction(q)
    assert M==generators[0]**q[0]*generators[1]**q[1]*generators[2]**q[2]
    assert s.trace(M)==(27 if q==(0,0,0) else 0)
nativeGenerators=[A*G*Ai for G in generators]
gNative=s.diag(*([1]*3+[2]*24))
assert all(N**3==I and N.T*gNative*N==gNative and
           N*A[:,0]==A[:,0] for N in nativeGenerators)
assert all(g*h==h*g for g,h in product(nativeGenerators,repeat=2))

# Exact original Cayley-Dickson coordinate formula, with Lean's native
# off20 = conjugate(upper02) orientation.
p=runpy.run_path(str(here/
    "check_griess1990_native_albert_rational_peirce_isometry.py"))
om,oc,oa,os=[p[k] for k in ("octmul","octconj","octadd","octscale")]
def native(X,Y):
    a,b,c=X[:3];d,e,f=Y[:3]
    x,y,z=tuple(X[3:11]),tuple(X[11:19]),tuple(X[19:27])
    u,v,w=tuple(Y[3:11]),tuple(Y[11:19]),tuple(Y[19:27])
    inner=lambda v,w:om(v,oc(w))[0]
    def half(*parts):
        t=(s.Rational(0),)*8
        for h in parts:t=oa(t,h)
        return os(s.Rational(1,2),t)
    return s.Matrix((
        a*d+inner(z,w)+inner(y,v),
        b*e+inner(z,w)+inner(x,u),
        c*f+inner(y,v)+inner(x,u),
        *half(om(oc(z),oc(v)),os(b,u),os(f,x),
              om(oc(w),oc(y)),os(e,x),os(c,u)),
        *half(os(d,y),om(oc(x),oc(w)),os(c,v),os(a,v),
              om(oc(u),oc(z)),os(f,y)),
        *half(os(a,w),os(e,z),om(oc(y),oc(u)),os(d,z),
              os(b,w),om(oc(v),oc(x)))))
for r,G in enumerate(nativeGenerators):
    for i,j in product(range(27),repeat=2):
        u,v=A[:,i],A[:,j]
        assert G*native(u,v)==native(G*u,G*v),(r,i,j)
    print("PASS source-selected F3^3 generator",r,
          "729/729 native rational Albert product identities")
print("PASS all 27 A characters: trace identity=27, every other element=0")
print("PASS order-3, commuting generators, unit and trace Gram on SAME native 27D Albert")
print("BOUNDARY: kernel and original-Q F4 classification, Monster and physical consumers unpaid")

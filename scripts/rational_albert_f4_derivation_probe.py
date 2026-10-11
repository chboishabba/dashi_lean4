#!/usr/bin/env python3
"""Exact-rational diagnostic for the native Albert derivation algebra.

Mirrors Integration/RationalAlbertNative.lean.  Diagnostic authority only:
Lean theorem authority is kept separate from the executable rank certificate.

Checks:
* all coordinate left-multiplication commutators are built exactly over Q;
* 324 are nonzero and their matrix span has rank 52;
* 52 exact pivot operators satisfy [D,L_x] = L_{Dx} on all 27 basis vectors;
* the subspace fixing the three diagonal idempotents has dimension 28;
* evaluation on those three idempotents has rank 24;
* that 28-dimensional stabilizer is block diagonal on the three octonion slots;
* each of its three 8-dimensional representation images has rank 28.
"""

from fractions import Fraction as F
import sympy as sp


def qadd(a,b): return tuple(x+y for x,y in zip(a,b))
def qneg(a): return tuple(-x for x in a)
def qconj(a): return (a[0],-a[1],-a[2],-a[3])
def qmul(a,b):
    w,x,y,z=a; W,X,Y,Z=b
    return (w*W-x*X-y*Y-z*Z,
            w*X+x*W+y*Z-z*Y,
            w*Y-x*Z+y*W+z*X,
            w*Z+x*Y-y*X+z*W)

Q0=(F(0),)*4
O0=(Q0,Q0)

def oadd(o,p): return (qadd(o[0],p[0]),qadd(o[1],p[1]))
def oconj(o): return (qconj(o[0]),qneg(o[1]))
def omul(o,p):
    a,b=o; c,d=p
    return (qadd(qmul(a,c),qneg(qmul(qconj(d),b))),
            qadd(qmul(d,a),qmul(b,qconj(c))))
def oscale(s,o): return (tuple(s*x for x in o[0]),tuple(s*x for x in o[1]))
def real(o): return o[0][0]
def inner(o,p): return real(omul(o,oconj(p)))
def osum(*xs):
    out=O0
    for x in xs: out=oadd(out,x)
    return out

HALF=F(1,2)

def jordan(X,Y):
    a,b,c,x,y,z=X; A,B,C,u,v,w=Y
    d0=a*A+inner(z,w)+inner(y,v)
    d1=b*B+inner(z,w)+inner(x,u)
    d2=c*C+inner(y,v)+inner(x,u)
    ox=oscale(HALF,osum(omul(oconj(z),oconj(v)),oscale(b,u),oscale(C,x),
                         omul(oconj(w),oconj(y)),oscale(B,x),oscale(c,u)))
    oy=oscale(HALF,osum(oscale(A,y),omul(oconj(x),oconj(w)),oscale(c,v),
                         oscale(a,v),omul(oconj(u),oconj(z)),oscale(C,y)))
    oz=oscale(HALF,osum(oscale(a,w),oscale(B,z),omul(oconj(y),oconj(u)),
                         oscale(A,z),oscale(b,w),omul(oconj(v),oconj(x))))
    return d0,d1,d2,ox,oy,oz

def vec(X):
    a,b,c,x,y,z=X
    return [a,b,c,*x[0],*x[1],*y[0],*y[1],*z[0],*z[1]]

def unvec(v):
    return (v[0],v[1],v[2],
            (tuple(v[3:7]),tuple(v[7:11])),
            (tuple(v[11:15]),tuple(v[15:19])),
            (tuple(v[19:23]),tuple(v[23:27])))

basis=[]
for i in range(27):
    v=[F(0)]*27; v[i]=F(1); basis.append(unvec(v))

L=[]
for i in range(27):
    cols=[vec(jordan(basis[i],basis[j])) for j in range(27)]
    L.append(sp.Matrix([[sp.Rational(cols[j][r].numerator,cols[j][r].denominator)
                         for j in range(27)] for r in range(27)]))

comm=[]
for i in range(27):
    for j in range(i+1,27):
        D=L[i]*L[j]-L[j]*L[i]
        if D != sp.zeros(27): comm.append(D)
assert len(comm)==324

flat=sp.Matrix.hstack(*[D.reshape(729,1) for D in comm])
assert flat.rank()==52
_,piv=flat.rref()
der=[comm[i] for i in piv]
assert len(der)==52

# Exact derivation identity [D,L_x]=L_{Dx} for every selected basis derivation.
for D in der:
    for j in range(27):
        coeff=D[:,j]
        LD=sp.zeros(27)
        for i,c in enumerate(coeff):
            if c: LD += c*L[i]
        assert D*L[j]-L[j]*D == LD

# Evaluate derivations on the three diagonal idempotents.
ev=sp.Matrix.hstack(*[sp.Matrix.vstack(D[:,0],D[:,1],D[:,2]) for D in der])
assert ev.rank()==24
null=ev.nullspace()
assert len(null)==28

fix=[]
for coeff in null:
    D=sp.zeros(27)
    for i,c in enumerate(coeff):
        if c: D += c*der[i]
    fix.append(D)

blocks=[range(3),range(3,11),range(11,19),range(19,27)]
for D in fix:
    for br,R in enumerate(blocks):
        for bc,C in enumerate(blocks):
            if br!=bc:
                assert all(D[r,c]==0 for r in R for c in C)

for a,b in [(3,11),(11,19),(19,27)]:
    restriction=sp.Matrix.hstack(*[D[a:b,a:b].reshape(64,1) for D in fix])
    assert restriction.rank()==28

print('nonzero_inner_commutators=324')
print('inner_derivation_span_rank=52')
print('selected_derivations_exact_law=52')
print('diagonal_evaluation_rank=24')
print('diagonal_stabilizer_dimension=28')
print('slot0_representation_rank=28')
print('slot1_representation_rank=28')
print('slot2_representation_rank=28')
print('decomposition=52=28+8+8+8 (dimension/action diagnostic)')

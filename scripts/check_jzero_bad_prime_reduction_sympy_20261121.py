#!/usr/bin/env python3
"""Exact SymPy bad-prime minimal-reduction analysis for y²=x³+1.

Independent original Weierstrass model Δ=-432; p-minimal because
v_2(Δ)=4<12 and v_3(Δ)=3<12. Translate singular points to v²=u³,
count smooth rational points on each reduction, infer additive bad
Euler polynomial 1 via standard elliptic reduction classification.
Does NOT calculate wild conductor exponent or prove a global L-series.
"""
from sympy import symbols, Poly, factorint, __version__

x,y,u,v=symbols("x y u v")

def singular_points(p):
    return [(a,b) for a in range(p) for b in range(p)
            if (b*b-a*a*a-1)%p==0 and (2*b)%p==0 and (3*a*a)%p==0]

def affine_points(p):
    return [(a,b) for a in range(p) for b in range(p)
            if (b*b-a*a*a-1)%p==0]

def main():
    assert factorint(432)=={2:4,3:3}
    for p,sing in ((2,(0,1)),(3,(2,0))):
        assert singular_points(p)==[sing]
        smooth=len(affine_points(p))-1+1
        assert smooth==p
        a,b=sing
        eq=(y*y-x*x*x-1).subs({x:u+a,y:v+b}).expand()
        assert all(int(c)%p==0 for _,c in Poly(eq-(v*v-u**3),u,v).terms())
        assert p-smooth==0
        print(f"PASS p={p}: original model p-minimal, cusp at {sing}, #smooth={smooth}, local inverse Euler polynomial=1")
    print("SymPy",__version__)
    print("OPEN conductor exponent wild ramification; external LMFDB identifies conductor 36")

if __name__=="__main__": main()

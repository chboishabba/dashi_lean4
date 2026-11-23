#!/usr/bin/env python3
"""SymPy/integer exact conductor-factor and original bad-model reductions.

For type-one principal ray character, modulus f=2sqrt(-3) must
distinguish all 6 Eisenstein units. Removing either prime-power factor
makes a nontrivial unit congruent 1. Bad p=2,3 singularity checked
literally on y²=x³+1, NOT an asserted Tate-algorithm conductor exponent
or local L factor. Kernel acceptance deferred, no CI.
"""
UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d,a*d+b*c-b*d
def conjugate(z):return z[0]-z[1],-z[1]
def norm(z):return z[0]*z[0]-z[0]*z[1]+z[1]*z[1]
def divisible(z,m):
    n=norm(m);v=mul(z,conjugate(m))
    return all(x%n==0 for x in v)
def unit_kernel(m):
    return [u for u in UNITS if divisible((u[0]-1,u[1]),m)]
def singular_model_points(p):
    return [(x,y) for x in range(p) for y in range(p)
            if (y*y-x*x*x-1)%p==0 and (3*x*x)%p==0 and (2*y)%p==0]
def main():
    two=(2,0);root=(1,2);f=mul(two,root)
    assert f==(2,4) and norm(f)==12
    assert norm(two)==4 and norm(root)==3
    assert unit_kernel(f)==[(1,0)]
    assert set(unit_kernel(two))=={(1,0),(-1,0)}
    assert set(unit_kernel(root))=={(1,0),(0,1),(-1,-1)}
    assert len(unit_kernel((1,0)))==6
    assert singular_model_points(2)==[(0,1)]
    assert singular_model_points(3)==[(2,0)]
    print("PASS f=2sqrt(-3), norm 12 and trivial six-unit ray kernel")
    print("PASS 2 component necessary: -1 ≡ 1 (mod 2)")
    print("PASS sqrt(-3) component necessary: omega ≡ 1 (mod sqrt(-3))")
    print("PASS both bad characteristic models have exact singular reduction")
    print("OPEN Tate/Artin conductor exponents, exceptional Euler factors, global analytic L")
if __name__=="__main__":main()

#!/usr/bin/env python3
"""Exact localized integral-ideal fractions A/B and infinity-type-one ray value.

Imports the same actual HNF-lattice and Euclidean gcd producer from the
integral ideal test. Checks equivalence AD=CB in the IDEAL lattice,
multiplicativity and inverse in exact Q(omega) rational coordinates.
Kernel deferred. Not an analytic L-series or formal infinite ideal theorem.
"""
from fractions import Fraction
from itertools import product
from importlib.util import spec_from_file_location,module_from_spec
from pathlib import Path

filename=Path(__file__).with_name("check_jzero_hecke_ideal_hnf_sympy_20261121.py")
spec=spec_from_file_location("jzero_hnf",filename)
hnf=module_from_spec(spec);spec.loader.exec_module(hnf)

def divide(z,w):
    n=hnf.norm(w)
    assert n>0
    x=hnf.mul(z,hnf.conj(w))
    return (Fraction(x[0],n),Fraction(x[1],n))
def product_ideals(A,B):
    return hnf.lattice(hnf.mul(hnf.ideal_generator(A),hnf.ideal_generator(B)))
def frac_equal(x,y):
    A,B=x;C,D=y
    return product_ideals(A,D)==product_ideals(C,B)
def char(pair):
    A,B=pair
    return divide(hnf.psi(A),hnf.psi(B))
def times(x,y):
    A,B=x;C,D=y
    return product_ideals(A,C),product_ideals(B,D)
def main():
    zs=[(a,b) for a,b in product(range(-4,5),repeat=2) if hnf.coprime((a,b))]
    ideals={tuple(hnf.lattice(z)):hnf.lattice(z) for z in zs}
    H=list(ideals.values())
    assert len(H)==9
    fractions=list(product(H,repeat=2))
    same=0
    for A,B in fractions:
        W=H[3]
        equivalent=(product_ideals(A,W),product_ideals(B,W))
        assert frac_equal((A,B),equivalent)
        assert char((A,B))==char(equivalent)
        assert hnf.mul(char((A,B)),char((B,A)))==(1,0)
        assert char((A,A))==(1,0)
        same+=1
    products=0
    for x,y in product(fractions[::4],repeat=2):
        assert char(times(x,y))==hnf.mul(char(x),char(y))
        products+=1
    one=hnf.lattice((1,0))
    principal=0
    for z in zs:
        if hnf.normalize(z)==z:
            assert char((hnf.lattice(z),one))==z
            principal+=1
    assert (same,products,principal)==(81,441,7)
    print("PASS 9 ideal HNF generators and 81 localized fractions")
    print("PASS 81/81 fraction equivalence, inverse and identity")
    print("PASS 441/441 fractional ideal product character equations")
    print("PASS 7/7 principal ray values: Psi((z))=z (infinity type 1)")
    print("OPEN universal source-typed ideal character, minimal conductor, bad factors, analytic L-series")
if __name__=="__main__":main()

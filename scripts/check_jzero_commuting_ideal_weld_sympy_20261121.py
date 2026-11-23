#!/usr/bin/env python3
"""Weld forward from existing ideal HNF producer and C2/C3 CRT producer.

No duplicate ideal, Euclidean division, generator, ray normalization or units.
Test SAME HNF ideal Psi against commuting sign/cubic normalization.
Local equivalent used the earlier archived HNF owner API; this script
accepts either exported owner naming without changing source semantics.
Exact finite SymPy checks, no kernel/CI.
"""
from itertools import product
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

def load(name,basename):
    spec=spec_from_file_location(name,Path(__file__).with_name(basename))
    obj=module_from_spec(spec);spec.loader.exec_module(obj)
    return obj

ideal=load("ideal","check_jzero_hecke_ideal_hnf_sympy_20261121.py")
crt=load("crt","check_jzero_commuting_square_cube_sympy_20261121.py")

def original_generator(H):
    return (ideal.ideal_generator if hasattr(ideal,"ideal_generator")
            else ideal.generator_from_hnf)(H)

def original_psi(H):
    return (ideal.psi if hasattr(ideal,"psi")
            else ideal.ideal_character)(H)

def ideal_product(H,J):
    # Native original ideal product = HNF of all four basis-vector products.
    columns=[]
    for i,j in product(range(2),repeat=2):
        x=(int(H[0,i]),int(H[1,i]))
        y=(int(J[0,j]),int(J[1,j]))
        columns.append(Matrix(ideal.mul(x,y)))
    return hermite_normal_form(Matrix.hstack(*columns))

def component_normalizer(z):
    u=crt.normalizer(z)
    sign=crt.power(u,3)
    cubic=crt.power(u,4)
    assert crt.mul(sign,cubic)==crt.mul(cubic,sign)==u
    assert crt.mul_res(crt.res(sign),crt.res(z))[2]==1
    assert crt.mul_res(crt.res(cubic),crt.res(z))[:2]==crt.res(crt.ONE)[:2]
    return sign,cubic

def weld(H):
    z=original_generator(H)
    sign,cubic=component_normalizer(z)
    result=ideal.mul(ideal.mul(sign,cubic),z)
    assert result==original_psi(H)
    assert ideal.lattice(result)==H
    return result

def main():
    elements=[(a,b) for a,b in product(range(-6,7),repeat=2)
              if ideal.coprime((a,b))]
    ideals={tuple(ideal.lattice(z)):ideal.lattice(z) for z in elements}
    assert len(elements)==80 and len(ideals)==20
    for z in elements:
        H=ideal.lattice(z)
        assert weld(H)==crt.mul(crt.normalizer(z),z)
        for u in crt.UNIT_CODES:
            uz=ideal.mul(u,z)
            assert weld(H)==crt.mul(crt.normalizer(uz),uz)
    pairs=0
    for H,J in product(ideals.values(),repeat=2):
        HK=ideal_product(H,J)
        assert weld(HK)==ideal.mul(weld(H),weld(J))
        pairs+=1
    print("PASS 80 original-source HNF ideals normalized via commuting C2 x C3")
    print("PASS 480 original-unit associates agree with canonical HNF Psi")
    print(f"PASS {pairs} actual HNF ideal products against commuting Psi weld")
    print("OPEN bad 2/3 factors, global analytic L-series, Lean kernel deferred")

if __name__=="__main__":main()

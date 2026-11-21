#!/usr/bin/env python3
"""LMFDB 36.a4 independent acceptance atop EXISTING PR #114 producers.

This is deliberately only a consumer, not a replacement Jacobi sum,
ray normalizer, elliptic point counter, or Dirichlet-series constructor.
It imports two source-owned PR #114 scripts and checks them against
LMFDB's 36.a4 isogeny-class 20-coefficient anlist.

Sources:
https://www.lmfdb.org/EllipticCurve/Q/36/a/4
https://www.lmfdb.org/EllipticCurve/Q/data/36.a4
Exact SymPy acceptance, Lean kernel and Tate algorithm deferred.
"""
from importlib.util import spec_from_file_location, module_from_spec
from pathlib import Path
from math import gcd
from sympy import __version__ as sympy_version

LIMIT=600
LMFDB_36A4_FIRST20=(1,0,0,0,0,0,-4,0,0,0,0,0,2,0,0,0,0,0,8,0)

def source(filename,name):
    spec=spec_from_file_location(name,Path(__file__).with_name(filename))
    module=module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def main():
    bad=source("check_jzero_bad_prime_reduction_sympy_20261121.py","bad")
    euler=source("check_jzero_hecke_euler_weld_sympy_20261121.py","euler")
    for p,sing in ((2,(0,1)),(3,(2,0))):
        assert bad.singular_points(p)==[sing]
        smooth_affine=len(bad.affine_points(p))-len(bad.singular_points(p))
        assert smooth_affine+1==p
        assert p-(smooth_affine+1)==0
        # Wrong control: counting the singular point gives a_bad = -1.
        assert p-(len(bad.affine_points(p))+1)==-1
        assert euler.elliptic_trace(p)==euler.hecke_trace(p)==0
    elliptic=euler.coefficients(LIMIT,euler.elliptic_trace)
    hecke=euler.coefficients(LIMIT,euler.hecke_trace)
    assert len(elliptic)==LIMIT+1 and elliptic==hecke
    assert tuple(elliptic[1:21])==LMFDB_36A4_FIRST20
    bad_indices=[n for n in range(1,LIMIT+1) if gcd(n,6)>1]
    assert len(bad_indices)==400 and all(elliptic[n]==0 for n in bad_indices)
    print("SymPy",sympy_version)
    print("PASS imported original bad reduction producer: both smooth-locus factors 1")
    print("PASS 2/2 naive singular total-point count negative controls")
    print("PASS imported original Euler producer: 600/600 coefficients")
    print("PASS 400/400 coefficients at indices divisible by 2 or 3 vanish")
    print("PASS 20/20 LMFDB 36.a4 original isogeny-class coefficients")
    print("OPEN external Tate/Kodaira classifications and analytic L-series")

if __name__=="__main__":main()

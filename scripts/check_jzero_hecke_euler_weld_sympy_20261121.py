#!/usr/bin/env python3
"""Same-object CM ray-ideal vs elliptic finite Euler/Dirichlet coefficient weld.

At p=2,3 additive bad Euler polynomial 1: the Hecke ideal character is
ramified and those ideals are EXCLUDED from its Euler product. At good
inert primes ray-normalized (p)=-p yields polynomial 1+p*T².
At good split primes use canonical cubic/quadratic Jacobi Jp and
alpha=-Jp, its conjugate; compare trace with independent Fp point count.

Exact coefficient comparison through n<=600. NOT an analytic equality
or independent Tate wild conductor computation. Lean kernel deferred.
"""
from sympy import primerange, __version__
from math import gcd
from functools import lru_cache

# WELD FORWARD: reuse exact original CRT/Jacobi and ray-normalizer
# producer rather than maintaining a second choice of cubic character.
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec

_ray_source=Path(__file__).with_name("check_jzero_hecke_ray_quotient_sympy_20261121.py")
_ray_spec=spec_from_file_location("jzero_original_ray",_ray_source)
_ray=module_from_spec(_ray_spec)
_ray_spec.loader.exec_module(_ray)

mul=_ray.mul
norm=_ray.norm
chi=_ray.quadratic

def normalize(z):
    return _ray.normalize(z)[0]

@lru_cache(None)
def jacobi(p):
    return _ray.jacobi(p)

@lru_cache(None)
def point_trace(p):
    return -sum(chi(x*x*x+1,p) for x in range(p))

def elliptic_trace(p):
    return 0 if p in (2,3) else point_trace(p)

def hecke_trace(p):
    if p in (2,3):
        return 0
    if p%3==2:
        assert normalize((p,0))==(-p,0)
        return 0
    j=jacobi(p)
    assert norm(j)==p
    alpha=normalize(j)
    assert alpha==(-j[0],-j[1])
    return 2*alpha[0]-alpha[1]

def coefficients(limit,trace):
    a=[0]*(limit+1);a[1]=1
    for n in range(2,limit+1):
        p=next(int(q) for q in primerange(2,n+1) if n%q==0)
        m=n;power=1
        while m%p==0:
            m//=p;power*=p
        if p in (2,3):
            local=0
        else:
            ap=trace(p)
            older=1;recent=ap;local=ap;term=p*p
            while term<=power:
                older,recent=recent,ap*recent-p*older
                local=recent;term*=p
        a[n]=local*a[m]
    return a

def main():
    assert {p:hecke_trace(p) for p in (5,7,11,13,17,19)}=={
        5:0,7:-4,11:0,13:2,17:0,19:8}
    good=0
    for p in primerange(5,601):
        assert hecke_trace(int(p))==elliptic_trace(int(p))
        good+=1
    assert good==107
    limit=600
    left=coefficients(limit,hecke_trace)
    right=coefficients(limit,elliptic_trace)
    assert left==right
    assert all(left[n]==0 for n in range(1,limit+1) if gcd(n,6)>1)
    print("SymPy",__version__)
    print("PASS p2/p3 bad local inverse Euler polynomials = 1, exclude ramified ideals")
    print(f"PASS {good} good rational primes: CM ray local coefficients = same-curve Fp counts")
    print(f"PASS {limit}/{limit} Dirichlet coefficient slots from independent producers")
    print("OPEN full analytic equality, conductor wild exponents, universal GRH")

if __name__=="__main__":main()

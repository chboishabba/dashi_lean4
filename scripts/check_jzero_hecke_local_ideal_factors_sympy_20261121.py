#!/usr/bin/env python3
"""Exact good-prime CM Hecke-shaped local factors for E:y²=x³+1.

Uses SAME ray-one normalizer from companion
check_jzero_hecke_ray_quotient_sympy_20261121.py.
No global ideal Hecke character, all-prime theorem, or kernel acceptance.
"""
import importlib.util
from pathlib import Path
from sympy import primerange

src=Path(__file__).with_name("check_jzero_hecke_ray_quotient_sympy_20261121.py")
spec=importlib.util.spec_from_file_location("crt",src)
crt=importlib.util.module_from_spec(spec);spec.loader.exec_module(crt)

def conjugate(z):
    a,b=z
    return a-b,-b

def trace(z):
    return 2*z[0]-z[1]

def frobenius(p):
    return -sum(crt.quadratic(x*x*x+1,p) for x in range(p))

def main():
    split=inert=0
    for p in primerange(5,2000):
        p=int(p)
        ap=frobenius(p)
        if p%3==1:
            split+=1
            j=crt.jacobi(p)
            alpha,u=crt.normalize(j)
            alphabar,v=crt.normalize(conjugate(j))
            assert u==(-1,0) and v==(-1,0),(p,u,v)
            assert alphabar==conjugate(alpha)
            assert crt.norm(alpha)==p
            assert crt.mul(alpha,alphabar)==(p,0)
            assert crt.ray_one(alpha) and crt.ray_one(alphabar)
            # Two degree-one prime ideals over p give factors
            # (1-alpha*T)(1-conj(alpha)*T).
            assert (1,-trace(alpha),crt.norm(alpha))==(1,-ap,p)
        else:
            inert+=1
            alpha,u=crt.normalize((p,0))
            assert u==(-1,0) and alpha==(-p,0)
            # Single degree-two ideal (p), N(p)=p².
            # 1-Psi((p))*T² = 1+p*T².
            assert ap==0
            assert (1,0,-alpha[0])==(1,-ap,p)
    assert (split,inert)==(148,153)
    print("PASS 148 split primes: conjugate ray-one generators give elliptic factors")
    print("PASS 153 inert primes: normalized -p gives 1+p*T²")
    print("PASS 301 good primes: Hecke-shaped local factors match same curve")
    print("OPEN global ideal-character/analytic L-series, conductor minimality, p2/p3")

if __name__=="__main__":main()

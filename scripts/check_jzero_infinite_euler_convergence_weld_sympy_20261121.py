#!/usr/bin/env python3
"""WELD FORWARD: conditional infinite Euler product from existing #114 owners.

Actual original inputs come from the EXISTING Euler producer and its imported
Eisenstein CRT/Jacobi/ray normalization module. No new character/curve.
For Re(s)=sigma>3/2 and the STANDARD (all-prime) Hasse input,
 |log L_p(s)| <= 4 p^(1/2-sigma), p>3.
Thus the prime logarithm tails beyond P>=5 are bounded by
 4 P^(3/2-sigma)/(sigma-3/2).
If all prime E/Hecke local factors agree, the two Euler products agree
for Re(s)>3/2. Finite tests do NOT prove the all-prime assumption,
analytic continuation, or critical-line RH/GRH. Kernel/CI deferred.
"""
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
from sympy import (symbols,Rational,sqrt,expand,diff,simplify,integrate,oo,
                   log,primerange,__version__)
from fractions import Fraction
from math import gcd

def owner(path,name):
    spec=spec_from_file_location(name,Path(__file__).with_name(path))
    obj=module_from_spec(spec)
    spec.loader.exec_module(obj)
    return obj

def main():
    e=owner("check_jzero_hecke_euler_weld_sympy_20261121.py","euler")
    crt=e._ray
    a,b,T,q=symbols("a b T q",real=True)
    # Complex embedding of a+b omega: trace 2a-b and norm a²-ab+b².
    assert expand(crt.norm((a,b))-(a*a-a*b+b*b))==0
    conj=(a-b,-b)
    product=crt.mul((a,b),conj)
    assert expand(product[0]-(a*a-a*b+b*b))==0 and expand(product[1])==0
    assert (a+conj[0],b+conj[1])==(2*a-b,0)
    # For 0<q<1: -log(1-q) <= q/(1-q), derivative >=0 and value 0 at 0.
    assert simplify(diff(q/(1-q)+log(1-q),q)-q/(1-q)**2)==0
    # For sigma>3/2 and p>=5, q=p^(1/2-sigma)<1/5.
    # Split: two conjugate factors, each <=q/(1-q); inert: q²/(1-q²).
    assert 2/(1-Rational(1,5))==Rational(5,2)<4
    n,P=symbols("n P",positive=True)
    for sigma,expected in [(Rational(2),8/sqrt(P)),
                           (Rational(7,4),16/P**Rational(1,4))]:
        delta=sigma-Rational(1,2)
        integral=4*integrate(n**(-delta),(n,P,oo))
        assert simplify(integral-expected)==0
    primes=[int(p) for p in primerange(5,601)]
    assert len(primes)==107
    for p in primes:
        ap=e.elliptic_trace(p)
        assert ap==e.hecke_trace(p)
        assert ap*ap<=4*p  # bounded test, NOT an all-prime Hasse proof
        if p%3==1:
            j=crt.jacobi(p)
            alpha,u=crt.normalize(j)
            assert u==(-1,0) and crt.norm(alpha)==p
            assert 2*alpha[0]-alpha[1]==ap
        else:
            assert crt.normalize((p,0))==((-p,0),(-1,0)) and ap==0
    for cutoff in (31,97,599):
        elliptic=Fraction(1)
        hecke=Fraction(1)
        for p in primes:
            if p>cutoff:break
            # At s=2: (1-a_p/p²+1/p³)^(-1) = p³/(p³-a_p*p+1)
            elliptic*=Fraction(p**3,p**3-e.elliptic_trace(p)*p+1)
            hecke*=Fraction(p**3,p**3-e.hecke_trace(p)*p+1)
        assert elliptic==hecke
        print("PASS finite Euler product at s=2 through p <=",cutoff,
              "value",round(float(elliptic),10))
    E=e.coefficients(600,e.elliptic_trace)
    H=e.coefficients(600,e.hecke_trace)
    assert E==H and len(E)==601
    assert sum(gcd(n,6)>1 for n in range(1,601))==400
    print("SymPy",__version__)
    print("PASS 107/107 independent elliptic / CM good-prime traces")
    print("PASS 600/600 exact truncated coefficients")
    print("PASS symbolic local factors, log-majorant derivative, exact tail integrals")
    print("CONDITIONAL: all-prime local equality + Hasse imply equality for Re(s)>3/2")
    print("OPEN: all-prime source identification, analytic continuation, RH/GRH")

if __name__=="__main__":main()

#!/usr/bin/env python3
"""Bad prime / 600 coefficient global Euler weld for y²=x³+1 (LMFDB 36.a4).

Original CM input: imported sibling script's Jacobi and ray-normalizer.
Independent elliptic input: count the ORIGINAL cubic's quadratic-character
sum over each good prime. Bad factors: count only smooth points of singular
reduction (including infinity), not the entire singular cubic.

Exact SymPy finite acceptance; NOT a Tate exponent computation, global
analytic continuation, or Lean kernel proof.
Source https://www.lmfdb.org/EllipticCurve/Q/36/a/4
"""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
from sympy import primerange, __version__ as sympy_version

LIMIT=600
LMFDB_FIRST_20=(1,0,0,0,0,0,-4,0,0,0,0,0,2,0,0,0,0,0,8,0)

def original_crt():
    p=Path(__file__).with_name("check_jzero_hecke_ray_quotient_sympy_20261121.py")
    s=spec_from_file_location("original_crt",p)
    m=module_from_spec(s)
    s.loader.exec_module(m)
    return m

def quadratic(t,p):
    t%=p
    return 0 if t==0 else (1 if pow(t,(p-1)//2,p)==1 else -1)

def elliptic_trace(p):
    return -sum(quadratic(x*x*x+1,p) for x in range(p))

def smooth_and_singular(p):
    smooth=[]; singular=[]
    for x in range(p):
        for y in range(p):
            if (y*y-x*x*x-1)%p: continue
            (singular if (2*y)%p==0 and (3*x*x)%p==0
             else smooth).append((x,y))
    return smooth,singular

def hecke_trace(p,crt):
    if p%3==2:
        z,u=crt.normalize((p,0))
        assert (z,u)==((-p,0),(-1,0))
        return 0
    j=crt.jacobi(p)
    a,u=crt.normalize(j)
    conjugate=lambda v:(v[0]-v[1],-v[1])
    b,v=crt.normalize(conjugate(j))
    assert u==v==(-1,0) and b==conjugate(a)
    assert crt.mul(a,b)==(p,0)
    return 2*a[0]-a[1]

def series_coefficients(primes,traces):
    a=[0]*(LIMIT+1);a[1]=1
    for p in primes:
        if p in (2,3):continue  # P_p(T)=1, so every p-power coefficient 0
        first,second=1,traces[p]
        powers=[];q=p
        while q<=LIMIT:
            powers.append((q,second))
            first,second=second,traces[p]*second-p*first
            q*=p
        for n in range(LIMIT,0,-1):
            if not a[n]:continue
            for power,local in powers:
                if n*power>LIMIT:break
                a[n*power]+=a[n]*local
    return a

def main():
    crt=original_crt()
    for p,point,n_affine in ((2,(0,1),1),(3,(2,0),2)):
        smooth,singular=smooth_and_singular(p)
        assert singular==[point] and len(smooth)==n_affine
        assert p-(len(smooth)+1)==0
        assert p-(len(smooth)+len(singular)+1)==-1
    primes=[int(p) for p in primerange(2,LIMIT+1)]
    elliptic={p:elliptic_trace(p) for p in primes if p>3}
    hecke={p:hecke_trace(p,crt) for p in primes if p>3}
    assert elliptic==hecke
    E=series_coefficients(primes,elliptic)
    H=series_coefficients(primes,hecke)
    assert E==H and tuple(E[1:21])==LMFDB_FIRST_20
    bad_slots=[n for n in range(1,LIMIT+1) if n%2==0 or n%3==0]
    assert len(bad_slots)==400 and all(E[n]==0 for n in bad_slots)
    assert len(elliptic)==107
    print("SymPy",sympy_version)
    print("PASS 2/2 bad reductions: smooth counts and negative singular-cubic controls")
    print("PASS 2/2 bad inverse local Euler polynomials P_p(T)=1")
    print("PASS 107/107 independent elliptic and Hecke Jacobi/ray good-prime traces")
    print("PASS 600/600 exact Dirichlet coefficients")
    print("PASS 400/400 indices divisible by 2 or 3 vanish")
    print("PASS 20/20 LMFDB 36.a4 initial Dirichlet coefficients")
    print("EXTERNAL conductor 36=2²·3² and Kodaira IV/III: LMFDB, not a Tate proof")
    print("OPEN global analytic identity and original Lean kernel verification")

if __name__=="__main__":main()

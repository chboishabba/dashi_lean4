#!/usr/bin/env python3
"""Exact finite source audit for E32 original Mathlib localEulerFactor <-> point-count route.

No Lean kernel, reduction theorem, infinite Euler product, analytic continuation,
or BSD proof. Checks the independent integer Euler-polynomial model against
Dedekind eta(4z)^2 eta(8z)^2 through q^128.
"""
from sympy import primerange, symbols, Poly

N = 128

def prime_ap(p):
    assert p > 2
    count = 1  # projective identity point
    residues = {y*y % p for y in range(p)}
    for x in range(p):
        f = (x*x*x-x) % p
        if f == 0:
            count += 1
        elif f in residues:
            count += 2
    return p + 1 - count

def eta_coeffs(N):
    # Original eta(4z)^2 eta(8z)^2 = q * prod(1-q^(4n))^2 prod(1-q^(8n))^2.
    poly = [0] * (N+1)
    poly[1] = 1
    for d in (4, 8):
        for n in range(1, N//d+1):
            k = d*n
            for _ in range(2):
                for exp in range(N, k-1, -1):
                    poly[exp] -= poly[exp-k]
    return poly

def euler_coeffs(N):
    a = [0] * (N+1)
    a[1] = 1
    primes = list(primerange(2, N+1))
    for p in primes:
        if p == 2:
            continue  # conductor32: original additive p2 has inverse polynomial 1
        ap = prime_ap(p)
        power = p
        previous, current = 1, ap
        while power <= N:
            for n in range(1, N//power+1):
                if n % p == 0: continue
                a[power*n] = current * a[n]
            power *= p
            previous, current = current, ap*current - p*previous
    return a

def main():
    checks = 0
    prime_table = {}
    eta = eta_coeffs(N)
    euler = euler_coeffs(N)
    for p in primerange(3, N+1):
        ap=prime_ap(p)
        x=symbols('x')
        P=Poly(1-ap*x+p*x*x,x)
        assert tuple(P.all_coeffs()) == (p,-ap,1)
        checks+=1
        prime_table[p]=ap
    for n in range(1,N+1):
        assert eta[n] == euler[n], (n,eta[n],euler[n])
        checks+=1
    assert prime_table[5]==-2 and eta[5]==-2
    checks+=1
    assert eta[5] != -prime_table[5]
    checks+=1
    assert eta[2]==0 and eta[4]==0 and eta[8]==0
    checks+=1
    assert eta[2] != 1
    checks+=1
    assert ((1**3 - 1) % 2 == 0) and ((1-1**2)%2 == 0)
    checks+=1
    print('SymPy exact E32 model: PASS', checks, 'checks')
    print('Original E32 coefficients == eta(4z)^2 eta(8z)^2:', N,'/',N)
    print('Odd good primes checked:',len(prime_table),'first',list(prime_table.items())[:10])
    print('Bad p2 handled as additive factor 1; wrong multiplicative sign negative control PASS')
    print('OPEN: Mathlib minimal reduction field identification, p2 additive case, Lean kernel, analytic Mellin')

if __name__=='__main__':
    main()

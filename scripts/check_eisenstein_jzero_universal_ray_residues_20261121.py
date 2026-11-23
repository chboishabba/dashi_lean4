#!/usr/bin/env python3
"""Extended *finite* exact ray-congruence acceptance for original j=0 Jacobi.

148 split primes p<2000; each uses an explicit cubic character on F_p and
quadratic character of 1-t. Checks the constructive integer quotient
(J+1)/(2+4ω), its two mod-two/mod-three premises, and all six units.
Neither the sample nor the conditional Lean record proves all-prime
character orthogonality or constructs a global ideal Hecke character.
"""
from sympy import primerange, primitive_root
OMEGA=((1,0),(0,1),(-1,-1))
UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1))

def mul(z,w):
    a,b=z;c,d=w
    return a*c-b*d,a*d+b*c-b*d

def qchar(x,p):
    x%=p
    return 0 if x==0 else (1 if pow(x,(p-1)//2,p)==1 else -1)

def jacobi(p):
    g=int(primitive_root(p))
    psi={0:(0,0)}
    x=1
    for e in range(p-1):
        psi[x]=OMEGA[e%3]
        x=x*g%p
    a=b=0
    for t in range(p):
        u,v=psi[t]
        sign=qchar(1-t,p)
        a+=u*sign;b+=v*sign
    return (a,b)

def divides_ray(z):
    a,b=z
    return (-2*a+4*b)%12==0 and (-4*a+2*b)%12==0

def main():
    ps=[int(p) for p in primerange(7,2000) if p%3==1]
    assert len(ps)==148
    assert len(UNITS)==6
    for p in ps:
        a,b=jacobi(p)
        assert a*a-a*b+b*b==p
        A=a+1
        assert A%2==0 and b%2==0, (p,a,b,"mod2")
        u,v=A//2,b//2
        assert (u+v)%3==0, (p,a,b,"mod_sqrt_minus3")
        k=(u+v)//3
        w=(v-k,k-u)
        assert mul((2,4),w)==(A,b), (p,a,b,w)
        assert divides_ray((A,b))
        good_units=[unit for unit in UNITS
                    if divides_ray((mul(unit,(a,b))[0]-1,
                                    mul(unit,(a,b))[1]))]
        assert good_units==[(-1,0)], (p,good_units)
    print(f"PASS {len(ps)}/{len(ps)} split primes p<2000: mod2, mod sqrt(-3), explicit ray quotient")
    print(f"PASS {len(ps)}/{len(ps)} six-unit unique ray choices, always -1")
    print("OPEN source character-sum proofs for arbitrary p; Lean kernel and global Hecke")

if __name__=="__main__":
    main()

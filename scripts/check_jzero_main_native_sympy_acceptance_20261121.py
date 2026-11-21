#!/usr/bin/env python3
"""Finite exact SymPy acceptance, main-original E:y²=x³+1.

No Lean kernel, no CI. Does not prove all-prime or global Hecke statements.
For all 301 primes 3<p<2000, check actual group addition on (0,1),(-1,0),
six distinct subgroup elements, exact #E divisible 6. At all 148 split
primes also check original cubic/quadratic Jacobi, norm/trace,
unique -1 ray normalization and all 1776 norm-p Eisenstein elements.
"""
from math import isqrt
from sympy import primerange, primitive_root, symbols, expand, __version__
O=None
UNITS=((1,0),(-1,0),(0,1),(0,-1),(-1,-1),(1,1))
OMEGA=((1,0),(0,1),(-1,-1))

def emul(z,w):
    a,b=z;c,d=w
    return a*c-b*d,a*d+b*c-b*d

def norm(z):
    a,b=z;return a*a-a*b+b*b

def primary(z):
    a,b=z;return b%2==0 and (2*a-b-2)%3==0

def ray(z):
    a=z[0]-1;b=z[1]
    return (-2*a+4*b)%12==0 and (-4*a+2*b)%12==0

def chi(x,p):
    x%=p
    return 0 if x==0 else (1 if pow(x,(p-1)//2,p)==1 else -1)

def jacobi(p):
    psi={0:(0,0)};x=1;g=int(primitive_root(p))
    for e in range(p-1):
        psi[x]=OMEGA[e%3];x=x*g%p
    a=b=0
    for t in range(p):
        u,v=psi[t];c=chi(1-t,p);a+=c*u;b+=c*v
    return a,b

def add(P,Q,p):
    if P is None:return Q
    if Q is None:return P
    x,y=P;a,b=Q
    if x==a and (y+b)%p==0:return O
    if x==a:
        m=3*x*x*pow(2*y,-1,p)%p
    else:
        m=(b-y)*pow((a-x)%p,-1,p)%p
    xx=(m*m-x-a)%p
    return xx,(m*(x-xx)-y)%p

def shell(p):
    bound=isqrt(4*p//3)+3
    return ((a,b) for a in range(-bound,bound+1)
            for b in range(-bound,bound+1)
            if norm((a,b))==p)

def main():
    a,b,c,d,u,v,k=symbols('a b c d u v k',integer=True)
    A=a*c-b*d;B=a*d+b*c-b*d
    assert expand(A*A-A*B+B*B-(a*a-a*b+b*b)*(c*c-c*d+d*d))==0
    assert (2*(v-k)-4*(k-u)-2*u).subs(k,(u+v)/3).simplify()==0
    assert (4*(v-k)-2*(k-u)-2*v).subs(k,(u+v)/3).simplify()==0
    primes=list(primerange(5,2000))
    assert len(primes)==301
    splits=elements=0
    for p in primes:
        P=(0,1);Q=(p-1,0)
        assert add(P,P,p)==(0,p-1)
        assert add(add(P,P,p),P,p)==O and add(Q,Q,p)==O
        subgroup={add((O,P,(0,p-1))[i],(O,Q)[j],p)
                  for i in range(3) for j in range(2)}
        assert len(subgroup)==6
        trace=-sum(chi(x*x*x+1,p) for x in range(p))
        count=p+1-trace
        assert count%6==0
        if p%3==2:
            assert trace==0
        else:
            splits+=1;assert trace%6==2
            j=jacobi(p)
            assert norm(j)==p and trace==-(2*j[0]-j[1])
            assert primary((-j[0],-j[1])) and ray((-j[0],-j[1]))
            assert [w for w in UNITS if ray(emul(w,j))]==[(-1,0)]
            for z in shell(p):
                elements+=1
                assert primary(z)==ray(z)
                assert sum(ray(emul(w,z)) for w in UNITS)==1
    assert splits==148 and elements==1776
    print("SymPy",__version__)
    print("PASS symbolic norm multiplicativity and ray quotient")
    print("PASS 301/301 p>3: elliptic subgroup of order six, 6 divides #E")
    print("PASS 148/148 split Jacobi norm/trace and unique ray unit -1")
    print("PASS 1776/1776 norm-p: primary iff ray and unique six-unit normalization")
    print("OPEN universal proof and global Hecke/GRH admission")

if __name__=="__main__":main()

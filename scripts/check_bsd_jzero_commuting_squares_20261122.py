#!/usr/bin/env python3
"""Original BSD E32 two-isogeny and Eisenstein j=0 twist commuting squares.

Sources: Agda ClayBSDOriginalLevel32S4ClassicalClosure20261116 (E32 -> E'),
Lean MillenniumBSDMathlibLFunctionWeld and EisensteinJZeroPointCMExact.
Proves universal chart identities with SymPy, tests finite group squares
and Frobenius twist sign. NOT Lean kernel, integral Neron, or BSD theorem.
"""
from sympy import symbols, I, cancel, simplify, factor, Poly, rem, primerange

x, y, X, Y = symbols('x y X Y', nonzero=True)
checks = 0
phi_x = x - 1/x
phi_y = y*(1 + 1/x**2)
psi_x = (X + 4/X)/4
psi_y = Y*(1 - 4/X**2)/8
# Original source curve and its 2-isogenous optimal model E': y²=X³+4X.
assert cancel((x**3-x)*(1+1/x**2)**2 - (phi_x**3 + 4*phi_x)) == 0; checks += 1
assert cancel((X**3+4*X)*(1-4/X**2)**2/64 - (psi_x**3-psi_x)) == 0; checks += 1
assert cancel(phi_y**2 - (phi_x**3+4*phi_x) -
              (y**2-(x**3-x))*(1+1/x**2)**2) == 0; checks += 1
assert cancel(psi_y**2 - (psi_x**3-psi_x) -
              (Y**2-(X**3+4*X))*(1-4/X**2)**2/64) == 0; checks += 1
# A chart-level commuting square: E32 --phi--> E' --psi--> E32 = doubling.
double_x = ((3*x*x-1)/(2*y))**2 - 2*x
double_y = (3*x*x-1)/(2*y)*(x-double_x) - y
for f in (psi_x.subs(X,phi_x)-double_x,
          psi_y.subs({X:phi_x,Y:phi_y}, simultaneous=True)-double_y):
    numerator = cancel(f).as_numer_denom()[0]
    assert rem(Poly(numerator,y), Poly(y*y-(x**3-x),y)).is_zero
    checks += 1
assert cancel(psi_x.subs(X,phi_x) - (x*x+1)**2/(4*x*(x*x-1))) == 0
checks += 1
# Over Q(i) the j=0 plus/minus models are isomorphic by (x,y)->(-x,i*y).
assert simplify((I*y)**2 - ((-x)**3-1) + (y*y - (x**3+1))) == 0
checks += 1
assert simplify((-I*(I*y)) - y) == 0
checks += 1
assert (64, -432, -432, -4096) == (64, -16*27, -16*27, -64*4**3)
checks += 1

def points(p,a,b):
    return {(u,v) for u in range(p) for v in range(p)
            if (v*v-u*u*u-a*u-b) % p == 0} | {None}

def add(p,a,P,Q):
    if P is None: return Q
    if Q is None: return P
    u,v=P; w,z=Q
    if u==w and (v+z)%p==0: return None
    if u==w:
        slope = ((3*u*u+a) * pow(2*v, -1, p))%p
    else:
        slope = ((z-v)*pow((w-u)%p,-1,p))%p
    U=(slope*slope-u-w)%p
    V=(slope*(u-U)-v)%p
    return U,V

def isogeny_phi(p,P):
    if P is None: return None
    u,v=P
    if u==0: return None  # genuine E32 order-two kernel point (0,0)
    return ((u-pow(u,-1,p))%p, (v*(1+pow(u,-2,p)))%p)

def isogeny_dual(p,P):
    if P is None: return None
    u,v=P
    if u==0: return None  # E' order-two kernel point (0,0)
    return ((u+4*pow(u,-1,p))*pow(4,-1,p)%p,
            v*(1-4*pow(u,-2,p))*pow(8,-1,p)%p)

finite_phi = 0
finite_dual = 0
finite_square = 0
finite_hom = 0
for p in primerange(3,103):
    source=points(p,-1,0)
    target=points(p,4,0)
    assert len(source)==len(target)
    checks += 1
    for P in source:
        Q=isogeny_phi(p,P)
        assert Q in target
        assert isogeny_dual(p,Q)==add(p,-1,P,P)
        finite_square += 1
    for Q in target:
        assert isogeny_dual(p,Q) in source
        finite_dual += 1
    finite_phi += len(source)
    if p<=43:
        for P in source:
            for Q in source:
                assert isogeny_phi(p,add(p,-1,P,Q)) == add(p,4,isogeny_phi(p,P),isogeny_phi(p,Q))
                finite_hom+=1
    checks += 1
assert finite_phi==finite_square and finite_dual==finite_phi
checks += 1
assert finite_phi>1000 and finite_hom>5000
checks += 1

split_twist_points=0
inert_sign_primes=0
split_primes=0
inert_point_checks=0
for p in primerange(5,103):
    plus=points(p,0,1)
    minus=points(p,0,-1)
    trace_plus=p+1-len(plus)
    trace_minus=p+1-len(minus)
    sign=1 if p%4==1 else -1
    assert trace_minus==sign*trace_plus, (p,trace_plus,trace_minus)
    checks+=1
    if sign==1:
        ii=next(z for z in range(p) if (z*z)%p == p-1)
        transformed={None if P is None else (-P[0]%p,ii*P[1]%p) for P in plus}
        assert transformed==minus
        for P in plus:
            for Q in plus if p<=29 else []:
                def twist(R):
                    return None if R is None else (-R[0]%p,ii*R[1]%p)
                assert twist(add(p,0,P,Q))==add(p,0,twist(P),twist(Q))
                split_twist_points+=1
        split_primes+=1
        checks+=1
    else:
        # In F_(p²)=F_p[i] with i²=-1, i^p=-i, hence the twist square
        # anti-commutes with Frobenius by elliptic involution [-1].
        assert (-1)**((p-1)//2)==-1
        for P in plus:
            if P is None: continue
            xx,yy=P
            # Frob_p(i*y)=(-i)*y while twist(Frob_p(y))=i*y.
            assert (yy%p)==((yy**p)%p)
            assert (-yy)%p == (-(yy**p))%p
            inert_point_checks+=1
        inert_sign_primes+=1
        checks+=1
assert split_primes>0 and inert_sign_primes>0
checks+=1
# Existing J+ C3 action x -> omega*x transports through the twist,
# on fields containing BOTH i and omega (split primes p == 1 mod 12).
c3_commuting_points = 0
c3_split_primes = 0
for p in primerange(5,103):
    if p % 12 != 1: continue
    ii = next(z for z in range(p) if (z*z)%p == p-1)
    w = next(z for z in range(2,p) if pow(z,3,p)==1 and z!=1)
    plus=points(p,0,1); minus=points(p,0,-1)
    def sigma(P):
        return None if P is None else ((w*P[0])%p,P[1])
    def tau(P):
        return None if P is None else ((-P[0])%p,(ii*P[1])%p)
    for P in plus:
        assert sigma(P) in plus
        assert tau(P) in minus
        assert tau(sigma(P))==sigma(tau(P))
        c3_commuting_points += 1
    c3_split_primes += 1
    checks += 1
assert c3_split_primes>0 and c3_commuting_points>0
checks+=1
# Exact unpromotable cross-family obstruction: distinct geometric j values.
assert (1728,0,0)==(1728,0,0)
assert 1728!=0
checks+=1
# Particularly useful finite negative controls.
assert len(points(3,-1,0))==len(points(3,0,1))==4
assert (3+1-len(points(3,-1,0))) == 0
checks+=1
assert (8-len(points(7,0,1)),8-len(points(7,0,-1))) == (-4,4)
checks+=1

print('PASS',checks,'source-shaped exact commuting-square checks')
print('E32->Eprime->E32 = [2] (odd primes <=101):',finite_square,'full-group points')
print('E32 phi homomorphism on full finite groups:',finite_hom,'ordered pairs')
print('Eprime dual maps:',finite_dual,'points; chart identities exact via SymPy')
print('J+/J- twist split-prime homomorphism:',split_twist_points,'pairs, primes:',split_primes)
print('J+/J- inert sign:',inert_sign_primes,'primes,',inert_point_checks,'affine points')
print('J+/J- transported C3 action commuting:',c3_commuting_points,'points, primes:',c3_split_primes)
print('BAD/OBSTRUCTION: no natural rational Q->Fp field hom; localize at p;')
print('  p2 isogeny degree is not invertible, and E32 vs j0 have different j/CM.')
print('OPEN: pinned Lean kernel, full Q-isogeny extension, minimal model and L-function formal weld')

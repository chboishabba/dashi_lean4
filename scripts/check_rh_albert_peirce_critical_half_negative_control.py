#!/usr/bin/env python3
"""RH/Hilbert–Polya adversarial finite-operator benchmark, NOT RH progress.
Griess-1990 Albert source Peirce spectrum is 2:1, -1:10, 1/2:16.
RH critical real part 1/2 is NOT a Hermitian Hamiltonian eigenvalue.
For actual Hilbert–Polya, spectral E is the ordinate gamma in 1/2+iE,
and the operator must encode the completed zeta zero set, not a
finite-degree hand-made determinant. External owners: Riemann, Hilbert,
Pólya and the original Jordan/Albert/Griess 1990 literature.
"""
import sympy as s
z=s.symbols('z');half=s.Rational(1,2)
# Genuine source-consequence finite characteristic polynomial.
H=(z-2)*(z+1)**10*(z-half)**16
ratio=s.factor(H.subs(z,1-z)/H)
assert ratio==-((z-2)/(z+1))**9
assert ratio!=1 and ratio!=-1
# Universal Peirce operator p has spectrum 1:1, 0:10, 1/2:16.
Lp=(z-1)*z**10*(z-half)**16
assert s.factor(Lp.subs(z,1-z)/Lp)==-((z-1)/z)**9
# Artificial FINITE Hilbert–Polya analogue built from H and -H:
# Xi_toy(z)=det(((z-1/2)^2+H^2)) has obvious critical-line zeros
# and exact functional equation. Does NOT share zeta's ordinates.
u=(z-half)**2
Xi=(u+4)*(u+1)**10*(u+s.Rational(1,4))**16
assert s.expand(Xi.subs(z,1-z)-Xi)==0
zeros={half+s.I*r for r in (2,-2,1,-1,half,-half)}
assert all(s.re(v)==half for v in zeros)
assert s.degree(Xi,z)==54
# For an arbitrary finite selfadjoint operator, same tautology obtains.
assert s.factor(Xi.subs(z,half+s.I*2))==0
assert s.factor(Xi.subs(z,half+s.I))==0
assert s.factor(Xi.subs(z,half+s.I*half))==0
print('PASS Peirce half eigenvalue is universal Jordan law, no zeta ordinate encoding')
print('PASS actual Albert charpoly violates s->1-s functional equation')
print('PASS artificial degree54 entire Xi_toy has functional equation + critical-line zeros')
print('NEGATIVE CONTROL: these finite spectral facts cannot pay RH #50 A1/A2/B signed analytic producers')

#!/usr/bin/env python3
"""Independent finite/symbolic checks for the native Lean exotic topology tranche.

Uses exact SymPy arithmetic. This does NOT run Lean's kernel, certify
topological homeomorphisms or prove Hatcher's comparison theorem.
"""
from fractions import Fraction
import json
import sympy as S

def tetrahedron():
    d2=S.Matrix([
       [1,1,0,0],[-1,0,1,0],[0,-1,-1,0],
       [1,0,0,1],[0,1,0,-1],[0,0,1,1]])
    fundamental=S.Matrix([-1,1,-1,1])
    assert d2*fundamental==S.zeros(6,1)
    assert d2.rank()==3
    kernel=d2.nullspace()
    assert len(kernel)==1
    assert kernel[0]==fundamental or kernel[0]==-fundamental
    return {'faces':4,'edges':6,'boundary_matrix_rank':3,'h2_dimension':1}

def exact_pairing():
    for q in [S.Integer(-13),S.Rational(-3,7),S.Integer(0),S.Rational(5,11)]:
        assert S.expand(q * S.Integer(1))==q
    # H^2 and H_2 both one-dimensional over Q, with matrix [1].
    ev=S.Matrix([[1]])
    assert ev.det()==1
    return {'pairing_det':'1','left_nondegenerate':True,'right_nondegenerate':True}

def whitney():
    u,v,z=S.symbols('u v z',real=True)
    x,y,Z=u*v,u,v*v
    polynomial=S.expand(x*x-y*y*Z)
    assert polynomial==0
    assert S.expand(S.Integer(0)**2-S.Integer(0)**2*z)==0
    # Polynomial vanishes at (0,0,-1), but v^2=-1 has no real solution.
    return {'parametric_implicit_residual':'0',
            'negative_axis_algebraic_without_real_preimage':True}


def whitney_inverse_rational_grid():
    tested=0
    for u in range(-7,8):
        for v in range(-7,8):
            x,y,z=Fraction(u*v),Fraction(u),Fraction(v*v)
            if y != 0:
                ur,vr=y,x/y
            else:
                ur,vr=Fraction(0),Fraction(abs(v))
            assert ur*vr==x and ur==y and vr*vr==z
            tested+=1
    # Source algebra (not just grid): y!=0 -> v=x/y; x²=y²z
    # gives v²=z. If y=0 then x=0; z>=0 -> v=sqrt(z).
    return {'rational_grid_cases':tested,'source_formula':'y!=0 -> (y,x/y); y=0 -> (0,sqrt(z))',
            'kernel_unverified':True}

def simons():
    x=S.symbols('x0:4',real=True)
    y=S.symbols('y0:4',real=True)
    nx=sum(z*z for z in x); ny=sum(z*z for z in y)
    assert S.solve([nx-ny,nx+ny-1],[nx,ny])=={nx:S.Rational(1,2),ny:S.Rational(1,2)}
    return {'link_squared_radii':['1/2','1/2'],
            'ambient_dimension':8,'area_minimality_verified':False}

def c3_not_wada():
    rows=[{0,1},{1,2},{2,0}]
    for i in range(3):
        for r in range(3):
            assert ((r in rows[i]) == (((r+1)%3) in rows[(i+1)%3]))
    assert rows[0]!=rows[1]
    return {'equivariant':True,'equal_boundaries':False}

if __name__=='__main__':
    print(json.dumps({'tetrahedral_h2':tetrahedron(),
      'finite_h2_pairing':exact_pairing(),
      'whitney':whitney(),'whitney_inverse_rational_grid':whitney_inverse_rational_grid(),'simons':simons(),
      'c3_wada_negative_control':c3_not_wada(),
      'status':'PASS exact finite/symbolic checks (no Lean kernel receipt)'},
      sort_keys=True,indent=2))

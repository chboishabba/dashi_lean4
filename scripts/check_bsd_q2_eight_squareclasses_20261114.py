#!/usr/bin/env python3
"""Exact dyadic eight square-class scan for integer-x points on
ORIGINAL E: y²=x³-x. Nonzero integer n is square in Q₂ iff v₂(n)
even and odd unit part ≡1 mod8. This is an integer slice, never
all Q₂ points/H1/Selmer/Sha. Kernel receipt still required.
"""
from collections import defaultdict
from fractions import Fraction as Q
import json
def cls(n):
    assert n!=0
    v=0
    while n%2==0:n//=2;v+=1
    return (v%2,n%8)
def fact(n):
    if n==0:return 0,0,1
    v=0
    while n%2==0:n//=2;v+=1
    return v,n,n%8
def rational_class(value):
    q=Q(value)
    def split(n):
        v=0
        while n%2==0:
            n//=2
            v+=1
        return v,n
    assert q!=0
    va,ua=split(q.numerator)
    vb,ub=split(q.denominator)
    return ((va-vb)%2,(ua*pow(ub,-1,8))%8)

def original_curve_eight_witnesses():
    # Every f(x)=x^3-x equals scale^2*u with u=1 mod 8, so
    # Hensel produces an actual Q2 point (x,scale*sqrt(u)).
    cases=((28,2,5481),(31,8,465),(33,8,561),
           (39,4,3705),(41,4,4305),(112,4,87801),
           (Q(1,4),Q(1,8),-15),(Q(1,16),Q(1,64),-255))
    witnesses=[]
    for x,scale,u in cases:
        x,scale=Q(x),Q(scale)
        assert x**3-x==scale**2*u and u%8==1
        assert rational_class(x**3-x)==(0,1)
        triple=tuple(rational_class(z) for z in (x-1,x,x+1))
        assert rational_class((x-1)*x*(x+1))==(0,1)
        witnesses.append({'x':str(x),'scale':str(scale),
          'odd_unit':u,'triple':triple})
    assert len({tuple(tuple(z) for z in w['triple']) for w in witnesses})==8
    assert len({tuple(tuple(z) for z in w['triple']) for w in witnesses[:6]})==6
    return witnesses

def check():
    reps={(v,u) for v in (0,1) for u in (1,3,5,7)}
    assert len(reps)==8
    out=defaultdict(list);points=0;B=16384
    for x in range(-B,B+1):
        if x in (-1,0,1):continue
        f=x**3-x;v,u,r=fact(f)
        if v%2!=0 or r!=1:continue
        d=tuple(cls(n) for n in (x-1,x,x+1))
        assert all(a in reps for a in d) and cls(f)==(0,1)
        if len(out[d])<5:out[d].append(x)
        points+=1
    positive={}
    for x in range(2,2000):
        f=x**3-x
        if cls(f)==(0,1):
            d=tuple(cls(n) for n in (x-1,x,x+1))
            positive.setdefault(d,x)
    assert len(out)==len(positive)==6
    assert set(positive.values())=={28,31,33,39,41,112}
    six=[]
    for d,x in sorted(positive.items(),key=lambda z:z[1]):
        f=x**3-x;v,u,_=fact(f)
        assert v%2==0 and u%8==1
        six.append({'x':x,'f':f,'root_power_of_two':v//2,
          'odd_unit_u':u,'u_mod8':u%8,'classes_xminus1_x_xplus1':d})
    witnesses=original_curve_eight_witnesses()
    assert {str(x) for x in positive.values()} == {'28','31','33','39','41','112'}
    return {'schema':'bsd-original-E-q2-eight-distinct-local-Kummer-triples-v2',
      'result':'PASS','q2_nonzero_square_classes':8,
      'integer_x_window':[-B,B],
      'integer_x_q2_point_candidates':points,
      'distinct_triplets_on_integer_slice':len(out),
      'positive_integer_x_six_witnesses':six,
      'eight_distinct_original_curve_rational_x_Hensel_witnesses':witnesses,
      'number_distinct_Q2_Kummer_coordinate_triples':8,
      'standard_Q2_square_criterion_used':True,
      'all_Q2_local_image_exhausted':False,
      'all_eight_H1_classes_implemented':False,
      'actual_Q2_point_and_cohomology_kernel_bridge':False,
      'actual_Kummer_or_Sha2':False,'Lean_kernel_receipt':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))

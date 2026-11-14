#!/usr/bin/env python3
"""Exact dyadic eight square-class scan for integer-x points on
ORIGINAL E: y²=x³-x. Nonzero integer n is square in Q₂ iff v₂(n)
even and odd unit part ≡1 mod8. This is an integer slice, never
all Q₂ points/H1/Selmer/Sha. Kernel receipt still required.
"""
from collections import defaultdict
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
    return {'schema':'bsd-original-E-q2-eight-squareclass-integer-slice-v1',
      'result':'PASS','q2_nonzero_square_classes':8,
      'integer_x_window':[-B,B],
      'integer_x_q2_point_candidates':points,
      'distinct_triplets_on_integer_slice':len(out),
      'positive_integer_x_six_witnesses':six,
      'standard_Q2_square_criterion_used':True,
      'all_Q2_local_image_exhausted':False,
      'all_eight_H1_classes_implemented':False,
      'actual_Kummer_or_Sha2':False,'Lean_kernel_receipt':False}
if __name__=='__main__':print(json.dumps(check(),indent=2))

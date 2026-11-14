#!/usr/bin/env python3
"""Exact integer Hensel lifts for the ORIGINAL BSD K1 dyadic witness 3705.

For every odd a == 1 (mod 8), x_3=1 and
  e_n = ((a - x_n*x_n)//(2**n)) % 2
  x_(n+1) = x_n + e_n*2**(n-1), n>=3
satisfy x_n^2 == a (mod 2**n) and x_(n+1)==x_n (mod 2**(n-1)).
The latter gives a Cauchy sequence in Z_2. Completeness yields x with
x^2=a (the formal Q_2 transfer uses Hensel/completeness in Lean).

Finite modular witnesses are NOT a Lean kernel proof of actual Kummer H1.
"""
import argparse
import json

A=3705

def lift_odd_unit(a,precision):
    assert a%8==1 and precision>=3
    x=1
    rows=[{'n':3,'root':x,'modulus':8}]
    for n in range(3,precision):
        power=1<<n
        assert (a-x*x)%power==0
        eps=((a-x*x)//power)&1
        nxt=x+eps*(power>>1)
        assert (a-nxt*nxt)%(power*2)==0
        assert (nxt-x)%(power>>1)==0
        x=nxt
        if n+1<=16 or n+1 in (32,64,128,256,precision):
            rows.append({'n':n+1,'root':x%(power*2),
                         'modulus':power*2,'bit':eps})
    return x,rows

def check(precision):
    assert A%8==1
    assert 1-A==-8*463 and 463%2==1
    root,rows=lift_odd_unit(A,precision)
    assert (root*root-A)%(1<<precision)==0
    assert root&1
    # For *odd* residues modulo 8, only 1 is a square.
    odd_units=(1,3,5,7)
    assert {x*x%8 for x in odd_units}=={1}
    reps=(1,-1,5,-5,2,-2,10,-10)
    keys=set()
    for representative in reps:
        value=abs(representative)
        parity=0
        while not value&1:
            value//=2
            parity^=1
        residue=((1 if representative>0 else -1)*value)%8
        keys.add((parity,residue))
    assert len(keys)==8
    # Arbitrary example units with each a = 1 (mod 8) have coherent
    # roots by the *same* induction, not a hardcoded 3705 table.
    all_tested=0
    for a in range(1,2049,2):
        if a%8==1:
            r,_=lift_odd_unit(a,32)
            assert (r*r-a)%(1<<32)==0
            all_tested+=1
    return {'schema':'bsd_k1_q2_hensel_3705_exact_v1',
            'result':'PASS','a':A,'a_mod_8':A%8,
            'v2_a_minus_one':3,'precise_hensel_input':'|f(1)|_2=1/8 < |f\'(1)|_2^2=1/4',
            'lift_precision_bits':precision,
            'root_mod_2_power':str(root%(1<<precision)),
            'coherent_lifts':rows,'other_odd_units_tested':all_tested,
            'eight_square_class_representatives':list(reps),
            'math_Q2_square_exists_using_completeness':True,
            'Lean_Q2_sqrt_kernel_checked':False,
            'PadicQuadraticKummerCompatibility_2':False,
            'classical_H1_image_identification':False}

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--precision',type=int,default=128)
    args=parser.parse_args()
    print(json.dumps(check(args.precision),indent=2))

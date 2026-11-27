#!/usr/bin/env python3
"""Conditional Ogg-formula conductor check for exact LMFDB 36.a4 model.

LMFDB source: https://www.lmfdb.org/EllipticCurve/Q/36/a/4
y²=x³+1 is a minimal model, Δ_min=-432, type IV at 2 and III at 3.
The component counts 3 for IV and 2 for III are external Kodaira
classification data. Ogg f_p=v_p(Δ_min)+1-m_p is valid in wild residue
characteristics. This test does NOT derive Kodaira types by Tate.
"""
from sympy import Integer, factorint, __version__

def main():
    delta=Integer(-432)
    valuations=factorint(abs(delta))
    assert valuations=={2:4,3:3}
    reduction={2:("IV",3),3:("III",2)}
    exponents={p:valuations[p]+1-m for p,(_,m) in reduction.items()}
    assert exponents=={2:2,3:2}
    conductor=Integer(1)
    for p,f in exponents.items():conductor*=p**f
    assert conductor==36
    print("SymPy",__version__)
    print("PASS Δ_min=-432=-2^4*3^3")
    print("PASS f_2=4+1-3=2, f_3=3+1-2=2 via Ogg")
    print("PASS N=36=2²·3²")
    print("EXTERNAL input: minimal model, Kodaira IV/III, component counts")
    print("OPEN self-contained Tate classification; analytic L-series and kernel deferred")

if __name__=="__main__":main()

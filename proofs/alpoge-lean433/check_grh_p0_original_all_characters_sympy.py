#!/usr/bin/env python3
"""Local GRH P0 exact audit: source fingerprints and finite Dirichlet arithmetic.

No CI, Lean, Agda, author-proof replay or infinite-analytic claim. This
checks every finite complex Dirichlet character modulo 1..64 by cyclotomic
polynomial arithmetic, plus the five ORIGINAL published source/admission
mappings when --source-root and --adapter are supplied.
"""
import argparse
import hashlib
import itertools
import math
import re
from pathlib import Path
import sympy as S

BLOBS = {"Main.lean": "dbd5db70bc11b35f18fa5751216ab335321e7bfc",
         "Statements.lean": "1cd1bce93344065936b2b392b23306254e0785ef",
         "RHAdmission.lean": "43a3f106e09a013fada4d1868f3bf9b0ba7dbf87"}
OWNERS = (
    ("original_mathlib_rh", "riemannHypothesis", "RiemannHypothesis", "rhOfAll"),
    ("original_riemann_zero_location", "riemannZeta_eq_zero_re", "RiemannZetaZerosOnLine", "rhOfAll"),
    ("original_dirichlet_nonvanishing", "LFunction_ne_zero_of_half_lt_re", "DirichletLNonvanishingRightOfHalf", "allChi"),
    ("original_dirichlet_zeros", "LFunction_eq_zero_re", "DirichletLZerosOnLine", "claimAll.2.1"),
    ("original_primitive_dirichlet_zeros", "LFunction_eq_zero_re_of_isPrimitive", "PrimitiveDirichletLZerosOnLine", "critAll"),
)

def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()

def source_audit(main, statements, adapter):
    assert git_blob(main) == BLOBS["Main.lean"], "original Main blob mismatch"
    assert git_blob(statements) == BLOBS["Statements.lean"], "original Statements blob mismatch"
    assert git_blob(adapter) == BLOBS["RHAdmission.lean"], "original admission adapter blob mismatch"
    main, statements, adapter = [x.decode("utf-8") for x in (main, statements, adapter)]
    assert "import Statements" in main and "import Main" in adapter
    assert statements.count("DirichletCharacter ℂ N") == 3
    assert statements.count("χ.IsPrimitive") == 1
    assert "χ ≠ 1 ∨ s ≠ 1" in statements
    for local, source, target, witness in OWNERS:
        assert re.search(r"\btheorem\s+" + re.escape(source) + r"\s*:\s*" +
                         re.escape(target) + r"\s*:=\s*" + re.escape(witness) +
                         r"(?=\s|$)", main), source
        if target != "RiemannHypothesis":
            assert re.search(r"\bdef\s+" + re.escape(target) +
                             r"\s*:\s*Prop\s*:=", statements), target
        assert re.search(r"\btheorem\s+" + re.escape(local) + r"\s*:\s*" +
                         re.escape(target) + r"\s*:=\s*_root_\." +
                         re.escape(source) + r"(?=\s|$)", adapter), local
        assert re.search(r"#print\s+axioms\s+" + re.escape(local) +
                         r"(?=\s|$)", adapter), local

def negative_sources(main, statements, adapter):
    cases = (
        (main, statements.replace("χ.IsPrimitive".encode(), b"True"), adapter),
        (main.replace(b"claimAll.2.1", b"claimAll.2.2"), statements, adapter),
        (main, statements, adapter.replace(b"_root_.LFunction_ne_zero_of_half_lt_re",
                                           b"_root_.LFunction_eq_zero_re")),
    )
    for mutated in cases:
        assert mutated != (main, statements, adapter), "ineffective mutation"
        try:
            source_audit(*mutated)
        except AssertionError:
            pass
        else:
            raise AssertionError("altered theorem/qualifier/adapter accepted")

def local_characters(p, exponent):
    q = p ** exponent
    if p != 2 or exponent == 2:
        order = int(S.totient(q))
        generator = int(S.primitive_root(q))
        logs = {pow(generator, i, q): i for i in range(order)}
        return q, order, [{x: (k*j) % order for x, j in logs.items()}
                          for k in range(order)]
    if exponent == 1:
        return 2, 1, [{1: 0}]
    # (Z/2^e)^* = <-1> x <5> = C2 x C_(2^(e-2)) for e>=3.
    order = 2 ** (exponent-2)
    logs = {pow(5, j, q): j for j in range(order)}
    chars = []
    for ksign in range(2):
        for kfive in range(order):
            table = {}
            for x in range(1, q, 2):
                sign = int(x % 4 == 3)
                b = logs[(-x) % q if sign else x]
                table[x] = (ksign*sign*(order//2) + kfive*b) % order
            chars.append(table)
    return q, order, chars

def audit_modulus(N, cutoff):
    parts = [local_characters(int(p), int(e)) for p, e in S.factorint(N).items()]
    order = math.lcm(*(part[1] for part in parts)) if parts else 1
    units = [a % N for a in range(1, N+1) if math.gcd(a, N) == 1]
    z = S.Symbol("z")
    cyclotomic = S.Poly(S.cyclotomic_poly(order, z), z, domain=S.QQ)
    totals = [0, 0, 0, 0, 0]  # chars, coefficients, factors, group products, primitive
    for choices in itertools.product(*(part[2] for part in parts)):
        chars = {a: sum((order//part[1])*choice[a % part[0]]
                        for part, choice in zip(parts, choices)) % order
                 for a in units}
        for a in units:
            for b in units:
                assert chars[(a*b) % N] == (chars[a] + chars[b]) % order
                totals[3] += 1
        valid = []
        for d0 in S.divisors(N):
            d = int(d0)
            fibres = {}
            for a in units:
                if a % d in fibres and fibres[a % d] != chars[a]:
                    break
                fibres[a % d] = chars[a]
            else:
                valid.append((d, fibres))
        d, primitive = min(valid, key=lambda pair: pair[0])
        if d == N:
            totals[4] += 1
        # Exact formal Dirichlet convolution, NOT a q-series substitution.
        base = [0] + [z**primitive[n % d] if math.gcd(n, d) == 1 else 0
                      for n in range(1, cutoff+1)]
        product = base
        for p0 in S.factorint(N):
            p = int(p0)
            if d % p == 0:
                continue
            cp = z**primitive[p % d]
            product = [0] + [product[n] - (cp*product[n//p] if n % p == 0 else 0)
                             for n in range(1, cutoff+1)]
            totals[2] += 1
        for n in range(1, cutoff+1):
            actual = z**chars[n % N] if math.gcd(n, N) == 1 else 0
            discrepancy = S.expand(product[n] - actual)
            if discrepancy:
                assert S.rem(S.Poly(discrepancy, z), cyclotomic).is_zero, (N, d, n)
            totals[1] += 1
        totals[0] += 1
    assert totals[0] == int(S.totient(N)), (N, totals[0])
    return totals

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-modulus", type=int, default=64)
    ap.add_argument("--cutoff", type=int, default=180)
    ap.add_argument("--source-root", type=Path)
    ap.add_argument("--adapter", type=Path)
    args = ap.parse_args()
    assert 1 <= args.max_modulus <= 256 and args.cutoff >= 2
    if args.source_root is not None or args.adapter is not None:
        assert args.source_root is not None and args.adapter is not None
        mainfile = (args.source_root / "src/Main.lean").read_bytes()
        statements = (args.source_root / "src/Statements.lean").read_bytes()
        adapter = args.adapter.read_bytes()
        source_audit(mainfile, statements, adapter)
        negative_sources(mainfile, statements, adapter)
        print("PASS pinned source and corrected adapter Git blobs 3/3, direct mappings 5/5, negative controls 3/3")
    else:
        print("Original source fingerprint: SKIPPED (supply --source-root AND --adapter)")
    totals = [0] * 5
    for N in range(1, args.max_modulus+1):
        for i, value in enumerate(audit_modulus(N, args.cutoff)):
            totals[i] += value
    print("PASS all moduli 1..%d: %d/%d characters" %
          (args.max_modulus, totals[0], totals[0]))
    print("PASS exact cyclotomic Dirichlet coefficient comparisons:", totals[1])
    print("PASS omitted Euler factor instances:", totals[2])
    print("PASS exact character multiplication instances:", totals[3])
    print("PASS independently recovered primitive characters:", totals[4])
    print("OPEN: unbounded moduli, infinite analytic L, critical-line zeros, Lean/Agda kernel, GRH")

if __name__ == "__main__":
    main()

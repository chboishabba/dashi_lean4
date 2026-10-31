#!/usr/bin/env python3
"""Check the ACTUAL checkout's original-DAG -> canonical OAI378 frontend.

Run from repository root: python scripts/check_openai378_frontend_exact.py.
Self-contained, stdlib only; no network, no CI, no SAT oracle.
This is not Lean/Agda kernel or a machine step/space proof.
"""
import importlib.util
import itertools
import json
import pathlib
import random

HERE = pathlib.Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "original_dashi_oai378_frontend", HERE / "compile_dashi_circuit_openai378.py")
frontend = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(frontend)
R = random.Random(20261031)


def other_normalize(clauses):
    return sorted(set(tuple(sorted({2 * v + int(p) for v, p in clause}))
                      for clause in clauses))


def read_nat(bits, start):
    i = start
    while i < len(bits) and bits[i]:
        i += 1
    assert i < len(bits)
    return i - start, i + 1


def read_frame(bits, start):
    out = []
    i = start
    while True:
        assert i < len(bits)
        if not bits[i]:
            return out, i + 1
        assert i + 1 < len(bits)
        out.append(bits[i + 1])
        i += 2


def read_list(bits, start, decode):
    out = []
    i = start
    while True:
        assert i < len(bits)
        if not bits[i]:
            return out, i + 1
        inside, i = read_frame(bits, i + 1)
        item, final = decode(inside, 0)
        assert final == len(inside)
        out.append(item)


def decode_cnf(bits):
    variables, i = read_nat(bits, 0)
    clauses, i = read_list(bits, i, lambda payload, at:
                           read_list(payload, at, read_nat))
    assert i == len(bits)
    return variables, clauses


def wire(wire_type, index):
    return {"type": wire_type, "index": index}


def fixture(n, g):
    gates = []
    for j in range(g):
        wires = [wire("input", k) for k in range(n)]
        wires += [wire("gate", k) for k in range(j)]
        op = R.choice(("const", "not", "and", "or")) if wires else "const"
        if op == "const":
            gates.append({"op": op, "value": R.choice((False, True))})
        elif op == "not":
            gates.append({"op": op, "source": R.choice(wires)})
        else:
            gates.append({"op": op, "left": R.choice(wires),
                          "right": R.choice(wires)})
    outputs = [wire("input", k) for k in range(n)]
    outputs += [wire("gate", k) for k in range(g)]
    return {"input_count": n, "gates": gates, "output": R.choice(outputs)}


def independent_circuit(c, bits):
    n = c["input_count"]
    g = []
    def lookup(w):
        return bits[w["index"]] if w["type"] == "input" else g[w["index"]]
    for gate in c["gates"]:
        op = gate["op"]
        if op == "const":
            value = gate["value"]
        elif op == "not":
            value = not lookup(gate["source"])
        elif op == "and":
            value = lookup(gate["left"]) and lookup(gate["right"])
        else:
            value = lookup(gate["left"]) or lookup(gate["right"])
        g.append(value)
    return lookup(c["output"]), tuple(g)


def check_one(c):
    v, source = frontend.compile_original_circuit(c)
    diagnostics = frontend.compile_and_report(c)
    assert diagnostics["num_variables"] == v
    codes = other_normalize(source)
    assert frontend.canonical_clause_codes(source) == codes
    assert diagnostics["normalized_literal_codes"] == [list(c) for c in codes] or (
        diagnostics["normalized_literal_codes"] == codes)
    stream = [x == "1" for x in diagnostics["bits"]]
    assert decode_cnf(stream) == (v, [list(c) for c in codes])
    assert len(stream) == diagnostics["bit_length"]
    assert len(stream) <= diagnostics["formal_target_upper_bound"]
    assert len(stream) <= diagnostics["quadratic_source_variable_upper_bound"]
    counts = diagnostics["normalization_comparisons"]
    assert sum(counts.values()) <= diagnostics["normalization_comparison_budget"]
    accepted = 0
    models = 0
    for input_bits in itertools.product((False, True), repeat=c["input_count"]):
        result, expected_gates = independent_circuit(c, input_bits)
        accepted += int(result)
        for suffix in itertools.product((False, True), repeat=len(c["gates"])):
            valuation = input_bits + suffix
            src = frontend.evaluate_clauses(source, valuation)
            normalized = all(any(valuation[k // 2] == bool(k % 2)
                                 for k in clause) for clause in codes)
            assert src == normalized == (result and suffix == expected_gates)
            models += src
    assert accepted == models
    return 2 ** v


def main():
    cases = checks = 0
    for n in range(4):
        for g in range(6):
            if n + g == 0:
                continue
            for _ in range(35):
                checks += check_one(fixture(n, g))
                cases += 1

    for malformed in (
        {"input_count": 1, "gates": [{"op": "not",
          "source": wire("gate", 0)}], "output": wire("gate", 0)},
        {"input_count": 1, "gates": [], "output": wire("input", 1)},
        {"input_count": -1, "gates": [], "output": wire("input", 0)},
    ):
        try:
            frontend.compile_original_circuit(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid original DAG was accepted")

    report = {
        "status": "PASS",
        "cases": cases,
        "finite_assignments": checks,
        "source_module": "scripts/compile_dashi_circuit_openai378.py",
        "source_status": "actual-checkout Python only; Agda/Lean kernel and TM costs outstanding",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

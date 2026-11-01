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
from io import StringIO

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
    # Independent arithmetic certificate for the *nested framed unary*
    # encoder. This is stronger than an asymptotic bound or a round trip.
    exact_length = v + 2 + sum(
        4 + sum(4 * literal + 8 for literal in clause) for clause in codes)
    assert len(stream) == exact_length
    assert diagnostics["exact_framed_length_certificate"] == exact_length
    assert len(stream) <= diagnostics["sharper_source_clause_upper_bound"]
    # Distinct bounded-prefix emitter shares exactly the OAI encoding.
    for chunk_size in (1, 2, 7, 31):
        sink = StringIO()
        receipt = frontend.stream_original_circuit(c, sink, chunk_size)
        assert sink.getvalue() == diagnostics["bits"]
        assert receipt["bit_length"] == exact_length
        assert receipt["exact_framed_length_certificate"] == exact_length
        assert 0 < receipt["max_buffered_output_bits"] <= chunk_size
    assert len(stream) <= diagnostics["formal_target_upper_bound"]
    assert len(stream) <= diagnostics["quadratic_source_variable_upper_bound"]
    counts = diagnostics["normalization_comparisons"]
    assert sum(counts.values()) <= diagnostics["normalization_comparison_budget"]
    assert diagnostics["normalization_equality_calls"] == sum(counts.values())
    assert diagnostics["normalization_ordering_calls"] <= sum(counts.values())
    assert diagnostics["normalization_total_python_comparison_calls"] == (
        diagnostics["normalization_equality_calls"]
        + diagnostics["normalization_ordering_calls"])
    assert diagnostics["normalization_total_python_comparison_calls"] <= (
        diagnostics["normalization_python_comparison_call_budget"])
    shifts = diagnostics["normalization_list_shifts"]
    assert sum(shifts.values()) <= diagnostics["normalization_shift_budget"]
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


def check_agda_original_newest_first_wire_bridge():
    """Same finite index law as Golden Agda chronologicalGateNumberExact.

    This tests the actual Python conversion, with an independent arithmetic
    oracle for the original Compiler.gateVariableIndex constructor recursion.
    """
    tested = 0
    for n in range(6):
        for earlier in range(9):
            for i in range(n):
                jsonwire = frontend.agda_fin_wire_to_json(
                    "input", i, n, earlier)
                assert jsonwire == wire("input", i)
                assert frontend.json_wire_to_agda_fin(
                    jsonwire, n, earlier) == ("input", i)
                assert frontend.agda_fin_wire_number(
                    "input", i, n, earlier) == i
                tested += 1
            for i in range(earlier):
                jsonwire = frontend.agda_fin_wire_to_json(
                    "gate", i, n, earlier)
                # Original Agda indices are newest-first.
                expected_creation_index = earlier - 1 - i
                original_gate_variable_index = n + expected_creation_index
                assert jsonwire == wire("gate", expected_creation_index)
                assert frontend.json_wire_to_agda_fin(
                    jsonwire, n, earlier) == ("gate", i)
                assert frontend.wire_number(
                    jsonwire, n, earlier) == original_gate_variable_index
                assert frontend.agda_fin_wire_number(
                    "gate", i, n, earlier) == original_gate_variable_index
                tested += 1
    for args in (("gate", 0, 0, 0),
                 ("input", 0, 0, 0),
                 ("gate", -1, 1, 1),
                 ("input", True, 1, 1),
                 ("gate", 1, 1, 1)):
        try:
            frontend.agda_fin_wire_to_json(*args)
        except ValueError:
            pass
        else:
            raise AssertionError("out-of-bounds/non-Fin index was accepted")
    return tested


def main():
    cases = checks = 0
    agda_wire_indices = check_agda_original_newest_first_wire_bridge()
    for n in range(4):
        for g in range(6):
            if n + g == 0:
                continue
            for _ in range(35):
                checks += check_one(fixture(n, g))
                cases += 1

    # M00 executable ingress: canonical serialization and exact parse
    # round-trip, independently of the SAT/counting test below. In particular
    # duplicate names at ANY depth cannot be erased by json.loads.
    for n in range(4):
        for g in range(5):
            if n + g == 0:
                continue
            source_circuit = fixture(n, g)
            canonical = frontend.canonical_original_circuit_json(source_circuit)
            decoded = frontend.parse_original_circuit_json(canonical)
            assert decoded == source_circuit
            assert frontend.canonical_original_circuit_json(decoded) == canonical
            # Alternative legal whitespace and key order describe same DAG.
            assert frontend.parse_original_circuit_json(
                json.dumps(source_circuit, indent=2)) == source_circuit

    # M02 source-size firewall. Without this profile the decimal arity is
    # logarithmic in n, but the OpenAI bitstream contains n unary digits.
    machine_profile_cases = 0
    for n in range(6):
        for g in range(5):
            if n + g == 0:
                continue
            circuit = fixture(n, g)
            machine_input = frontend.canonical_machine_circuit_json(circuit)
            parsed = frontend.parse_machine_circuit_json(machine_input)
            assert parsed == circuit
            assert frontend.canonical_machine_circuit_json(parsed) == machine_input
            assert len(machine_input.encode("utf-8")) >= n + g
            # Quadratic bound is now in the actual serialized input size,
            # not just the mathematical parameter n+g.
            v, clauses = frontend.compile_original_circuit(parsed)
            code_lists = frontend.canonical_clause_codes(clauses)
            encoded_bits = sum(4 + sum(4 * code + 8 for code in row)
                               for row in code_lists) + v + 2
            input_bytes = len(machine_input.encode("utf-8"))
            assert encoded_bits <= 72 * (input_bytes + 1) ** 2

            assert frontend.compile_original_circuit(parsed) == (
                frontend.compile_original_circuit(circuit))
            machine_profile_cases += 1
    compressed = {"input_count": 10000, "gates": [],
                  "output": wire("input", 0)}
    legacy = frontend.canonical_original_circuit_json(compressed)
    assert len(legacy.encode("utf-8")) < compressed["input_count"]
    machine = frontend.canonical_machine_circuit_json(compressed)
    assert len(machine.encode("utf-8")) >= compressed["input_count"]
    assert frontend.parse_machine_circuit_json(machine) == compressed
    assert len(machine.encode("utf-8")) >= 10000
    assert 10000 + 2 <= 72 * (len(machine.encode("utf-8")) + 1) ** 2
    assert "input_unary" not in legacy
    for invalid in (
        '{"input_count":2,"input_unary":"1","gates":[],'
        '"output":{"type":"input","index":0}}',
        '{"input_count":2,"input_unary":"111","gates":[],'
        '"output":{"type":"input","index":0}}',
        '{"input_count":2,"input_unary":"1\\u0030","gates":[],'
        '"output":{"type":"input","index":0}}',
        '{"input_count":2,"input_unary":"11","input_unary":"11",'
        '"gates":[],"output":{"type":"input","index":0}}',
        legacy,
    ):
        try:
            frontend.parse_machine_circuit_json(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("compressed, malformed or ambiguous machine arity accepted")

    ambiguous_json = (
        '{"input_count":1,"input_count":2,"gates":[],'
        '"output":{"type":"input","index":0}}',
        '{"input_count":1,"gates":[],'
        '"output":{"type":"input","type":"gate","index":0}}',
        '{"input_count":1,"gates":[{"op":"const",'
        '"value":true,"value":false}],'
        '"output":{"type":"gate","index":0}}',
        '{"input_count":1,"gates":[],'
        '"output":{"type":"input","index":0,"index":0}}',
        '{"input_count":NaN,"gates":[],'
        '"output":{"type":"input","index":0}}',
        '{"input_count":1,"gates":[],'
        '"output":{"type":"input","index":0},"irrelevant":null}',
    )
    for invalid in ambiguous_json:
        try:
            frontend.parse_original_circuit_json(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid/ambiguous JSON circuit accepted")

    for malformed in (
        {"input_count": 1, "gates": [{"op": "not",
          "source": wire("gate", 0)}], "output": wire("gate", 0)},
        {"input_count": 1, "gates": [], "output": wire("input", 1)},
        {"input_count": -1, "gates": [], "output": wire("input", 0)},
        {"input_count": True, "gates": [], "output": wire("input", 0)},
        {"input_count": 1, "gates": [], "output": wire("input", 0),
         "ignored_semantic_field": False},
        {"input_count": 1, "gates": [], "output":
         {"type": "input", "index": 0, "alias": 1}},
        {"input_count": 1, "gates": [{"op": "const", "value": True,
         "source": wire("gate", 300)}], "output": wire("gate", 0)},
        {"input_count": 1, "gates": [{"op": "not",
         "source": wire("input", 0), "right": wire("input", 0)}],
         "output": wire("gate", 0)},
        {"input_count": 1, "gates": [{"op": "or",
         "left": wire("input", 0), "right": wire("input", 0),
         "unused": 3}], "output": wire("gate", 0)},
        {"input_count": 1, "gates": [{}], "output": wire("input", 0)},
        {"input_count": 1, "gates": "not-a-list",
         "output": wire("input", 0)},
    ):
        try:
            frontend.compile_original_circuit(malformed)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid original DAG was accepted")

    for chunk in (0, -1, True):
        try:
            frontend.stream_original_circuit(
                {"input_count": 1, "gates": [],
                 "output": wire("input", 0)}, StringIO(), chunk)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid chunk size accepted")

    report = {
        "status": "PASS",
        "cases": cases,
        "finite_assignments": checks,
        "original_agda_fin_indices_checked": agda_wire_indices,
        "ambiguous_json_rejections_checked": len(ambiguous_json),
        "canonical_json_roundtrip_cases": 19,
        "unary_arity_machine_profile_cases": machine_profile_cases,
        "decimal_arity_counterexample_checked": True,
        "source_module": "scripts/compile_dashi_circuit_openai378.py",
        "source_status": "actual-checkout Python only; exact framed length and canonical schema tested; Agda/Lean kernel and TM costs outstanding",
    }
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()

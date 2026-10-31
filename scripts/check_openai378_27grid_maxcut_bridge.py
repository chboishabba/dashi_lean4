#!/usr/bin/env python3
"""Source-indexed bridge fixture: original native ternary 27-grid to
the exact *existing* DAG->OAI378 CNF bitstream frontend.

The graph is the 27 vertices and 54 edges of the Golden Agda owners
GraphColouring369PantsGridAdjacencyExact and
GraphColouring369PantsWeightedMaxCutExact.unitNativeGridEdges.
27 3D ternary coordinates with step-1 adjacency, 18 per axis.
This fixture encodes all 54 XOR edge constraints as a shared Boolean DAG,
not the distinct 27-function/11-orbit/7-even+4-odd C3 quotient.
It proves its expected two checkerboard colourings by finite BFS and checks
the compiler for these witnesses and deterministic non-witnesses.
No claim about general Max-Cut hardness, Monster3B representation, or
Agda/Lean-kernel theorem acceptance.
"""
import importlib.util
import itertools
import json
from collections import deque
from pathlib import Path
from random import Random

HERE = Path(__file__).resolve().parent
SPEC = importlib.util.spec_from_file_location(
    "dashi_oai378", HERE / "compile_dashi_circuit_openai378.py")
frontend = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(frontend)

TRITS = range(3)
VERTICES = tuple(itertools.product(TRITS, repeat=3))
POSITION = {v: i for i, v in enumerate(VERTICES)}
EDGES = tuple(
    (POSITION[v], POSITION[tuple(w)])
    for v in VERTICES for axis in range(3)
    if v[axis] < 2
    for w in [list(v[:axis]) + [v[axis] + 1] + list(v[axis + 1:])]
)
assert len(VERTICES) == 27
assert len(EDGES) == 54
assert all(a < b for a, b in EDGES)


def adjacency():
    neighbors = [set() for _ in VERTICES]
    for a, b in EDGES:
        neighbors[a].add(b)
        neighbors[b].add(a)
    return neighbors


def exactly_two_checkerboards():
    neighbors = adjacency()
    colours = [None] * len(VERTICES)
    colours[0] = False
    todo = deque([0])
    while todo:
        i = todo.popleft()
        for j in neighbors[i]:
            expected = not colours[i]
            if colours[j] is None:
                colours[j] = expected
                todo.append(j)
            else:
                assert colours[j] == expected
    assert all(v is not None for v in colours)
    assert all(colours[a] != colours[b] for a, b in EDGES)
    # Connectivity + one fixed seed's forced colours proves two solutions:
    # seed false, or its complement. This is a finite graph argument.
    return tuple(colours), tuple(not v for v in colours)


def wire_input(i):
    return {"type": "input", "index": i}


def wire_gate(i):
    return {"type": "gate", "index": i}


def make_shared_circuit():
    gates = []
    def gate(op, **kwargs):
        gates.append({"op": op, **kwargs})
        return wire_gate(len(gates) - 1)

    # Each original input's complement is computed ONCE, then reused.
    complements = [
        gate("not", source=wire_input(i))
        for i in range(27)
    ]

    cross = []
    for a, b in EDGES:
        left = gate("and", left=wire_input(a), right=complements[b])
        right = gate("and", left=complements[a], right=wire_input(b))
        cross.append(gate("or", left=left, right=right))

    # All native adjacent endpoints must be oppositely coloured.
    accumulated = cross[0]
    for next_edge in cross[1:]:
        accumulated = gate("and", left=accumulated, right=next_edge)

    assert len(gates) == 27 + 3 * 54 + 53
    return {"input_count": 27, "gates": gates, "output": accumulated}


def main():
    witnesses = exactly_two_checkerboards()
    circuit = make_shared_circuit()
    checked = 0
    for v in witnesses:
        accepts, computed_gate_values = frontend.evaluate_circuit(circuit, v)
        assert accepts
        checked += 1
        # Exact canonical extension, not a giant 2^269 enumeration.
        assert frontend.evaluate_clauses(
            frontend.compile_original_circuit(circuit)[1],
            v + computed_gate_values)

    R = Random(20261031)
    nonwitness = 0
    for _ in range(500):
        test = tuple(R.choice((False, True)) for _ in VERTICES)
        accepts, _ = frontend.evaluate_circuit(circuit, test)
        expected = test in witnesses
        assert accepts == expected
        if not expected:
            nonwitness += 1
        checked += 1

    report = frontend.compile_and_report(circuit)
    assert report["input_count"] == 27
    assert report["gate_count"] == 242
    assert report["num_variables"] == 269
    assert report["source_clause_count"] == 700
    assert report["normalized_clause_count"] <= 700
    assert report["bit_length"] <= 72 * 270**2
    assert sum(report["normalization_comparisons"].values()) <= report[
        "normalization_comparison_budget"]
    return {
        "status": "PASS",
        "native_vertices": 27,
        "native_edges": 54,
        "source_owner": "Agda #1438 native GridAdjacency and WeightedMaxCutExact",
        "original_DAG_inputs": 27,
        "original_DAG_gates": report["gate_count"],
        "source_3CNF_clauses": report["source_clause_count"],
        "normalized_upstream_3CNF_clauses": report["normalized_clause_count"],
        "normalized_binary_length_bits": report["bit_length"],
        "normalization_comparisons": report["normalization_comparisons"],
        "expected_source_input_models_by_connected_bipartiteness": 2,
        "input_witnesses_checked": checked,
        "nonwitnesses_checked": nonwitness,
        "boundary": "finite executed fixture, not general MaxCut hardness or kernel",
    }


if __name__ == "__main__":
    print(json.dumps(main(), indent=2))

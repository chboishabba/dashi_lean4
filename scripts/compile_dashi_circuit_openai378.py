#!/usr/bin/env python3
"""Deterministic executable source-DAG -> upstream OAI378 canonical bitstream.

The input is a JSON encoding of the EXISTING DASHI circuit carrier: input
count, gates in *creation order*, and input/gate wire references. Gate refs
are converted to source compiler numbers n + creation_index; each gate may
only read earlier gates. This is a Python executable counterpart of the
existing Agda optional 1/2/3-clause CNF, not a competing formal proof owner.

The bit encoder follows the ACTUAL OpenAI Encoding.lean (2026-10-31 read):
  literalCode = 2 * variable + (1 if positive else 0)
  clauseNumbers = sorted distinct literal codes
  cnfNumbers = sorted distinct clauseNumbers
  encodeNat = unary true^n ++ false
  frame = true,data_bit for each bit then false
  encodeList = true,frame(item) per element, then false
  encodeCNF = encodeNat(numVariables) ++ encodeList(encodeList(encodeNat), cnfNumbers)
No semantic oracle, unbounded-Cook tail, or exponentially large truth table.

Historical credit: Cook/Levin/Tseitin; original DASHI P-vs-NP DAG/compiler
owners; OpenAI's literal and encoding definition. This is EXECUTABLE Python,
not a kernel-accepted Agda/Lean same-object or machine complexity theorem.
"""
import argparse
import json
from pathlib import Path


def wire_number(wire, n, earlier):
    kind = wire["type"]
    index = wire["index"]
    if type(index) is not int or index < 0:
        raise ValueError("wire index must be a nonnegative integer")
    if kind == "input" and index < n:
        return index
    if kind == "gate" and index < earlier:
        return n + index
    raise ValueError("invalid, future, or out-of-range wire reference")


def compile_original_circuit(data):
    n = data["input_count"]
    if type(n) is not int or n < 0:
        raise ValueError("input_count must be a natural number")
    gates = data["gates"]
    if not isinstance(gates, list):
        raise ValueError("gates must be a creation-ordered list")
    clauses = []
    for i, gate in enumerate(gates):
        out = n + i
        op = gate["op"]
        if op == "const":
            value = gate["value"]
            if type(value) is not bool:
                raise ValueError("constant requires Boolean value")
            clauses.append(((out, value),))
        elif op == "not":
            x = wire_number(gate["source"], n, i)
            clauses.extend([((out, False), (x, False)),
                            ((out, True), (x, True))])
        elif op in ("and", "or"):
            x = wire_number(gate["left"], n, i)
            y = wire_number(gate["right"], n, i)
            if op == "and":
                clauses.extend([((out, False), (x, True)),
                                ((out, False), (y, True)),
                                ((out, True), (x, False), (y, False))])
            else:
                clauses.extend([((out, True), (x, False)),
                                ((out, True), (y, False)),
                                ((out, False), (x, True), (y, True))])
        else:
            raise ValueError("unknown gate operation")
    acceptance = wire_number(data["output"], n, len(gates))
    clauses.append(((acceptance, True),))
    return n + len(gates), clauses


def canonical_clause_codes(clauses):
    return sorted(set(tuple(sorted({2 * v + int(sign) for v, sign in clause}))
                      for clause in clauses))


def encode_nat(n):
    if type(n) is not int or n < 0:
        raise ValueError("natural number expected")
    return [True] * n + [False]


def frame(bits):
    result = []
    for bit in bits:
        result.extend([True, bit])
    result.append(False)
    return result


def encode_list(values, encoder):
    result = []
    for value in values:
        result.append(True)
        result.extend(frame(encoder(value)))
    result.append(False)
    return result


def encode_upstream_cnf(num_variables, clauses):
    codes = canonical_clause_codes(clauses)
    bits = encode_nat(num_variables)
    bits.extend(encode_list(codes, lambda clause: encode_list(clause, encode_nat)))
    return codes, bits


def evaluate_clauses(clauses, valuation):
    return all(any(valuation[v] == sign for v, sign in clause)
               for clause in clauses)


def evaluate_circuit(data, inputs):
    if len(inputs) != data["input_count"]:
        raise ValueError("wrong input arity")
    gates = []
    def lookup(w):
        if w["type"] == "input":
            return inputs[w["index"]]
        return gates[w["index"]]
    for gate in data["gates"]:
        op = gate["op"]
        if op == "const":
            value = gate["value"]
        elif op == "not":
            value = not lookup(gate["source"])
        elif op == "and":
            value = lookup(gate["left"]) and lookup(gate["right"])
        elif op == "or":
            value = lookup(gate["left"]) or lookup(gate["right"])
        else:
            raise ValueError(op)
        gates.append(value)
    return lookup(data["output"]), tuple(gates)


def compile_and_report(data):
    nvars, source_clauses = compile_original_circuit(data)
    canonical, bits = encode_upstream_cnf(nvars, source_clauses)
    g = len(data["gates"])
    assert len(source_clauses) <= 3 * g + 1
    assert all(len(c) <= 3 for c in source_clauses)
    assert all(len(c) <= 3 for c in canonical)
    assert all(0 <= literal < 2 * nvars for c in canonical for literal in c)
    upper = nvars + 2 + (24 * nvars + 28) * (3 * g + 1)
    assert len(bits) <= upper
    quadratic_upper = 72 * (nvars + 1) ** 2
    assert len(bits) <= quadratic_upper
    return {
        "input_count": data["input_count"], "gate_count": g,
        "num_variables": nvars, "source_clause_count": len(source_clauses),
        "normalized_clause_count": len(canonical),
        "normalized_literal_codes": canonical,
        "bit_length": len(bits), "formal_target_upper_bound": upper,
        "quadratic_source_variable_upper_bound": quadratic_upper,
        "bits": "".join("1" if b else "0" for b in bits),
        "source_status": "executable Python, not Agda/Lean kernel proof",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("circuit_json", type=Path)
    p.add_argument("--out", type=Path)
    args = p.parse_args()
    result = compile_and_report(json.loads(args.circuit_json.read_text()))
    serial = json.dumps(result, indent=2) + "\n"
    if args.out:
        args.out.write_text(serial)
    else:
        print(serial, end="")


if __name__ == "__main__":
    main()

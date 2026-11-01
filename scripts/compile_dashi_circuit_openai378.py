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


def _require_exact_fields(value, fields, owner):
    """A unique JSON representation for each source constructor.

    Reject silent extension fields: the serializer must not identify two
    distinct JSON objects with one Agda wire/gate/circuit term.
    """
    if not isinstance(value, dict) or set(value) != set(fields):
        raise ValueError(f"{owner} requires exactly {sorted(fields)}")


def wire_number(wire, n, earlier):
    _require_exact_fields(wire, ("type", "index"), "wire")
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
    _require_exact_fields(data, ("input_count", "gates", "output"), "circuit")
    n = data["input_count"]
    if type(n) is not int or n < 0:
        raise ValueError("input_count must be a natural number")
    gates = data["gates"]
    if not isinstance(gates, list):
        raise ValueError("gates must be a creation-ordered list")
    clauses = []
    for i, gate in enumerate(gates):
        out = n + i
        if not isinstance(gate, dict):
            raise ValueError("gate must be an object")
        op = gate.get("op")
        if op == "const":
            _require_exact_fields(gate, ("op", "value"), "constant gate")
            value = gate["value"]
            if type(value) is not bool:
                raise ValueError("constant requires Boolean value")
            clauses.append(((out, value),))
        elif op == "not":
            _require_exact_fields(gate, ("op", "source"), "NOT gate")
            x = wire_number(gate["source"], n, i)
            clauses.extend([((out, False), (x, False)),
                            ((out, True), (x, True))])
        elif op in ("and", "or"):
            _require_exact_fields(gate, ("op", "left", "right"), "binary gate")
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


def _insert_ordered_unique(items, value, counters, counter_name):
    """Explicit linear scan: <=len(items) lexicographic comparisons.

    Each clause has <=3 literals; integer codes are bounded by 2*num_variables.
    This avoids unmodelled Python set hashing and sorting complexity.
    """
    for index, old in enumerate(items):
        counters[counter_name] += 1
        if value == old:
            return
        if value < old:
            items.insert(index, value)
            return
    items.append(value)


def canonical_clause_codes(clauses, counters=None):
    """Exact OAI Finset normalization via explicit bounded insertion scans."""
    if counters is None:
        counters = {"literal_comparisons": 0, "clause_comparisons": 0}
    result = []
    for clause in clauses:
        literal_codes = []
        for v, sign in clause:
            _insert_ordered_unique(
                literal_codes, 2 * v + int(sign),
                counters, "literal_comparisons")
        _insert_ordered_unique(
            result, tuple(literal_codes), counters, "clause_comparisons")
    return result


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


def iter_encode_nat(n):
    """Emit unary n without allocating a unary list of length n."""
    if type(n) is not int or n < 0:
        raise ValueError("natural number expected")
    for _ in range(n):
        yield True
    yield False


def iter_frame(bits):
    for bit in bits:
        yield True
        yield bit
    yield False


def iter_encode_list(values, encoder):
    for value in values:
        yield True
        yield from iter_frame(encoder(value))
    yield False


def iter_canonical_cnf_bits(num_variables, canonical):
    """Same OAI encodeCNF order, with O(1) additional encoder buffers."""
    yield from iter_encode_nat(num_variables)
    yield from iter_encode_list(
        canonical, lambda clause:
        iter_encode_list(clause, iter_encode_nat))


def encode_upstream_cnf(num_variables, clauses, counters=None):
    codes = canonical_clause_codes(clauses, counters)
    # Preserve the previous list API while sharing its actual emitter with
    # the bounded-buffer streaming output path.
    return codes, list(iter_canonical_cnf_bits(num_variables, codes))


def stream_original_circuit(data, sink, chunk_bits=4096):
    """Emit the same canonical bits to a text sink in bounded chunks.

    No bitstream-sized list or string is constructed. The input JSON,
    compiled source clauses, normalized clauses and a <=chunk_bits output
    buffer remain live. This is a Python logical-buffer certificate, NOT a
    primitive-TM visited-space or elapsed-step proof.
    """
    if type(chunk_bits) is not int or chunk_bits <= 0:
        raise ValueError("chunk_bits must be positive")
    num_variables, clauses = compile_original_circuit(data)
    canonical = canonical_clause_codes(clauses)
    exact = num_variables + 2 + sum(
        4 + sum(4 * code + 8 for code in clause) for clause in canonical)
    pending = []
    count = 0
    max_pending = 0
    for bit in iter_canonical_cnf_bits(num_variables, canonical):
        pending.append("1" if bit else "0")
        count += 1
        max_pending = max(max_pending, len(pending))
        if len(pending) == chunk_bits:
            sink.write("".join(pending))
            pending.clear()
    if pending:
        sink.write("".join(pending))
    assert count == exact
    return {
        "num_variables": num_variables,
        "gate_count": len(data["gates"]),
        "source_clause_count": len(clauses),
        "normalized_clause_count": len(canonical),
        "bit_length": count,
        "exact_framed_length_certificate": exact,
        "max_buffered_output_bits": max_pending,
        "configured_output_chunk_bits": chunk_bits,
        "source_status": "executed Python streaming emitter; TM proof pending",
    }


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
    comparisons = {"literal_comparisons": 0, "clause_comparisons": 0}
    canonical, bits = encode_upstream_cnf(nvars, source_clauses, comparisons)
    g = len(data["gates"])
    assert len(source_clauses) <= 3 * g + 1
    assert all(len(c) <= 3 for c in source_clauses)
    assert all(len(c) <= 3 for c in canonical)
    assert all(0 <= literal < 2 * nvars for c in canonical for literal in c)
    # Exact closed form for *actual OAI* unary/framed nested-list encoding.
    # Outer formula: v+2 + sum over canonical clauses of
    # (4 + sum over literal codes of (4*code+8)).
    exact_bit_length = nvars + 2 + sum(
        4 + sum(4 * code + 8 for code in clause) for clause in canonical)
    assert len(bits) == exact_bit_length
    # Every code is < 2*v, and each canonical clause has <=3 literals.
    # This strengthens (but does not replace) the upstream width-3 bound.
    sharper_upper = nvars + 2 + (24 * nvars + 16) * (3 * g + 1)
    assert len(bits) <= sharper_upper
    upper = nvars + 2 + (24 * nvars + 28) * (3 * g + 1)
    assert len(bits) <= upper
    quadratic_upper = 72 * (nvars + 1) ** 2
    assert len(bits) <= quadratic_upper
    m = len(source_clauses)
    # Each source clause has <=3 literal inserts (each scan <=2 comparisons);
    # each source clause insert scans at most all previously seen clauses.
    comparison_budget = 6 * m + m * (m - 1) // 2
    assert sum(comparisons.values()) <= comparison_budget
    return {
        "input_count": data["input_count"], "gate_count": g,
        "num_variables": nvars, "source_clause_count": len(source_clauses),
        "normalized_clause_count": len(canonical),
        "normalized_literal_codes": canonical,
        "bit_length": len(bits),
        "exact_framed_length_certificate": exact_bit_length,
        "sharper_source_clause_upper_bound": sharper_upper,
        "formal_target_upper_bound": upper,
        "quadratic_source_variable_upper_bound": quadratic_upper,
        "normalization_comparisons": comparisons,
        "normalization_comparison_budget": comparison_budget,
        "bits": "".join("1" if b else "0" for b in bits),
        "source_status": "executable Python, not Agda/Lean kernel proof",
    }


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("circuit_json", type=Path)
    p.add_argument("--out", type=Path)
    p.add_argument("--stream-bits-out", type=Path,
                   help="write canonical bits separately using bounded chunks; "
                        "omit the giant bit string from the JSON receipt")
    p.add_argument("--chunk-bits", type=int, default=4096)
    args = p.parse_args()
    source = json.loads(args.circuit_json.read_text())
    if args.stream_bits_out is None:
        result = compile_and_report(source)
    else:
        with args.stream_bits_out.open("w") as sink:
            result = stream_original_circuit(source, sink, args.chunk_bits)
    serial = json.dumps(result, indent=2) + "\n"
    if args.out:
        args.out.write_text(serial)
    else:
        print(serial, end="")


if __name__ == "__main__":
    main()

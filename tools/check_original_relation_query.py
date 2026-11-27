#!/usr/bin/env python3
"""Independent replay of the native original relation-query inverse.

This is an acceptance comparator, not a production parser or semantic owner.
Canonical typed digest is the original ITIR contract, not JSON text hashing.
"""
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path


def typed_digest(value):
    h = hashlib.sha256()
    def count(n):
        h.update(n.to_bytes(8, "big"))
    def string(s):
        raw = s.encode()
        h.update(b"S")
        count(len(raw))
        h.update(raw)
    def encode(v):
        if v is None:
            h.update(b"N")
        elif type(v) is bool:
            h.update(b"B1" if v else b"B0")
        elif type(v) is int:
            if not -(1 << 63) <= v < 1 << 64:
                raise ValueError("outside typed integer carrier")
            h.update(b"I-" if v < 0 else b"I+")
            raw = abs(v).to_bytes(max(1, (abs(v).bit_length() + 7) // 8), "big")
            count(len(raw))
            h.update(raw)
        elif isinstance(v, str):
            string(v)
        elif isinstance(v, list):
            h.update(b"Q")
            count(len(v))
            for item in v:
                encode(item)
        elif isinstance(v, dict):
            h.update(b"M")
            count(len(v))
            for key in sorted(v):
                string(key)
                encode(v[key])
        else:
            raise ValueError("noncanonical value")
    h.update(b"ITIR")
    contract = b"itir.typed-canonical.v1"
    count(len(contract))
    h.update(contract)
    encode(value)
    return h.hexdigest()


def check(native, answer):
    def require(value, message):
        if not value:
            raise ValueError(message)
    require(native["schema"] == "slr-reopened-original-relation-packet-v1", "wrong source ABI")
    require(answer["schema"] == "slr.original-relation-query.v1", "wrong answer ABI")
    for key in ("numeric_run_ref", "document_ref", "snapshot_ref", "packet_sha256"):
        require(native[key] == answer[key], "wrong " + key)
    packet = native["packet"]
    require(typed_digest(packet) == native["packet_sha256"], "source packet digest")
    c = packet["comparison"]
    for key in ("source_sha256", "source_revision_ref", "parser_run_ref", "scope", "prefix_end_char"):
        require(c[key] == answer[key], "source coordinate " + key)
    for key in ("missing_original_tags", "prefix_uncovered_nonwhitespace"):
        require(packet[key] == answer[key], "source debt " + key)
    relations = c["bundle"]["relations"]
    atoms = {a["id"]: a for a in c["bundle"]["atoms"]}
    inverse = packet["atom_token_inverse"]
    require(len(atoms) == len(c["bundle"]["atoms"]) == len(inverse)
            and atoms.keys() == inverse.keys(), "atom inverse")
    factors = defaultdict(list)
    owners = {}
    for f in c["reduction_projection"]["factors"]:
        owner = f["metadata"]["relation_ref"]
        require(f["factor_ref"] not in owners, "duplicate factor")
        owners[f["factor_ref"]] = owner
        factors[owner].append(f)
    constraints = defaultdict(list)
    for q in c["reduction_projection"]["constraints"]:
        for owner in {owners[f] for key in ("source_factor_refs", "target_factor_refs") for f in q[key]}:
            constraints[owner].append(q)
    expected = []
    original_refs = set()
    kind = answer["query_relation_type"]
    for relation in relations:
        ref = "semantic-relation:" + typed_digest({"document_ref": native["document_ref"], "relation": relation})
        require(ref not in original_refs and ref in factors, "relation factor inverse")
        original_refs.add(ref)
        if kind != "all" and relation["type"] != kind:
            continue
        roles = [{"ordinal": n, "original_role": role,
                  "original_atom": atoms[role["atom"]] if "atom" in role else None,
                  "numeric_token_id": inverse[role["atom"]] if "atom" in role else None}
                 for n, role in enumerate(relation["roles"])]
        expected.append({"relation_ref": ref, "original_relation": relation,
            "role_inverse": roles, "original_factors": factors[ref],
            "original_constraints": constraints[ref],
            "recorded_residuals": sorted({r for f in factors[ref] for r in f["residuals"]}),
            "semantic_coverage_paid": False})
    require(original_refs == factors.keys(), "orphan factor")
    require(answer["relation_type_inventory"] == dict(Counter(r["type"] for r in relations)), "type inventory")
    require(answer["recorded_relation_count"] == len(relations), "recorded count")
    require(answer["answer_count"] == len(expected) and answer["answers"] == expected, "answer inverse")
    for key in ("all_live_semantic_readings_covered", "governed_identity_paid", "level_three_paid", "world_truth_paid"):
        require(answer[key] is False, "promotion " + key)
    require(answer["complete_recorded_query"] is True and answer["outside_model_possible"] is True, "scope")
    return {"schema": "itir.original-relation-query-reference.v1", "original_packet_sha256": native["packet_sha256"],
            "recorded_relation_count": len(relations), "query_relation_type": kind, "answer_count": len(expected),
            "exact_original_role_factor_constraint_inverse": True, "semantic_coverage_paid": False}


def main():
    native, answer = (json.loads(Path(p).read_text()) for p in sys.argv[1:3])
    result = check(native, answer)
    # Actual original source mutation controls, not fabricated positives.
    from copy import deepcopy
    if answer["answers"]:
        bad = deepcopy(answer)
        bad["answers"].pop()
        try:
            check(native, bad)
        except ValueError:
            pass
        else:
            raise ValueError("missing row accepted")
    bad = deepcopy(answer)
    bad["governed_identity_paid"] = True
    try:
        check(native, bad)
    except ValueError:
        pass
    else:
        raise ValueError("forged admission accepted")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()

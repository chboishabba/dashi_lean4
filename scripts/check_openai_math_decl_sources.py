#!/usr/bin/env python3
"""Audit exact upstream declaration locations for the 208 main-result rows.

The catalogue may name a newer upstream revision than the pinned submodule.
Source-name presence is a discovery/integrity check, NOT a kernel certificate
or type-preserving imported proof. This script fails closed on source drift.
Historical credit: original upstream openai/math formalization authors.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

from build_openai_math_same_object_matrix import catalog


# A source-level hint that the symbol occurs at a Lean declaration header.
# Not namespace resolution, typechecking, proof checking or axiom closure.
LEAN_HEAD = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|opaque)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|structure|class|instance)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)\b"
)


def declaration_header_lines(source_text, name):
    result = []
    for i, line in enumerate(source_text.splitlines(), start=1):
        hit = LEAN_HEAD.search(line)
        if hit and hit.group(1).split(".")[-1] == name:
            result.append(i)
    return result


def inspect(catalogue, upstream_root):
    results = []
    for i, (comparator, declaration, source_path) in enumerate(
            catalog(catalogue), start=1):
        path = upstream_root / "lean" / source_path
        name = declaration.split(".")[-1]
        digest = None
        line_numbers = []
        header_lines = []
        if not path.is_file():
            status = "SOURCE_FILE_MISSING"
        else:
            raw = path.read_bytes()
            digest = hashlib.sha256(raw).hexdigest()
            source_text = raw.decode("utf-8", errors="replace")
            # A textual identifier might occur in a comment or a reference.
            # Never promote a lexical hit to a theorem or verified type.
            matcher = re.compile(
                r"(?<![A-Za-z0-9_'])" + re.escape(name)
                + r"(?![A-Za-z0-9_'])")
            line_numbers = [
                i for i, line in enumerate(source_text.splitlines(), start=1)
                if matcher.search(line)
            ]
            header_lines = declaration_header_lines(source_text, name)
            status = ("IDENTIFIER_TEXT_FOUND_UNVERIFIED" if line_numbers
                      else "DECLARATION_IDENTIFIER_NOT_FOUND")
        results.append({
            "index": i, "comparator": comparator,
            "declaration": declaration, "source_file": source_path,
            "source_file_present": path.is_file(),
            "source_content_sha256": digest,
            "identifier_text_line_numbers": line_numbers,
            "declaration_header_line_numbers": header_lines,
            "declaration_header_status": (
                "LEXICAL_HEADER_UNVERIFIED" if header_lines
                else "NOT_IDENTIFIED_BY_HEADER_SCAN"),
            "source_text_status": status,
            "source_statement_match": "NOT_CHECKED",
            "upstream_kernel_acceptance": "NOT_CHECKED",
            "dashi_kernel_acceptance": "NOT_CHECKED",
            "same_object_transport": "NOT_ESTABLISHED",
        })
    bad = [x for x in results
           if x["source_text_status"] != "IDENTIFIER_TEXT_FOUND_UNVERIFIED"]
    return {
        "catalogue_rows": len(results),
        "source_identifiers_seen": len(results) - len(bad),
        "source_integrity_blockers": len(bad),
        "lexical_declaration_headers_seen": sum(
            bool(x["declaration_header_line_numbers"]) for x in results),
        "status": "SOURCE_TEXT_ONLY_NEVER_KERNEL",
        "rows": results,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--catalogue", required=True, type=Path)
    ap.add_argument("--upstream-root", required=True, type=Path)
    ap.add_argument("--json-out", required=True, type=Path)
    args = ap.parse_args()
    receipt = inspect(args.catalogue, args.upstream_root)
    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    print(json.dumps({k: v for k, v in receipt.items() if k != "rows"},
                     indent=2))
    if receipt["source_integrity_blockers"]:
        raise SystemExit("BLOCKED: source locations/identifiers need review")


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Audit a *source-qualified* OpenAI formalization inventory.

Read the actual upstream YAML from an explicit checkout, not a scraped README.
No external Python packages, network, CI, or implicit GitHub authentication.
A catalogue entry is not a theorem-import or a same-object port.
"""
import argparse
import json
import pathlib
import re
import sys
from collections import Counter

YAML_ENTRY = re.compile(
    r"^    - comparator_config: (\S+)\r?\n"
    r"      declaration: ([^\r\n]+)\r?\n"
    r"      file: ([^\r\n]+)", re.M)
LEAN_ENTRY = re.compile(
    r'\{ comparator := ("(?:[^"\\]|\\.)*"), '
    r'declaration := ("(?:[^"\\]|\\.)*"), '
    r'file := ("(?:[^"\\]|\\.)*") \}')


def parse_yaml(source: str):
    if "status:\n  scope: \"Partial progress.\"" not in source:
        raise ValueError("Upstream YAML scope changed; manual audit required")
    entries = YAML_ENTRY.findall(source)
    if not entries:
        raise ValueError("No source-qualified upstream comparator entries")
    return entries


def parse_lean(source: str):
    entries = [tuple(json.loads(x) for x in row)
               for row in LEAN_ENTRY.findall(source)]
    if not entries:
        raise ValueError("No Lean catalogue declarations found")
    return entries


def audit(upstream: pathlib.Path, catalogue: pathlib.Path):
    originals = parse_yaml(upstream.read_text(encoding="utf-8"))
    recorded = parse_lean(catalogue.read_text(encoding="utf-8"))
    source_counts = Counter(originals)
    recorded_counts = Counter(recorded)
    missing = list((source_counts-recorded_counts).elements())
    extra = list((recorded_counts-source_counts).elements())
    result = {
        "upstream_file": str(upstream),
        "catalogue_file": str(catalogue),
        "source_declarations": len(originals),
        "catalogue_declarations": len(recorded),
        "distinct_comparators": len({x[0] for x in originals}),
        "missing_from_catalogue": missing,
        "unexpected_in_catalogue": extra,
        "catalogue_agrees_with_supplied_upstream_checkout": not (missing or extra),
        "dashi_kernel_ports_established_by_this_audit": 0,
        "reason": "metadata agreement is not an Agda/Lean kernel receipt",
    }
    return result


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--upstream", type=pathlib.Path, required=True)
    p.add_argument("--catalogue", type=pathlib.Path, default=pathlib.Path(
        "Integration/OpenAIMath/FullUpstreamMainResultsCatalogue.lean"))
    p.add_argument("--json-out", type=pathlib.Path)
    args = p.parse_args()
    result = audit(args.upstream, args.catalogue)
    output = json.dumps(result, indent=2, ensure_ascii=False)
    if args.json_out:
        args.json_out.write_text(output + "\n", encoding="utf-8")
    print(output)
    return 0 if result["catalogue_agrees_with_supplied_upstream_checkout"] else 1


if __name__ == "__main__":
    sys.exit(main())

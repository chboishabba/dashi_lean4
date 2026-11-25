#!/usr/bin/env python3
"""Audit actual Lean axiom output; no proof authority from text alone."""
import argparse
import pathlib
import re

UPSTREAM = (
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
)
ADAPTER = tuple("DASHI.AlpogeRH." + x for x in (
    "original_mathlib_rh",
    "original_riemann_zero_location",
    "original_dirichlet_nonvanishing",
    "original_dirichlet_zeros",
    "original_primitive_dirichlet_zeros",
    "original_dirichlet_zero_horizontal",
    "original_dirichlet_cosh_collapse",
))
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def audit(txt, targets):
    result = {}
    for full in targets:
        # Lean v4.33.1 and v4.35.0 Elab/Print.lean printAxiomsOf.
        pat = (r"(?m)^(?:[^\r\n]*:\d+:\d+:[ \t]*info:[ \t]*|info:[ \t]*)?'"
               + re.escape(full)
               + r"' (?:depends on axioms:[ \t]*\[([^\]]*)\]|does not depend on any axioms)[ \t]*\r?$")
        receipts = list(re.finditer(pat, txt))
        if len(receipts) != 1:
            raise ValueError(f"expected one axiom receipt for {full}, got {len(receipts)}")
        raw = receipts[0].group(1)
        axioms = [] if raw is None else [a.strip() for a in raw.split(",")]
        if raw is not None and (not all(axioms) or len(axioms) != len(set(axioms))):
            raise ValueError(f"malformed axiom list for {full}")
        extra = set(axioms) - ALLOWED
        if extra:
            raise ValueError(f"unexpected axioms for {full}: {sorted(extra)}")
        result[full] = sorted(axioms)
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mode", choices=("upstream", "adapter"))
    parser.add_argument("log", type=pathlib.Path)
    args = parser.parse_args()
    try:
        result = audit(args.log.read_text(encoding="utf-8"), UPSTREAM if args.mode == "upstream" else ADAPTER)
    except (ValueError, OSError) as exc:
        parser.exit(1, f"BLOCKED: {exc}\n")
    for name, axioms in result.items():
        print(f"PASS axiom receipt: {name}: {axioms}")
    print(f"PASS {len(result)}/{len(result)} {args.mode} axiom receipts")


if __name__ == "__main__":
    main()

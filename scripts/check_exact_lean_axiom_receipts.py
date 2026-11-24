#!/usr/bin/env python3
"""Check exact Lean #print axioms reports; no proof or kernel substitute."""
import argparse
import re
from pathlib import Path

ALLOWED = frozenset({'propext', 'Classical.choice', 'Quot.sound'})


def audit(log, targets):
    result = {}
    for name in targets:
        pattern = (r"'" + re.escape(name) +
                   r"'\s+(?:depends on axioms:\s*\[([^\]]*)\]|(does not depend on any axioms))")
        reports = list(re.finditer(pattern, log))
        if not reports:
            raise ValueError(f'missing exact Lean axiom receipt for {name}')
        sets = [frozenset(a.strip() for a in (m.group(1) or '').split(',') if a.strip()) for m in reports]
        if any(s != sets[0] for s in sets):
            raise ValueError(f'conflicting axiom receipts for {name}')
        unexpected = sets[0] - ALLOWED
        if unexpected:
            raise ValueError(f'unexpected axioms for {name}: {sorted(unexpected)}')
        result[name] = sets[0]
    return result


def self_test():
    name = 'DASHI.AlpogeRH.original_mathlib_rh'
    good = f"'{name}' depends on axioms: [propext, Classical.choice,\n Quot.sound]"
    empty = f"'{name}' does not depend on any axioms"
    assert audit(good, [name])[name] == ALLOWED
    assert audit(empty, [name])[name] == frozenset()
    assert audit(good + '\n' + good, [name])[name] == ALLOWED
    bad = ['', name, f"axioms of {name}: [propext]", f"'{name}X' depends on axioms: [propext]", good.replace('Quot.sound', 'sorryAx'), good.replace('Quot.sound', 'Custom.axiom'), good+'\n'+empty]
    for fixture in bad:
        try:
            audit(fixture, [name])
        except ValueError:
            continue
        raise AssertionError(f'accepted invalid fixture: {fixture}')
    print('PASS: 3 positive, 7 negative receipt-parser fixtures (not Lean execution)')


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--self-test', action='store_true')
    p.add_argument('log', nargs='?')
    p.add_argument('targets', nargs='*')
    args = p.parse_args()
    if args.self_test:
        self_test()
    else:
        if not args.log or not args.targets:
            p.error('log and exact target names required')
        try:
            for name, axioms in audit(Path(args.log).read_text(encoding='utf-8'), args.targets).items():
                print(f'PASS exact axiom receipt: {name}: {sorted(axioms)}')
        except ValueError as exc:
            p.exit(1, f'BLOCKED: {exc}\n')

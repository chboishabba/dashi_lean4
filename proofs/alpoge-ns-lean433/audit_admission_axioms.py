"""Fail-closed Lean #print axioms audit; checks evidence, not certificate data."""
import re
import sys
from pathlib import Path

EXPECTED = {
    "Breakdown.breakdown_on_space",
    "Breakdown.breakdown_on_torus",
    "Breakdown.CellLayerSystem.breakdownOnSpaceAndTorus_of_cell_system_condition",
    "DASHI.AlpogeBuckmaster.from_profile",
    "DASHI.AlpogeBuckmaster.from_original_cell_condition",
    "DASHI.AlpogeBuckmaster.solution_original",
    "DASHI.AlpogeBuckmaster.original_torus_to_clayD",
    "DASHI.AlpogeBuckmaster.original_cell_condition_to_clayD",
}
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
PATTERN = re.compile(
    r"(?m)^(?:[^\r\n]*:\d+:\d+:[ \t]*info:[ \t]*|info:[ \t]*)?'([^']+)' "
    r"(?:depends on axioms:[ \t]*\[([^\]]*)\]|does not depend on any axioms)[ \t]*\r?$"
)

def audit(log):
    if re.search(r"(?im)\berror:|declaration uses 'sorry'|\bsorryAx\b", log):
        raise ValueError("Lean error or sorry evidence")
    seen = {}
    for match in PATTERN.finditer(log):
        name, body = match.groups()
        if name not in EXPECTED or name in seen:
            raise ValueError(f"unexpected or duplicate declaration: {name}")
        items = [] if body is None else [item.strip() for item in body.split(",")]
        if body is not None and (not all(items) or len(set(items)) != len(items)):
            raise ValueError(f"{name}: malformed axiom list")
        axioms = set(items)
        if not axioms <= ALLOWED:
            raise ValueError(f"{name}: unexpected axioms {axioms - ALLOWED}")
        seen[name] = axioms
    if set(seen) != EXPECTED:
        raise ValueError(f"missing declarations: {EXPECTED - set(seen)}")
    return seen

def self_test():
    good = "\n".join(f"'{n}' depends on axioms: [propext, Quot.sound,\n Classical.choice]" for n in sorted(EXPECTED))
    audit(good)
    empty = "\n".join(f"'{n}' does not depend on any axioms" for n in sorted(EXPECTED))
    audit(empty)
    audit("\n".join("Proof.lean:12:3: info: " + line if line.startswith("\'") else line for line in good.splitlines()))
    audit(good.replace("\n", "\r\n"))
    controls = [
        "", good + "\n" + good, good.replace("propext", "evil"),
        good.replace("Quot.sound", "sorryAx"), good + "\nerror: failure",
        good.replace("depends on axioms:", "unknown format"),
        good + "\nwarning: declaration uses 'sorry'",
        good + "\n'Unrelated' depends on axioms: []",
        good.replace("propext", "propext, propext"),
        good.replace("propext", "propext,"),
    ]
    for bad in controls:
        try:
            audit(bad)
        except ValueError:
            continue
        raise RuntimeError("accepted malformed evidence")
    print("14/14 axiom parser controls PASS")

if __name__ == "__main__":
    if sys.argv[1:] == ["--self-test"]:
        self_test()
    elif len(sys.argv) == 2:
        for name, axioms in sorted(audit(Path(sys.argv[1]).read_text()).items()):
            print(name, sorted(axioms))
    else:
        raise SystemExit("usage: audit_admission_axioms.py LOG | --self-test")

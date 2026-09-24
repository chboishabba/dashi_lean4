#!/usr/bin/env python3
"""Static Agda import-resolution check for the DASHI corpus.

No Agda toolchain is available in this environment, so this script does *not*
typecheck anything.  What it does is exact and mechanical:

* collect every module name that is present as a file under ``Agda/`` (and the
  vendored ``bishop``/``dchott``/``cubical`` trees);
* parse every ``import M`` / ``open import M`` line of every ``.agda`` file
  under ``Agda/DASHI``;
* report the imports that name a ``DASHI.*`` module with no corresponding file.

Standard-library imports (``Data.*``, ``Relation.*``, ``Agda.*``, ``Function``,
``Level`` and the like) are outside the shipped tree and are reported
separately as *external*, never as broken.

Usage:  python3 scripts/agda_import_check.py [--json]
"""

from __future__ import annotations

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AGDA = os.path.join(ROOT, "Agda")

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.'-]+)")


def module_files() -> set[str]:
    """Every module name that exists as a file in the shipped tree."""
    names: set[str] = set()
    for base, _dirs, files in os.walk(AGDA):
        for f in files:
            if not (f.endswith(".agda") or f.endswith(".lagda")):
                continue
            rel = os.path.relpath(os.path.join(base, f), AGDA)
            rel = rel[: rel.rindex(".")]
            names.add(rel.replace(os.sep, "."))
    return names


def dashi_sources() -> list[str]:
    out = []
    for base, _dirs, files in os.walk(os.path.join(AGDA, "DASHI")):
        for f in files:
            if f.endswith(".agda"):
                out.append(os.path.join(base, f))
    return sorted(out)


def main() -> int:
    present = module_files()
    unresolved: dict[str, list[str]] = {}
    external: set[str] = set()
    total_imports = 0
    for path in dashi_sources():
        rel = os.path.relpath(path, ROOT)
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = IMPORT_RE.match(line)
                if not m:
                    continue
                name = m.group(1)
                total_imports += 1
                if name in present:
                    continue
                if name.startswith("DASHI."):
                    unresolved.setdefault(rel, []).append(name)
                else:
                    external.add(name)

    report = {
        "dashi_files": len(dashi_sources()),
        "import_lines": total_imports,
        "modules_present": len(present),
        "external_module_names": len(external),
        "files_with_unresolved_dashi_imports": len(unresolved),
        "unresolved": unresolved,
    }
    if "--json" in sys.argv:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(f"DASHI .agda files scanned : {report['dashi_files']}")
        print(f"import lines parsed       : {report['import_lines']}")
        print(f"module files present      : {report['modules_present']}")
        print(f"external (library) modules: {report['external_module_names']}")
        print(f"unresolved DASHI imports  : {sum(len(v) for v in unresolved.values())}"
              f" in {len(unresolved)} files")
        for f, names in sorted(unresolved.items()):
            for n in sorted(set(names)):
                print(f"  {f}: {n}")
    return 1 if unresolved else 0


if __name__ == "__main__":
    raise SystemExit(main())

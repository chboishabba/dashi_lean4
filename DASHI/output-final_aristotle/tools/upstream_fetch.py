#!/usr/bin/env python3
"""Fetch the upstream DASHI Agda repository and vendor its *new* material into
`upstream/dashi_agda/`.

The corpus under `upstream/dashi_agda/` is what the Lean Agda front end
(`RequestProject/Agda/`) reads, what `tools/agdacheck.py` and
`tools/agda2lean.py` turn into the `AgdaCheck` and `AgdaVendor` libraries, and
what the coverage reports in `docs/` measure.  It is a *selection* of the
upstream repository rather than a mirror of it: upstream `master` alone carries
eleven thousand Agda modules, and the interesting content of the several hundred
`agent/…` branches is the handful of files each one adds to or changes from
`master`.

This tool computes that selection mechanically.  Against a bare clone of the
upstream remote it works out, for every branch,

  * the paths the branch adds to `master` (`--new`), and
  * the paths whose content the branch changes from `master` (`--changed`),

selects the requested slice (optionally restricted by `--match` to paths whose
name matches a regular expression, e.g. `Wikidata`), closes the selection under
the `import` graph so that every dependency a selected module names is vendored
too, and writes the files out under `upstream/dashi_agda/<ref>/<path>` with a
row in `upstream/dashi_agda/MANIFEST.tsv` recording the ref, the commit and the
SHA-256 of the content.

Usage
-----

    # what is upstream that is not here yet
    python3 tools/upstream_fetch.py --report

    # vendor every Wikidata module upstream has, with its import closure
    python3 tools/upstream_fetch.py --emit --match Wikidata --closure

    # vendor everything the branches add to master
    python3 tools/upstream_fetch.py --emit --new

The clone is cached in `--cache` (default `/tmp/dashi_agda.git`); pass
`--offline` to work from the cache without contacting the remote.
"""

from __future__ import annotations

import argparse
import collections
import hashlib
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.join(ROOT, "upstream", "dashi_agda")
MANIFEST = os.path.join(CORPUS, "MANIFEST.tsv")
REMOTE = "https://github.com/chboishabba/dashi_agda"

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+(\S+)")


# --------------------------------------------------------------------------
# the upstream clone
# --------------------------------------------------------------------------

def git(cache: str, *args: str, text: bool = True, stdin: str | None = None):
    return subprocess.run(["git", f"--git-dir={cache}", *args],
                          input=stdin, capture_output=True, text=text,
                          check=True).stdout


def ensure_clone(cache: str, offline: bool) -> None:
    if os.path.isdir(cache):
        if not offline:
            subprocess.run(["git", f"--git-dir={cache}", "fetch", "--depth", "1",
                            "origin", "+refs/heads/*:refs/heads/*"], check=False)
        return
    if offline:
        sys.exit(f"no clone at {cache} and --offline was given")
    subprocess.run(["git", "clone", "--bare", "--depth", "1",
                    "--no-single-branch", REMOTE, cache], check=True)


def refs(cache: str) -> dict[str, str]:
    out = {}
    for line in git(cache, "for-each-ref", "--format=%(refname:short)\t%(objectname)",
                    "refs/heads").splitlines():
        name, _, oid = line.partition("\t")
        out[name] = oid
    return out


def tree(cache: str, ref: str) -> dict[str, str]:
    """`{path: blob}` for the `.agda` files of a ref."""
    out = {}
    for line in git(cache, "ls-tree", "-r", "--format=%(objectname)\t%(path)",
                    ref).splitlines():
        oid, _, path = line.partition("\t")
        if path.endswith(".agda"):
            out[path] = oid
    return out


def blob(cache: str, oid: str) -> str:
    return git(cache, "cat-file", "blob", oid)


# --------------------------------------------------------------------------
# what is here already
# --------------------------------------------------------------------------

def vendored() -> dict[str, set[str]]:
    """`{path: {ref}}` for what the corpus carries, with `path` relative to the
    ref directory (`DASHI/…`, `Ontology/…`)."""
    out: dict[str, set[str]] = collections.defaultdict(set)
    for line in open(MANIFEST, encoding="utf-8"):
        ref, _commit, path, _sha = line.rstrip("\n").split("\t")
        out[path].add(ref)
    return out


def ref_dir(ref: str) -> str:
    return os.path.join(CORPUS, *ref.split("/"))


# --------------------------------------------------------------------------
# selection
# --------------------------------------------------------------------------

def module_path(mod: str) -> str:
    return mod.replace(".", "/") + ".agda"


def closure(cache: str, master: dict[str, str], seeds: set[str]) -> set[str]:
    """Close a set of master paths under `import`, staying inside master."""
    seen, stack = set(seeds), list(seeds)
    while stack:
        p = stack.pop()
        if p not in master:
            continue
        for line in blob(cache, master[p]).splitlines():
            m = IMPORT_RE.match(line)
            if not m:
                continue
            q = module_path(m.group(1))
            if q in master and q not in seen:
                seen.add(q)
                stack.append(q)
    return seen


def survey(cache: str) -> tuple[dict[str, str], dict[str, dict[str, str]]]:
    """`(master, {ref: {path: blob}})` for every branch that differs."""
    master = tree(cache, "master")
    branches = {}
    for ref in refs(cache):
        if ref == "master":
            continue
        t = tree(cache, ref)
        diff = {p: o for p, o in t.items() if master.get(p) != o}
        if diff:
            branches[ref] = diff
    return master, branches


# --------------------------------------------------------------------------
# emission
# --------------------------------------------------------------------------

def emit(cache: str, plan: list[tuple[str, str, str]], commits: dict[str, str],
         dry: bool) -> int:
    """`plan` is a list of `(ref, path, blob)`; returns the number written."""
    rows = []
    written = 0
    for ref, path, oid in plan:
        dest = os.path.join(ref_dir(ref), path)
        text = blob(cache, oid)
        sha = hashlib.sha256(text.encode("utf-8")).hexdigest()
        rows.append(f"{ref}\t{commits[ref]}\t{path}\t{sha}")
        if dry:
            continue
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        with open(dest, "w", encoding="utf-8") as fh:
            fh.write(text)
        written += 1
    if not dry and rows:
        have = set()
        if os.path.exists(MANIFEST):
            have = {l.rstrip("\n") for l in open(MANIFEST, encoding="utf-8")}
        keep = {(l.split("\t")[0], l.split("\t")[2]) for l in have}
        fresh = [r for r in rows if (r.split("\t")[0], r.split("\t")[2]) not in keep]
        allrows = sorted(have | set(fresh))
        with open(MANIFEST, "w", encoding="utf-8") as fh:
            fh.write("\n".join(allrows) + "\n")
    return written


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cache", default="/tmp/dashi_agda.git")
    ap.add_argument("--offline", action="store_true")
    ap.add_argument("--report", action="store_true",
                    help="say what upstream has that the corpus does not")
    ap.add_argument("--emit", action="store_true", help="vendor the selection")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--new", action="store_true",
                    help="select the paths the branches add to master")
    ap.add_argument("--changed", action="store_true",
                    help="select the paths the branches change from master")
    ap.add_argument("--master", action="store_true",
                    help="select from master itself (use with --match)")
    ap.add_argument("--match", default=None,
                    help="restrict the selection to paths matching this regex")
    ap.add_argument("--variants", action="store_true",
                    help="with --changed, vendor a branch's copy of a path even "
                         "when master's copy is already in the corpus")
    ap.add_argument("--closure", action="store_true",
                    help="add the master import closure of the selection")
    args = ap.parse_args()

    ensure_clone(args.cache, args.offline)
    commits = refs(args.cache)
    master, branches = survey(args.cache)
    here = vendored()
    pat = re.compile(args.match) if args.match else None

    if args.report:
        newp = collections.defaultdict(set)
        chgp = collections.defaultdict(set)
        for ref, diff in branches.items():
            for p in diff:
                (newp if p not in master else chgp)[p].add(ref)
        print(f"upstream refs: {len(commits)}  master modules: {len(master)}")
        print(f"branches differing from master: {len(branches)}")
        print(f"paths the branches add to master: {len(newp)}")
        print(f"paths the branches change from master: {len(chgp)}")
        print(f"corpus here: {len(here)} paths, "
              f"{sum(len(v) for v in here.values())} files")
        missing = [p for p in master if p not in here]
        print(f"master paths not vendored: {len(missing)}")
        if pat:
            m = sorted(p for p in master if pat.search(p))
            print(f"\nmaster paths matching {args.match!r}: {len(m)}")
            for p in m:
                print(("  have " if p in here else "  MISSING ") + p)
            for p, rs in sorted(newp.items()):
                if pat.search(p):
                    print(f"  branch-new {p}  [{sorted(rs)[0]}]")
            for p, rs in sorted(chgp.items()):
                if pat.search(p):
                    print(f"  branch-changed {p}  [{len(rs)} refs]")
        return

    # ---- build the selection -------------------------------------------
    plan: dict[tuple[str, str], str] = {}
    seeds: set[str] = set()

    if args.master:
        for p, o in master.items():
            if pat and not pat.search(p):
                continue
            seeds.add(p)
            if p not in here:
                plan[("master", p)] = o

    if args.new or args.changed:
        for ref, diff in sorted(branches.items()):
            for p, o in diff.items():
                if pat and not pat.search(p):
                    continue
                isnew = p not in master
                if isnew and not args.new:
                    continue
                if not isnew and not args.changed:
                    continue
                if p in here and not (args.variants and not isnew
                                      and ref not in here.get(p, ())):
                    continue
                if any((r, p) in plan for r in commits):
                    continue          # one branch's copy of a path is enough
                plan[(ref, p)] = o
                if not isnew:
                    seeds.add(p)

    if args.closure and seeds:
        for p in sorted(closure(args.cache, master, seeds)):
            if p not in here and ("master", p) not in plan:
                plan[("master", p)] = master[p]

    ordered = sorted((ref, path, oid) for (ref, path), oid in plan.items())
    print(f"selected {len(ordered)} files to vendor")
    for ref, path, _ in ordered[:20]:
        print(f"  {ref}\t{path}")
    if len(ordered) > 20:
        print(f"  … and {len(ordered) - 20} more")
    if args.emit:
        n = emit(args.cache, ordered, commits, args.dry_run)
        print(f"wrote {n} files under upstream/dashi_agda/")


if __name__ == "__main__":
    main()

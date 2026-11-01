#!/usr/bin/env python3
"""Offline, exhaustive *candidate* routing over the exact OpenAI math catalogue.

No theorem equivalence, relative strength, authorship, or kernel verification
is inferred from a lexical score. Run with side-by-side source checkouts.
Emits 208 declaration rows AND 373 result-family rows, retaining blanks and
explicit unresolved proof obligations rather than silently dropping them.

Original source: openai/math CONTENTS.md and lean/formalization.yaml.
DASHI original theorem owners remain authoritative; search must not extend ESD.
"""
import argparse
import csv
import json
import re
import subprocess
from collections import Counter, defaultdict
from pathlib import Path

ENTRY = re.compile(
    r'comparator\s*:=\s*"([^"]+)"\s*,\s*'
    r'declaration\s*:=\s*"([^"]+)"\s*,\s*'
    r'file\s*:=\s*"([^"]+)"'
)
FAMILY = re.compile(r'\*\*(\d{3})\.\s+(.+?)\*\*')
CAMEL = re.compile(r'[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+')
SKIP = {
    "dashi", "openai", "oai", "lean", "agda", "main", "proof",
    "theorem", "result", "exact", "source", "default", "statement",
    "comparator", "solution", "math", "mathematics", "formalization",
    "compute", "computability", "comparison", "research", "shared",
    "models", "model", "theory", "algebra", "analysis", "number",
    "new", "conjecture", "general", "paper", "local", "global",
    "finite", "properties", "all", "test", "types", "native",
}
SOURCE_SUFFIXES = {".agda", ".lean"}
# Source declaration names provide independent search evidence when the
# filename is generic (e.g. AlgebraicHierarchyExact.agda). A name match is a
# discovery lead only; it does not identify the same mathematical object.
AGDA_DECL = re.compile(r"(?m)^([A-Za-z_][A-Za-z0-9_'-]*)\s*:")
LEAN_DECL = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_.']*)\b"
)

def declaration_words(path):
    """Search actual top-level Agda signatures and Lean declaration headers.

    Read-only, deterministic, index-only: the tool never assumes the
    declarations compile, own an upstream theorem, or preserve its statement.
    """
    source = path.read_text(encoding="utf-8", errors="replace")
    grammar = AGDA_DECL if path.suffix == ".agda" else LEAN_DECL
    return {word for symbol in grammar.findall(source) for word in words(symbol)}

REVIEWED_SEEDS = {
    # These are real source-path discoveries / previous provenance owners.
    # They are candidate interfaces, NOT verified theorem equivalences.
    "SubexponentialSAT": [
        "DASHI/Research/OpenAIMath/OpenAIMathFiniteSupportedTseitinModelsExact.agda",
        "DASHI/Mathematics/Complexity/PNotEqualsNPConcreteCircuitSharedSemanticsExact.agda",
    ],
    "OptimalMaxCut": [
        "DASHI/Combinatorics/GraphColouring369PantsWeightedMaxCutExact.agda",
    ],
    "UniqueGamesTheorem": [
        "DASHI/Combinatorics/GraphColouring369PantsWeightedMaxCutExact.agda",
    ],
    "HodgeConjectureCMAbelianVarieties": [
        "DASHI/Mathematics/AlgebraicGeometry/HodgePrizeBoundaryExact.agda",
        "DASHI/Mathematics/AlgebraicGeometry/HodgeDecompositionCycleClassExact.agda",
    ],
    "QuasiRiemannHypothesis": [
        "DASHI/Research/OpenAIMath/OpenAIMathSourceAtlasExact.agda",
    ],
    "LocalSmoothing": [
        "DASHI/Papers/NavierStokes/Everything.agda",
    ],
}

def words(s):
    parts = []
    for part in re.split(r'[^a-zA-Z0-9]+', s):
        parts.extend(CAMEL.findall(part))
    return {x.lower() for x in parts if len(x) > 2 and x.lower() not in SKIP}

def catalog(path):
    source = path.read_text(encoding="utf-8")
    rows = ENTRY.findall(source)
    if len(rows) != 208:
        raise ValueError(f"Expected 208 source declarations, found {len(rows)}")
    if len(set(rows)) != len(rows):
        raise ValueError("Duplicated exact comparator/declaration/file rows")
    return rows

def families(contents):
    source = contents.read_text(encoding="utf-8")
    rows = FAMILY.findall(source)
    # One main heading per family, rather than per constituent manuscript.
    unique = {}
    for number, title in rows:
        unique.setdefault(number, re.sub(r'<[^>]+>', '', title).strip())
    if len(unique) != 373:
        raise ValueError(f"Expected 373 family headings, found {len(unique)}")
    return unique


def manuscripts(contents):
    """Extract all paper references from family-bounded Markdown sections.

    A single URL contains 'CAT(0)' in its directory; simplistic
    /preprints...[^)]/ matching therefore silently loses one paper.
    Balanced parenthesis matching keeps all 721 manuscript references.
    """
    source = contents.read_text(encoding="utf-8")
    headers = list(FAMILY.finditer(source))
    result = []
    for i, match in enumerate(headers):
        number = match.group(1)
        end = headers[i + 1].start() if i + 1 < len(headers) else len(source)
        block = source[match.end():end]
        start = 0
        while True:
            opener = block.find("](preprints/", start)
            if opener < 0:
                break
            k = opener + 2
            depth = 1
            j = k
            while j < len(block):
                if block[j] == "(":
                    depth += 1
                elif block[j] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                j += 1
            if depth != 0:
                raise ValueError(f"Unbalanced manuscript link in family {number}")
            url = block[k:j]
            if not url.lower().endswith(".pdf"):
                raise ValueError(f"Not a PDF manuscript link: {url}")
            title_start = block.rfind("[", 0, opener)
            title = (block[title_start + 1:opener].strip()
                     if title_start >= 0 else "")
            result.append({"family_id": number, "title": title,
                           "manuscript_path": url,
                           "formal_theorem": "NOT_ESTABLISHED",
                           "dashi_owner": "NOT_ESTABLISHED"})
            start = j + 1
    if len(result) != 721:
        raise ValueError(f"Expected 721 manuscript references, found {len(result)}")
    return result

def source_paths(root, subtree):
    src = root / subtree
    if not src.is_dir():
        return
    for p in src.rglob("*"):
        if p.is_file() and p.suffix in SOURCE_SUFFIXES:
            if not any(x in p.parts for x in
                       (".lake", ".git", "vendor", "node_modules")):
                yield p

def owner_index(agda, lean):
    index = defaultdict(set)
    # The original Lean theorem owner may live outside Integration/.
    # Search the full Lean source tree (excluding vendor/generated dirs).
    roots = ((agda, "DASHI"), (lean, "."))
    for root, sub in roots:
        for path in source_paths(root, sub):
            rel = path.relative_to(root).as_posix()
            if "/OpenAIMath/" in rel:
                # Prevent catalogue metadata echoing back as proof evidence.
                continue
            # Path tokens are cheap first-stage search evidence. Index real
            # source declaration identifiers too, so differently named
            # theorem owners are not completely invisible to discovery.
            candidate_tokens = words(rel) | declaration_words(path)
            for w in candidate_tokens:
                index[w].add((str(root), rel))
    return index

def first_addition(root, rel):
    try:
        x = subprocess.run(
            ["git", "-C", str(root), "log", "--all", "--diff-filter=A",
             "--follow", "--format=%H%x09%aI%x09%an", "--", rel],
            text=True, capture_output=True, check=True, timeout=20,
        ).stdout.strip().splitlines()
        # Git log output is newest first; earliest addition is the LAST hit.
        return x[-1] if x else ""
    except (OSError, subprocess.SubprocessError):
        return ""

def proposals(index, query, comparator, limit):
    """Must share an actual subject token, not only domain/generic terms."""
    subject = words(comparator)
    allterms = words(query)
    score = Counter()
    anchored = set()
    for w in allterms:
        for source in index.get(w, set()):
            score[source] += 1
            if w in subject:
                anchored.add(source)
    return [(root, path, val) for (root, path), val
            in sorted(score.items(), key=lambda t: (-t[1], t[0][1]))
            if val >= 2 and (root, path) in anchored][:limit]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--agda-root", type=Path, required=True)
    ap.add_argument("--lean-root", type=Path, required=True)
    ap.add_argument("--upstream-root", type=Path, required=True)
    ap.add_argument("--out-dir", type=Path, required=True)
    ap.add_argument("--topk", type=int, default=4)
    args = ap.parse_args()
    if args.topk <= 0:
        ap.error("--topk must be positive")
    cat = args.lean_root / "Integration/OpenAIMath/FullUpstreamMainResultsCatalogue.lean"
    data = catalog(cat)
    family_map = families(args.upstream_root / "CONTENTS.md")
    paper_rows = manuscripts(args.upstream_root / "CONTENTS.md")
    inverted = owner_index(args.agda_root, args.lean_root)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    allrows = []
    for i, (comp, decl, source) in enumerate(data, start=1):
        comp_name = comp.rstrip("/").split("/")[-1].removesuffix(".json")
        if comp_name == "main" and "/" in comp:
            comp_name = comp.split("/")[-2]
        candidate_query = " ".join((comp_name, decl, source))
        suggested = proposals(inverted, candidate_query, comp_name, args.topk)
        # Historical proof-owner seeds are separately labelled and never
        # allowed to upgrade to an established same-object relationship.
        seeds = []
        for rel in REVIEWED_SEEDS.get(comp_name, ()):
            root = args.agda_root
            if (root / rel).is_file():
                seeds.append((str(root), rel, "source-owner-seed"))
        seen = set()
        combined = []
        for root, path, evidence in seeds + suggested:
            if (root, path) not in seen:
                seen.add((root, path))
                combined.append((root, path, evidence))
        for candidate_rank, (root, path, evidence) in enumerate(
                combined[:args.topk], start=1):
            # The commit's existence is an attribution lead, not a
            # mathematical source-identity certificate.
            combined[candidate_rank - 1] = (
                root, path, evidence, first_addition(root, path))
        allrows.append({
            "catalogue_index": i, "comparator": comp,
            "declaration": decl, "upstream_source": source,
            "upstream_revision": "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a",
            "candidates": combined[:args.topk],
            "candidate_status": "LEXICAL_OR_SOURCE_OWNER_CANDIDATE_ONLY",
            "same_object": "NOT_ESTABLISHED",
            "stronger_or_equivalent": "NOT_EVALUATED",
            "lean_kernel": "NO_DASHI_RECEIPT",
            "agda_kernel": "NO_DASHI_RECEIPT",
            "required_proof": "typed carrier, hypotheses, conclusion, equivalence or implication",
            "required_attribution": "original author/date; earliest in-repo owner; donor commit",
        })
    frows = [
        {"family_id": key, "title": family_map[key],
         "family_to_declaration": "NOT_ESTABLISHED",
         "manuscript_and_prio": "REVIEW_REQUIRED",
         "same_object": "NOT_ESTABLISHED"}
        for key in sorted(family_map)
    ]
    (args.out_dir / "declarations.json").write_text(
        json.dumps(allrows, indent=2, ensure_ascii=False) + "\n")
    (args.out_dir / "families.json").write_text(
        json.dumps(frows, indent=2, ensure_ascii=False) + "\n")
    (args.out_dir / "manuscripts.json").write_text(
        json.dumps(paper_rows, indent=2, ensure_ascii=False) + "\n")
    with (args.out_dir / "declarations.tsv").open("w", newline="") as f:
        w = csv.writer(f, delimiter="\t")
        w.writerow(["i", "comparator", "declaration", "source",
                    "candidate_path", "candidate_evidence", "earliest_addition",
                    "same_object", "relative_strength", "kernel"])
        for row in allrows:
            cs = row["candidates"] or [("", "", "", "")]
            for r, path, evidence, origin in cs:
                w.writerow([row["catalogue_index"], row["comparator"],
                            row["declaration"], row["upstream_source"], path,
                            evidence, origin, row["same_object"],
                            row["stronger_or_equivalent"], row["agda_kernel"]])
    summary = {
        "declarations": len(allrows), "families": len(frows),
        "manuscripts": len(paper_rows),
        "declarations_with_candidate": sum(bool(x["candidates"]) for x in allrows),
        "same_object_verified": 0, "kernel_ports_verified": 0,
        "notes": "Coverage is metadata/candidate discovery, not proof import",
    }
    (args.out_dir / "audit.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()

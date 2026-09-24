# -*- coding: utf-8 -*-
"""Figures for the infographics in `docs/`, counted from the sources.

Run from the project root.  Nothing here is hand-maintained: every number the
posters show that can be counted is counted here, so the images cannot drift
away from the repository.

    python3 docs/stats.py            # print the figures as JSON
"""
import json
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "RequestProject")
DATA = os.path.join(ROOT, "data")

THM = re.compile(r"^\s*(theorem|lemma)\s")
DEF = re.compile(r"^\s*(noncomputable )?(private )?(def|abbrev|structure|inductive|instance)\s")
DECIDE = re.compile(r"by\s+(native_)?decide")
EVAL = re.compile(r"^#eval")
SORRY = re.compile(r"\bsorry\b|\badmit\b")
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def is_gap(line):
    """does this line really leave a proof gap?

    String literals are blanked first — the downloaded glossary quotes Wikidata
    descriptions such as "sciences that admit of absolute precision" — and so is
    the trailing line comment.
    """
    code = STRING.sub('""', line).split("--")[0]
    return bool(SORRY.search(code))


def lean_files():
    out = []
    for base, _, names in os.walk(SRC):
        for n in sorted(names):
            if n.endswith(".lean"):
                out.append(os.path.join(base, n))
    return sorted(out)


def module_name(path):
    rel = os.path.relpath(path, SRC)[: -len(".lean")]
    return rel.replace(os.sep, "/")


def per_module():
    """module name -> {theorems, defs, lines, decides, evals, sorries}."""
    d = {}
    for p in lean_files():
        txt = open(p, encoding="utf-8").read()
        lines = txt.splitlines()
        d[module_name(p)] = {
            "theorems": sum(1 for l in lines if THM.match(l)),
            "defs": sum(1 for l in lines if DEF.match(l)),
            "lines": len(lines),
            "decides": sum(1 for l in lines if DECIDE.search(l)),
            "evals": sum(1 for l in lines if EVAL.match(l)),
            "sorries": sum(1 for l in lines if is_gap(l)),
        }
    return d


def kb_counts(path):
    """items / sub / inst / disj records of a `.wdkb` or `.skb` file."""
    c = {"items": 0, "sub": 0, "inst": 0, "disj": 0}
    for line in open(path, encoding="utf-8"):
        tag = line.split("\t", 1)[0]
        if tag == "item":
            c["items"] += 1
        elif tag in ("sub", "inst", "disj"):
            c[tag] += 1
    return c


def derived_counts(module_path):
    """lengths of the `derivedSub` / `derivedInst` lists of a generated module."""
    txt = open(module_path, encoding="utf-8").read()
    out = {}
    for field in ("derivedSub", "derivedInst"):
        m = re.search(r"def " + field + r" : List \(Qid × Qid\) :=\n(.*?)\n\n", txt, re.S)
        out[field] = len(re.findall(r"\(Qid\.", m.group(1))) if m else 0
    return out


def derived_pairs(module_path, field):
    """the (a, b) pairs of a `derivedSub` / `derivedInst` list of a module."""
    txt = open(module_path, encoding="utf-8").read()
    m = re.search(r"def " + field + r" : List \(Qid . Qid\) :=\n(.*?)\n\n", txt, re.S)
    if not m:
        return set()
    return set(re.findall(r'\(Qid\.\w+ "([^"]+)", Qid\.\w+ "([^"]+)"\)', m.group(1)))


def merge_gain(merged="Core", fragments=("DouglasAdams", "UpperOntology", "Geography",
                                         "CreativeWorks", "Science", "Technology",
                                         "Mathematics", "LifeSciences", "Society",
                                         "Chemistry", "Events")):
    """facts the merged corpus entails that no single fragment entails."""
    gen = os.path.join(SRC, "Generated")
    out = {}
    for field in ("derivedSub", "derivedInst"):
        whole = derived_pairs(os.path.join(gen, merged + ".lean"), field)
        parts = set()
        for f in fragments:
            parts |= derived_pairs(os.path.join(gen, f + ".lean"), field)
        out[field] = len(whole - parts)
    return out


def totals():
    mods = per_module()
    hand = {k: v for k, v in mods.items() if not k.startswith("Generated/")}
    t = {
        "modules": len(mods),
        "handwritten_modules": len(hand),
        "generated_modules": len(mods) - len(hand),
        "theorems": sum(v["theorems"] for v in mods.values()),
        "handwritten_theorems": sum(v["theorems"] for v in hand.values()),
        "defs": sum(v["defs"] for v in mods.values()),
        "lines": sum(v["lines"] for v in mods.values()),
        "decides": sum(v["decides"] for v in mods.values()),
        "evals": sum(v["evals"] for v in mods.values()),
        "sorries": sum(v["sorries"] for v in mods.values()),
    }
    return t, mods


def corpus():
    out = {}
    for n in sorted(os.listdir(DATA)):
        if n.endswith(".wdkb"):
            out[n[: -len(".wdkb")]] = kb_counts(os.path.join(DATA, n))
    gen = os.path.join(SRC, "Generated")
    for n in sorted(os.listdir(gen)):
        if n.endswith(".lean"):
            out.setdefault("_derived", {})[n[: -len(".lean")]] = derived_counts(
                os.path.join(gen, n))
    return out


def glossary():
    """the grounded glossary: what `scripts/fetch_glossary.py` downloaded."""
    rows = [l.rstrip("\n").split("\t")
            for l in open(os.path.join(DATA, "glossary.tsv"), encoding="utf-8")][1:]
    voc = open(os.path.join(SRC, "Vocabulary.lean"), encoding="utf-8").read()
    return {
        "entities": len(rows),
        "properties": sum(1 for r in rows if r[2] == "property"),
        "items": sum(1 for r in rows if r[2] == "item"),
        "articles": sum(1 for r in rows if len(r) > 5 and r[5]),
        "redirects": sum(1 for r in rows if r[0] != r[1]),
        "vocabulary": voc.count("\u27e8``"),
    }


# The layering both posters draw.  One list, so the two images cannot disagree:
# each entry is (title, modules, note).  `layers()` checks that the layering
# covers every module exactly once, and fills the note of the layer that absorbs
# the compiled `Generated/` modules.
LAYERS = [
    ("Foundations and certified engine",
     ["Core", "BabySteps", "BabyStepsProperties", "BabyStepsAlignment", "Reachability",
      "Engine", "FastEval", "Matching", "Semantics"], None),
    ("Class hierarchy and ontology",
     ["Merge", "SelfDescription", "Subsumption", "Stratification", "Concepts", "DisjointUnion",
      "ClassAlgebra", "Alignment", "ItemMerge", "Taxonomy", "UpperOntology", "Examples",
      "Reflection", "Renaming", "MetaFrobenius", "SoftIdentity", "Modules",
      "ModulesExamples", "ModulesCorpus"], None),
    ("Property layer and constraints",
     ["Properties", "PropertyEngine", "PropertyConstraints", "StatementConstraints",
      "TypeProperties", "Schemas", "Paths", "FieldsOfStudy", "ConstraintExceptions"], None),
    ("Data model and serialisation",
     ["Ranks", "Snaks", "Qualifiers", "Quantities", "TimeValues", "Temporal", "Terms", "Sitelinks",
      "ExternalIds", "Provenance", "Lexemes", "Rdf", "GeoValues", "AllowedUnits"], None),
    ("The other hierarchies: parts, kinship, series, taxa",
     ["Mereology", "Kinship", "KinshipDiagnostics", "Parenting", "ParentingDiagnostics",
      "ParentingExamples", "Series", "SeriesChain", "SeriesExamples", "SeriesDiagnostics",
      "Taxa", "TaxaLineage", "TaxaDiagnostics", "TaxaExamples"], None),
    ("Queries, clean-up, defects and diagnostics",
     ["Queries", "Redundancy", "Diagnostics", "Normalize", "Defects", "DefectReport",
      "DefTest", "KbTerms", "ReportFormat", "Reports", "Fixes", "ReportExamples",
      "Gaps", "Worklist", "WorklistExamples"], None),
    ("Grounding every term in Wikidata",
     ["Grounding", "Vocabulary", "Grounded", "MathResonance", "MathCorpus", "RelatedNotions",
      "RelatedCorpus", "TheoryCorpus"], None),
    ("Category theory, topology and type theory of ontologies",
     ["CategoryOfOntologies", "OntologyLimits", "OntologyColimits", "PullbackComparison",
      "PullbackRetraction", "RetractTopology", "OntologyTopology", "OntologyGroups",
      "OntologyFields", "GrothendieckSite", "OntologySheaves", "HomotopyTypes",
      "CubicalTypes"], None),
    ("Programs, periodicity and the spectrum",
     ["RelationWords", "Periodicity", "PeriodicityReport", "SpectrumReport", "FeedbackSets",
      "ProgramAlgebra", "SignedWords", "CyclicAlgebra", "CompilerPipeline"], None),
    ("Enrichment: growing the corpus from its own sources",
     ["Enrichment", "EnrichmentCorpus", "CorpusFrontier", "CorpusRounds", "Cli/Enrich",
      "Cli/EnrichCmd", "Cli/ScanFormat"], None),
    ("Publication: mirrors, peer-to-peer sync and archives",
     ["Publish", "Sync", "Archive", "PublishExamples", "Cli/Publish"], None),
    ("Wikitext: reading and writing the project's own pages",
     ["Wiki/Syntax", "Wiki/Text", "Wiki/Clean", "Wiki/Subst", "Wiki/Template",
      "Wiki/Registry", "Wiki/Generate", "Wiki/Pages", "Cli/WikiCmd"], None),
    ("Command line tool, compiled corpus and demos",
     ["Cli/Codegen", "Cli/Derive", "Cli/Examples", "Cli/Fetch", "Cli/Format", "Cli/Import",
      "Cli/Query", "Cli/ReportCmd", "Cli/SeriesFormat", "Cli/TaxaFormat", "Cli/Tool",
      "Cli/WorklistCmd",
      "CompiledFacts",
      "CorpusEntailment", "Main", "Showcase"], "the compiled modules"),
]

# the last layer also absorbs every compiled module
GENERATED_LAYER = "Command line tool, compiled corpus and demos"


def layers():
    """[(title, modules, note, theorems)], checked to cover each module once.

    `modules` is everything the layer counts; `note` is a phrase standing for the
    modules a chart should not spell out (the compiled ones), or None.
    """
    mods = per_module()
    gen = sorted(m for m in mods if m.startswith("Generated/"))
    out = []
    for title, ms, note in LAYERS:
        ms = list(ms) + (gen if title == GENERATED_LAYER else [])
        unknown = [m for m in ms if m not in mods]
        assert not unknown, f"unknown modules in {title}: {unknown}"
        if title == GENERATED_LAYER:
            note = f"{len(gen)} compiled Generated/ modules"
        out.append((title, ms, note, sum(mods[m]["theorems"] for m in ms)))
    seen = [m for _, ms, _, _ in out for m in ms]
    assert len(seen) == len(set(seen)), "a module appears in two layers"
    missing = sorted(set(mods) - set(seen))
    assert not missing, f"modules missing from the chart: {missing}"
    return out


def cli_commands():
    """the commands the tool documents, read off `docs/CLI.md`."""
    md = open(os.path.join(ROOT, "docs", "CLI.md"), encoding="utf-8").read()
    return re.findall(r"^\| `wikidata ([a-z]+)", md, re.M)


def git_date():
    try:
        return subprocess.check_output(
            ["git", "log", "-1", "--format=%cs"], cwd=ROOT, text=True).strip()
    except Exception:
        return ""


if __name__ == "__main__":
    t, mods = totals()
    print(json.dumps({"totals": t, "modules": mods, "corpus": corpus(),
                      "glossary": glossary(), "commands": cli_commands(),
                      "merge_gain": merge_gain()}, indent=2))

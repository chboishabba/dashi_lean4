#!/usr/bin/env python3
"""Standalone regression for native declaration-name owner discovery.

Run: python scripts/test_openai_math_owner_discovery.py
This tests candidate retrieval only, NOT mathematical sameness or proof kernels.
"""
import importlib.util
import tempfile
from pathlib import Path


HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "corpus_routing", HERE / "build_openai_math_same_object_matrix.py")
routing = importlib.util.module_from_spec(spec)
spec.loader.exec_module(routing)


def main():
    with tempfile.TemporaryDirectory() as temporary:
        root = Path(temporary)
        agda = root / "dashi_agda"
        lean = root / "dashi_lean4"
        (agda / "DASHI" / "Abstract").mkdir(parents=True)
        lean.mkdir()
        agda_owner = agda / "DASHI" / "Abstract" / "Generic.agda"
        lean_owner = lean / "General.lean"
        agda_owner.write_text(
            "module DASHI.Abstract.Generic where\n"
            "zetaNonvanishingWitness : Set\n"
            "zetaNonvanishingWitness = Set\n",
            encoding="utf-8")
        lean_owner.write_text(
            "namespace General\n"
            "private theorem PrimeGapWitness : True := by trivial\n"
            "end General\n",
            encoding="utf-8")
        # Confirm path words alone could not discover either subject.
        assert not (routing.words("DASHI/Abstract/Generic.agda") &
                    {"zeta", "nonvanishing"})
        assert not (routing.words("General.lean") & {"prime", "gap"})
        index = routing.owner_index(agda, lean)
        zeta = routing.proposals(
            index, "ZetaNonvanishing", "ZetaNonvanishing", 4)
        gap = routing.proposals(index, "PrimeGap", "PrimeGap", 4)
        assert any(path == "DASHI/Abstract/Generic.agda"
                   for _, path, _ in zeta), zeta
        assert any(path == "General.lean" for _, path, _ in gap), gap
        assert routing.proposals(index, "ZetaOnly", "ZetaOnly", 4) == []
    print("PASS: Agda and Lean native symbol search finds path-invisible owners")


if __name__ == "__main__":
    main()

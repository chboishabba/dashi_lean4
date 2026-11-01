#!/usr/bin/env python3
"""Synthetic source-integrity audit regression, not a theorem acceptance test."""
import importlib.util
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "openai_source_audit", HERE / "check_openai_math_decl_sources.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def main():
    with tempfile.TemporaryDirectory() as temporary:
        base = Path(temporary)
        catalogue = base / "Catalogue.lean"
        upstream = base / "upstream"
        source = upstream / "lean" / "OAI" / "Example.lean"
        source.parent.mkdir(parents=True)
        source.write_text(
            "namespace OAI.Sample\n"
            "theorem checked_name : True := by trivial\n"
            "end OAI.Sample\n", encoding="utf-8")
        # One source can legitimately support many distinct comparator rows.
        catalogue.write_text(
            "\n".join(
                '  { comparator := "ComparatorChallenges/Synthetic'
                + str(i) + '.json", declaration := '
                + '"OAI.Sample.checked_name", file := "OAI/Example.lean" }'
                for i in range(208)), encoding="utf-8")
        result = mod.inspect(catalogue, upstream)
        assert result["catalogue_rows"] == 208
        assert result["source_identifiers_seen"] == 208
        assert result["source_integrity_blockers"] == 0
        assert all(x["upstream_kernel_acceptance"] == "NOT_CHECKED"
                   and x["same_object_transport"] == "NOT_ESTABLISHED"
                   for x in result["rows"])
        source.write_text("theorem different_name : True := by trivial\n",
                          encoding="utf-8")
        result = mod.inspect(catalogue, upstream)
        assert result["source_integrity_blockers"] == 208
        source.unlink()
        result = mod.inspect(catalogue, upstream)
        assert result["source_integrity_blockers"] == 208
        assert all(x["source_text_status"] == "SOURCE_FILE_MISSING"
                   for x in result["rows"])
    print("PASS: 208-row source drift audit is fail-closed and never kernel")


if __name__ == "__main__":
    main()

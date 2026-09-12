/-
# RunExport — applies the AristotleExporter plugin to this very project

This file *applies* the `AristotleExporter` NotebookLM exporter to the project
itself. When this file is compiled, the `#exportToNotebookLM` command runs and
writes the partitioned, top-down output into `notebook_lm_files/`:

* `notebook_lm_part_*.txt` — the **project partition**: the project's own
  declarations, result-first (the target "crown jewel" first, then the
  lemmas/definitions it rests on).
* `core_library_part_*.txt` — the **core-library frontier**: the boundary
  declarations from Mathlib / Std / the Lean core that the project directly rests
  on. The exporter partitions the dependency graph by each declaration's defining
  module and *stops at this boundary* rather than walking all the way down to the
  foundational axioms, so the heavy core library is grouped away and not
  re-exported in full on every run.

The chosen target, `AristotleExporter.elabExportCmd`, is the user-facing command
elaborator — the "crown jewel" of the project — so the export starts from it and
works backwards through every project declaration it depends on, cutting off at
the core-library frontier.
-/
import RequestProject.AristotleExporter

#exportToNotebookLM AristotleExporter.elabExportCmd into "notebook_lm_files"

/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Wiki.Pages

/-!
# `wikidata wiki` — templates and pages from the shell

```
wikidata wiki templates              the documented templates, as a Markdown table
wikidata wiki pages [--out DIR]      write the imported and generated pages to DIR
wikidata wiki import FILE.wiki       read a page and report what is in it
wikidata wiki expand NAME ARG…       expand a call to a documented template
```

Every command is a thin shell around the verified core:

| command     | verified statement |
|-------------|--------------------|
| `templates` | `Registry.registry_valid` (every documented template is valid) |
| `pages`     | `Pages.wikiProjectOntology.render_eq`, `Pages.upperOntologyIndex_roundTrip`, `Pages.propertyIndex_roundTrip` (what is written reads back as the page it was written from) |
| `import`    | `Wiki.render_parsePage` (a page that is read prints back to the file, character for character) |
| `expand`    | `Template.expand_no_refs` (a call that supplies every parameter leaves no `{{{…}}}` behind), `Template.expandStr_append_named` (undeclared arguments change nothing) |
-/

namespace Wikidata
namespace Cli

open Wikidata.Wiki

/-- `wikidata wiki templates`: the documentation table of the templates used on
`Wikidata:WikiProject Ontology`. -/
def cmdWikiTemplates : IO UInt32 := do
  IO.println Registry.docTable
  return 0

/-- `wikidata wiki pages --out DIR`: write the imported page and the generated
pages. -/
def cmdWikiPages (dir : String) : IO UInt32 := do
  IO.FS.createDirAll dir
  for (file, page) in Pages.allPages do
    let path := dir ++ "/" ++ file
    IO.FS.writeFile path (render page)
    IO.println s!"wrote {path} ({(render page).length} characters, {page.length} nodes)"
  return 0

/-- `wikidata wiki import FILE`: read a page of wikitext and report what is in
it. -/
def cmdWikiImport (file : String) : IO UInt32 := do
  let text ← IO.FS.readFile file
  match parsePage text with
  | none =>
      IO.eprintln s!"{file}: this is not well-formed wikitext"
      return 1
  | some p =>
      IO.println s!"{file}: {p.length} nodes, {text.length} characters"
      IO.println s!"  prints back to the file: {render p == text}"
      IO.println s!"  hygienic: {pageCleanB p}"
      IO.println s!"  only documented templates: {Registry.usesOnlyRegistered p}"
      let calls := (tmplRefsChars text.toList).map (·.trimAscii.toString)
      IO.println s!"  templates called: {String.intercalate ", " calls.dedup}"
      return 0

/-- `wikidata wiki expand NAME ARG…`: expand a call to a documented template. -/
def cmdWikiExpand (name : String) (args : List String) : IO UInt32 := do
  match Registry.registry.find? (fun t => t.name == name) with
  | none =>
      IO.eprintln s!"unknown template `{name}`; try `wikidata wiki templates`"
      return 1
  | some t =>
      let as := args.map fun a =>
        match (splitKey a.toList) with
        | some (k, v) => if k.isEmpty then (⟨none, a⟩ : Arg) else ⟨some (String.ofList k),
            String.ofList v⟩
        | none => ⟨none, a⟩
      IO.println (t.expandStr as)
      return 0

/-- The `wiki` command. -/
def cmdWiki (args : List String) (out : Option String) : IO UInt32 := do
  match args with
  | ["templates"] => cmdWikiTemplates
  | ["pages"] => cmdWikiPages (out.getD "pages")
  | ["import", f] => cmdWikiImport f
  | "expand" :: nm :: rest => cmdWikiExpand nm rest
  | _ =>
      IO.eprintln "usage: wikidata wiki (templates | pages [--out DIR] | import FILE | expand NAME ARG…)"
      return 1

end Cli
end Wikidata

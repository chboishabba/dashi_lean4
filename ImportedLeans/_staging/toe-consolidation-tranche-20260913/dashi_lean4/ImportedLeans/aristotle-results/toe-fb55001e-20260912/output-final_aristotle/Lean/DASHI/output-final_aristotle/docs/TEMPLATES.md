# Wikitext, templates and pages

This part of the development models the *page* layer of Wikidata: the wikitext of
a project page, the templates it calls, and the machinery to import a page from
wikidata.org and to generate new pages from the formalized ontology.

Everything here is checked by Lean.  The table at the bottom of this file is
printed by `wikidata wiki templates`, and every template in it carries a proof
that it is valid.

```
lake build RequestProject.Wiki.Pages     # builds the whole layer
wikidata wiki templates                  # the table below
wikidata wiki pages --out pages          # write the imported and generated pages
wikidata wiki import pages/Wikidata_WikiProject_Ontology.wiki
wikidata wiki expand Q Q5
```

## The files

| file | what it holds |
|---|---|
| `RequestProject/Wiki/Text.lean` | the wikitext syntax tree, the printer, the brace-aware parser, and `render_parsePage`: anything the parser accepts prints back unchanged |
| `RequestProject/Wiki/Clean.lean` | `pageCleanB`, the hygiene check, and `parsePage_render`: a hygienic page prints to wikitext that reads back as the same page |
| `RequestProject/Wiki/Subst.lean` | parameter substitution `substChars`, the references `paramRefsChars` of a piece of wikitext, and the theorems that substitution only depends on the parameters actually referred to and removes every reference it should |
| `RequestProject/Wiki/Template.lean` | `Template`, argument binding, expansion, and `Template.ValidB` — the nine conditions of a valid template — together with one theorem per condition |
| `RequestProject/Wiki/Syntax.lean` | `wiki!`, `template!` and `wikipage!`: wikitext written as wikitext, compiled to Lean |
| `RequestProject/Wiki/Registry.lean` | the eight templates used on `Wikidata:WikiProject Ontology`, each proved valid |
| `RequestProject/Wiki/Generate.lean` | the page generator, and the proof that what it generates is hygienic and therefore round-trips |
| `RequestProject/Wiki/Pages.lean` | the imported page and the generated pages, with their theorems |
| `RequestProject/Cli/WikiCmd.lean` | the `wikidata wiki` command |
| `pages/*.wiki` | the wikitext of the imported page and of the generated pages |

## `template2lean`: the syntax sugar

Wikitext is written as wikitext, in a string, and turned into Lean while the file
is elaborated.

```lean
-- a term: the string is parsed at compile time; wikitext that does not parse is
-- a compile-time error
#check (wiki! "The class {{Q|Q5}} is an {{P|P31}} of {{Q|Q16889133}}." : Page)

-- a command: declares the template *and* proves it valid
template! tDash : "-" doc "Clears floating content."
  param "1" default "both"
  body "<div style=\"clear:{{{1|both}}}; height: 1em\"></div>"

-- a command: declares a page and proves that printing it returns what was written
wikipage! demo := "Hello {{Q|Q5}}."
```

`template!` produces two declarations: `tDash : Template` and
`tDash.valid : tDash.ValidB = true`.  There is no way to declare a template
without the proof, so an invalid template cannot enter the development.

## What "valid" means

`Template.ValidB` is the conjunction of nine decidable conditions.  Each one is
turned into a usable statement by a theorem in `RequestProject/Wiki/Template.lean`:

| condition | theorem |
|---|---|
| the template name carries no markup | `Template.valid_name_clean` |
| the body is hygienic wikitext, so it prints to wikitext that reads back as the body | `Template.valid_body_clean`, `Template.valid_body_roundTrip` |
| every `{{{` in the body opens a reference that is closed | `Template.valid_refs_wellFormed` |
| parameter names carry no markup | `Template.valid_param_names_clean` |
| no parameter is declared twice | `Template.valid_params_nodup` |
| every reference in the body is to a declared parameter | `Template.valid_refs_declared` |
| every declared parameter is really used | `Template.valid_params_used` |
| every reference writes the declared default | `Template.valid_defaults_agree` |
| the template does not call itself | `Template.valid_not_self_recursive` |

Two further theorems say what validity buys, for calls rather than for the
template alone:

* `Template.expand_no_refs` — a call to a valid template that supplies every
  declared parameter (with values that contain no `{`) expands to wikitext with no
  parameter reference left in it;
* `Template.expandStr_append_named` — named arguments whose keys the template does
  not declare cannot change the expansion.

## The page

`Wikidata:WikiProject Ontology` was exported from wikidata.org and is stored in
`pages/Wikidata_WikiProject_Ontology.wiki`.  It is parsed at compile time in
`RequestProject/Wiki/Pages.lean`, and:

* `wikiProjectOntology.render_eq` — printing the parsed page returns the exported
  wikitext, character for character;
* `wikiProjectOntology_clean` and `wikiProjectOntology_reparse` — the page is
  hygienic, so reading its wikitext again gives the same page;
* `wikiProjectOntology_uses_registered` — every template it calls is one of the
  eight documented below.

The generated pages `pages/Upper_ontology_index.wiki` and
`pages/Property_index.wiki` are built by the verified generator from the
formalized upper ontology and from the glossary; `upperOntologyIndex_roundTrip`
and `propertyIndex_roundTrip` say that the wikitext written out reads back as
exactly the page that was generated, whatever the labels contain.

## How faithful are the template bodies?

Each body is the wikitext of the real template on wikidata.org, with three
systematic simplifications, because this model covers wikitext markup and not the
Scribunto/parser-function layer underneath it:

* `<noinclude>…</noinclude>` sections are dropped — they are the documentation of
  the template, not part of what a call expands to;
* where the real page is a redirect (`{{P}}` → `Template:Property`, `{{u}}` →
  `Template:Reply`) the body is the forwarding call the redirect performs;
* a parser-function wrapper whose *name* carries markup — `{{#if:{{{item|…}}}|…}}`
  in `{{Label}}` — is dropped, as are the language table of `{{User Ontology}}`
  and the dynamic template name `{{{{Participants/name|…}}}}` of
  `{{participants}}`, which are replaced by a representative call.

## The templates

<!-- generated by `wikidata wiki templates` -->
| template | parameters | what it does | body |
|---|---|---|---|
| `{{Q}}` | 1=, capitalization= | The label of an item, linked to the item. | `{{label|{{{1|}}}|capitalization={{{capitalization|}}} |show_id=1 |link=wikidata}}` |
| `{{P}}` | 1 | The label of a property, linked to the property; a redirect to Template:Property. | `{{Property|{{{1}}}}}` |
| `{{Cite Q}}` | 1 | A bibliographic citation generated from the item given as the first argument. | `{{#invoke:Cite Q|cite_q|qid={{{1}}}}}{{Scholia|{{{1}}}}}` |
| `{{Label}}` | item={{{1|}}} , 1=, lang={{{2|}}} , 2=, link=-, capitalization=none, show_id= | The label of an entity, in the reader's language when there is one. | `{{#invoke:Wikidata label|getLabel|item={{{item|{{{1|}}} }}}|lang={{{lang|{{{2|}}} }}}|link={{{link|-}}}|capitalization={{{capitalization|none}}}|show_id={{{show_id|}}}}}` |
| `{{User Ontology}}` | lang= | The userbox of WikiProject Ontology. | `{{Userbox|id=WikiProject Ontology|info=This user is a member of WikiProject Ontology.|lang={{{lang|}}}}}` |
| `{{-}}` | 1=both | Clears floating content; the argument says which side to clear. | `<div style="clear:{{{1|both}}}; height: 1em"></div>` |
| `{{participants}}` | 1= | The list of participants of the project named by the first argument. | `{{Participants/modify|{{{1|}}}}}{{Participants/pingproject}}` |
| `{{u}}` | 1 | A link to the user page of the user named by the first argument; a redirect to Template:Reply. | `{{Reply|{{{1}}}}}` |

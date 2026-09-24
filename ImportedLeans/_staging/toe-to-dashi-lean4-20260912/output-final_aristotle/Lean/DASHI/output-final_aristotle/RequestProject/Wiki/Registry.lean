import RequestProject.Wiki.Syntax

/-!
# The templates used on the WikiProject Ontology page

`Wikidata:WikiProject Ontology` calls exactly eight templates:

| template | calls on the page | what it does |
|---|---|---|
| `{{Q}}` | 4 | the label of an item, linked to it |
| `{{P}}` | 2 | the label of a property, linked to it |
| `{{Cite Q}}` | 2 | a bibliographic citation generated from an item |
| `{{Label}}` | 1 | the label of an entity in the reader's language |
| `{{User Ontology}}` | 1 | the userbox of the project |
| `{{-}}` | 1 | clears floating content |
| `{{participants}}` | 1 | the list of participants of a project |
| `{{u}}` | 26 | a link to a user page |

Each of them is declared below with `template!`, which parses the body as wikitext
at compile time and proves `Wikidata.Wiki.Template.ValidB` of the result by
evaluation.  So the eight `…valid` theorems in this file are the promised proof
that the templates of the page are valid, in the precise sense listed in
`RequestProject.Wiki.Template`.

**How faithful are the bodies?**  Each body below is the wikitext of the real
template on wikidata.org, with three systematic simplifications, because the
present model covers wikitext markup and not the Scribunto/parser-function layer
underneath it:

* `<noinclude>…</noinclude>` sections are dropped: they are the documentation of
  the template, not part of what a call expands to;
* where the real page is a redirect (`{{P}}` → `Template:Property`, `{{u}}` →
  `Template:Reply`) the body is written as the forwarding call the redirect
  performs on its first argument;
* a parser-function wrapper whose *name* contains markup — `{{#if:{{{item|…}}}|…}}`
  in `{{Label}}` — is dropped, since a template name that carries markup is
  outside the hygienic fragment of wikitext this development proves things about;
  likewise the language table of `{{User Ontology}}` and the dynamic template name
  `{{{{Participants/name|…}}}}` in `{{participants}}` are replaced by a
  representative call.

`Wikidata.Wiki.Registry.registry` collects the eight, and
`Wikidata.Wiki.Registry.usesOnlyRegistered` is the check — discharged for the real
page in `RequestProject.Wiki.Pages` — that a page calls no other template.
-/

namespace Wikidata
namespace Wiki
namespace Registry

template! tQ : "Q" doc "The label of an item, linked to the item."
  param "1" default ""
  param "capitalization" default ""
  body "{{label|{{{1|}}}|capitalization={{{capitalization|}}} |show_id=1 |link=wikidata}}"

template! tP : "P" doc "The label of a property, linked to the property; a redirect to Template:Property."
  param "1"
  body "{{Property|{{{1}}}}}"

template! tCiteQ : "Cite Q" doc "A bibliographic citation generated from the item given as the first argument."
  param "1"
  body "{{#invoke:Cite Q|cite_q|qid={{{1}}}}}{{Scholia|{{{1}}}}}"

template! tLabel : "Label" doc "The label of an entity, in the reader's language when there is one."
  param "item" default "{{{1|}}} "
  param "1" default ""
  param "lang" default "{{{2|}}} "
  param "2" default ""
  param "link" default "-"
  param "capitalization" default "none"
  param "show_id" default ""
  body "{{#invoke:Wikidata label|getLabel|item={{{item|{{{1|}}} }}}|lang={{{lang|{{{2|}}} }}}|link={{{link|-}}}|capitalization={{{capitalization|none}}}|show_id={{{show_id|}}}}}"

template! tUserOntology : "User Ontology" doc "The userbox of WikiProject Ontology."
  param "lang" default ""
  body "{{Userbox|id=WikiProject Ontology|info=This user is a member of WikiProject Ontology.|lang={{{lang|}}}}}"

template! tDash : "-" doc "Clears floating content; the argument says which side to clear."
  param "1" default "both"
  body "<div style=\"clear:{{{1|both}}}; height: 1em\"></div>"

template! tParticipants : "participants" doc "The list of participants of the project named by the first argument."
  param "1" default ""
  body "{{Participants/modify|{{{1|}}}}}{{Participants/pingproject}}"

template! tU : "u" doc "A link to the user page of the user named by the first argument; a redirect to Template:Reply."
  param "1"
  body "{{Reply|{{{1}}}}}"

/-- **The documented templates**: every template called on
`Wikidata:WikiProject Ontology`. -/
def registry : List Template :=
  [tQ, tP, tCiteQ, tLabel, tUserOntology, tDash, tParticipants, tU]

/-- The names of the documented templates. -/
def registryNames : List String := registry.map Template.name

/-- **Every documented template is valid.** -/
theorem registry_valid : registry.all Template.ValidB = true := by
  simp only [registry, List.all_cons, tQ.valid, tP.valid, tCiteQ.valid, tLabel.valid,
    tUserOntology.valid, tDash.valid, tParticipants.valid, tU.valid, List.all_nil,
    Bool.and_self]

/-- **No template is documented twice.** -/
theorem registryNames_nodup : registryNames.Nodup := by decide

/-- Does this wikitext call only documented templates?  A call may be written with
spaces around the name (`{{Cite Q | Q42 }}`), which MediaWiki trims, so the names
are compared after trimming. -/
def usesOnlyRegisteredChars (cs : List Char) : Bool :=
  (tmplRefsChars cs).all fun n => registryNames.contains n.trimAscii.toString

/-- Does this page call only documented templates? -/
def usesOnlyRegistered (p : Page) : Bool := usesOnlyRegisteredChars (render p).toList

/-! ## The documentation table -/

/-- The declared parameters of a template, as `name` or `name=default`. -/
def paramsText (t : Template) : String :=
  String.intercalate ", " (t.params.map fun p =>
    match p.dflt with
    | none => p.name
    | some d => p.name ++ "=" ++ d)

/-- One row of the documentation table. -/
def docRow (t : Template) : String :=
  "| `{{" ++ t.name ++ "}}` | " ++ paramsText t ++ " | " ++ t.doc ++ " | `" ++
    render t.body ++ "` |"

/-- **The documentation of the templates**, as a Markdown table.  This is what
`wikidata wiki templates` prints and what `docs/TEMPLATES.md` records. -/
def docTable : String :=
  String.intercalate "\n"
    (["| template | parameters | what it does | body |",
      "|---|---|---|---|"] ++ registry.map docRow)

end Registry
end Wiki
end Wikidata

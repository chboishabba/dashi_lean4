/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Wiki.Template

/-!
# `template2lean`: writing wikitext inside Lean

Writing a page or a template body as a list of `Wikidata.Wiki.Node`s by hand is
unreadable.  This file adds three pieces of syntax that let wikitext be written as
wikitext and turned into Lean at compile time.

* `wiki! "…"` is a **term**: the string is parsed by `Wikidata.Wiki.parsePage`
  *while the file is being elaborated*, and the resulting page is spliced in as a
  literal.  Wikitext that does not parse is a compile-time error, so a malformed
  page can never enter the development.  By `Wikidata.Wiki.render_parsePage` the
  page that is spliced in prints back to exactly the string that was written.

* `template! Ident : "Name" doc "…" param "1" default "…" … body "…"` is a
  **command**: it declares the template and, in the same breath, proves it valid.
  The proof obligation `Template.ValidB … = true` is discharged by evaluation, so
  a template that fails any of the nine conditions of
  `Wikidata.Wiki.Template.ValidB` cannot be declared.

* `wikipage! Ident := "…"` declares a page and proves that printing it returns the
  wikitext it was written with.

Every template in `RequestProject.Wiki.Registry` and every page in
`RequestProject.Wiki.Pages` is declared this way.
-/

open Lean Elab Term Command Meta

namespace Wikidata
namespace Wiki

deriving instance Lean.ToExpr for Arg
deriving instance Lean.ToExpr for Node

/-- `wiki! "…"` parses its argument as wikitext at elaboration time and elaborates
to the resulting `Wikidata.Wiki.Page`. -/
syntax (name := wikiStx) "wiki!" str : term

@[term_elab wikiStx]
def elabWiki : TermElab := fun stx _ => do
  match stx with
  | `(wiki! $s:str) =>
      match parsePage s.getString with
      | some p => return Lean.toExpr p
      | none => throwErrorAt s "wiki!: this is not well-formed wikitext"
  | _ => throwUnsupportedSyntax

/-- A declared parameter inside a `template!` command. -/
declare_syntax_cat wikiParamSpec
/-- A mandatory parameter: every reference to it must be written `{{{name}}}`. -/
syntax "param" str : wikiParamSpec
/-- A parameter with a default: every reference must be written
`{{{name|default}}}`. -/
syntax "param" str "default" str : wikiParamSpec

/-- `template! Ident : "Name" doc "…" param … body "…"` declares a template and
proves it valid. -/
syntax (name := templateCmd) "template!" ident ":" str
  "doc" str
  wikiParamSpec*
  "body" str : command

macro_rules
  | `(command| template! $id:ident : $nm:str doc $dc:str $[$ps:wikiParamSpec]* body $bd:str) => do
      let params ← ps.mapM fun p =>
        match p with
        | `(wikiParamSpec| param $n:str) => `(term| (⟨$n, none⟩ : Param))
        | `(wikiParamSpec| param $n:str default $d:str) => `(term| (⟨$n, some $d⟩ : Param))
        | _ => Macro.throwUnsupported
      let validId := mkIdentFrom id (id.getId ++ `valid)
      let decl ← `(command| def $id : Template := ⟨$nm, [$params,*], wiki! $bd, $dc⟩)
      let thm ← `(command| theorem $validId : Template.ValidB $id = true := by native_decide)
      return mkNullNode #[decl, thm]

/-- `wikipage! Ident := "…"` declares a page written as wikitext, and proves that
printing it returns that wikitext. -/
syntax (name := wikipageCmd) "wikipage!" ident ":=" str : command

macro_rules
  | `(command| wikipage! $id:ident := $s:str) => do
      let renderId := mkIdentFrom id (id.getId ++ `render_eq)
      let decl ← `(command| def $id : Page := wiki! $s)
      let thm ← `(command| theorem $renderId : render $id = $s := by native_decide)
      return mkNullNode #[decl, thm]

end Wiki
end Wikidata

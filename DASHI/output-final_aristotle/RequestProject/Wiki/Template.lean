/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Wiki.Subst

/-!
# Templates, and what it means for a template to be valid

A **template** is a named page with declared parameters.  A call `{{name|…}}`
expands to the template body with every parameter reference replaced by the
argument the call supplies (`Wikidata.Wiki.Template.expandStr`).  Arguments are
bound the way MediaWiki binds them: a named argument `k=v` binds `k`, and the
positional arguments bind `1`, `2`, … in order.

`Wikidata.Wiki.Template.ValidB` is a decidable check that a template is
well-formed.  It is a conjunction of nine conditions, each of which is turned into
a usable statement by one of the `valid_…` theorems below:

| condition | theorem |
|---|---|
| the name carries no markup | `Template.valid_name_clean` |
| the body is hygienic wikitext | `Template.valid_body_clean`, `Template.valid_body_roundTrip` |
| every `{{{` opens a real reference | `Template.valid_refs_wellFormed` |
| parameter names carry no markup | `Template.valid_param_names_clean` |
| parameters are declared at most once | `Template.valid_params_nodup` |
| every reference is to a declared parameter | `Template.valid_refs_declared` |
| every declared parameter is used | `Template.valid_params_used` |
| each reference writes the declared default | `Template.valid_defaults_agree` |
| the template does not call itself | `Template.valid_not_self_recursive` |

The two theorems that say what validity *buys* are
`Wikidata.Wiki.Template.expand_no_refs` (a call that supplies every parameter
expands to text with no leftover `{{{…}}}`) and
`Wikidata.Wiki.Template.expandStr_append_named` (arguments the template does not
declare cannot change the expansion).
-/

namespace Wikidata
namespace Wiki

/-! ## Templates -/

/-- A declared template parameter: its name, and the default that every reference
to it must write. -/
structure Param where
  /-- The parameter name; `"1"`, `"2"`, … for positional parameters. -/
  name : String
  /-- The default value, as raw wikitext, or `none` when the parameter is
  mandatory. -/
  dflt : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- A template: a named page with declared parameters and a one-line description. -/
structure Template where
  /-- The page name, without the `Template:` prefix. -/
  name : String
  /-- The declared parameters, in the order they should be supplied. -/
  params : List Param
  /-- The template body. -/
  body : Page
  /-- What the template is for; printed by the documentation generator. -/
  doc : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- Binds the arguments of a call: named arguments bind their key, positional
arguments bind `i`, `i+1`, … in order. -/
def bindFrom : ℕ → List Arg → Binding
  | _, [] => []
  | i, ⟨none, v⟩ :: as => (toString i, v) :: bindFrom (i + 1) as
  | i, ⟨some k, v⟩ :: as => (k, v) :: bindFrom i as

/-- The binding a call installs: positional arguments are numbered from `1`. -/
def bindArgs (args : List Arg) : Binding := bindFrom 1 args

/-- The number of positional arguments in a list of arguments. -/
def positionalCount : List Arg → ℕ
  | [] => 0
  | ⟨none, _⟩ :: as => positionalCount as + 1
  | ⟨some _, _⟩ :: as => positionalCount as

/-- The body of the template, as raw wikitext. -/
def Template.text (t : Template) : List Char := (render t.body).toList

/-- The names of the declared parameters. -/
def Template.declared (t : Template) : List String := t.params.map Param.name

/-- The parameter references occurring in the body. -/
def Template.refs (t : Template) : List (String × Option String) := paramRefsChars t.text

/-- The templates the body calls. -/
def Template.calls (t : Template) : List String := tmplRefsChars t.text

/-- **Expanding a call.**  The body with every parameter reference replaced by the
argument supplied for it. -/
def Template.expandStr (t : Template) (args : List Arg) : String :=
  String.ofList (substChars (bindArgs args) t.text)

/-- The expansion of a call, read back as a page. -/
def Template.expand (t : Template) (args : List Arg) : Option Page :=
  parsePage (t.expandStr args)

/-! ## Validity -/

/-- **A valid template.**  See the module docstring for the nine conditions. -/
def Template.ValidB (t : Template) : Bool :=
  nameCleanB t.name
    && pageCleanB t.body
    && refsWellFormedB t.text
    && t.params.all (fun p => nameCleanB p.name)
    && (t.declared.dedup.length == t.declared.length)
    && t.refs.all (fun r => t.declared.contains r.1)
    && t.declared.all (fun n => t.refs.any (fun r => r.1 == n))
    && t.refs.all (fun r => (t.params.find? (fun p => p.name == r.1)).any (fun p => p.dflt == r.2))
    && !t.calls.contains t.name

section Valid

variable {t : Template} (h : t.ValidB = true)
include h

theorem Template.valid_name_clean : nameCleanB t.name = true := by
  simp only [Template.ValidB, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

theorem Template.valid_body_clean : pageCleanB t.body = true := by
  simp only [Template.ValidB, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.2

theorem Template.valid_refs_wellFormed : refsWellFormedB t.text = true := by
  simp only [Template.ValidB, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.2

theorem Template.valid_param_names_clean : ∀ p ∈ t.params, nameCleanB p.name = true := by
  simp only [Template.ValidB, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1.1.1.1.1.2

theorem Template.valid_params_nodup : t.declared.Nodup := by
  simp only [Template.ValidB, Bool.and_eq_true, beq_iff_eq] at h
  have hlen := h.1.1.1.1.2
  have heq : t.declared.dedup = t.declared := (List.dedup_sublist _).eq_of_length hlen
  exact heq ▸ List.nodup_dedup t.declared

theorem Template.valid_refs_declared : ∀ r ∈ t.refs, r.1 ∈ t.declared := by
  simp only [Template.ValidB, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  have := h.1.1.1.2 r hr
  simpa using this

theorem Template.valid_params_used : ∀ n ∈ t.declared, ∃ r ∈ t.refs, r.1 = n := by
  simp only [Template.ValidB, Bool.and_eq_true, List.all_eq_true] at h
  intro n hn
  have := h.1.1.2 n hn
  simpa using this

theorem Template.valid_defaults_agree :
    ∀ r ∈ t.refs, ∃ p ∈ t.params, p.name = r.1 ∧ p.dflt = r.2 := by
  simp only [Template.ValidB, Bool.and_eq_true, List.all_eq_true] at h
  intro r hr
  have hp := h.1.2 r hr
  rcases hf : t.params.find? (fun p => p.name == r.1) with _ | p
  · rw [hf] at hp; simp at hp
  · rw [hf] at hp
    simp only [Option.any_some, beq_iff_eq] at hp
    refine ⟨p, List.mem_of_find?_eq_some hf, ?_, hp⟩
    have := List.find?_some hf
    simpa using this

theorem Template.valid_not_self_recursive : t.name ∉ t.calls := by
  simp only [Template.ValidB, Bool.and_eq_true, Bool.not_eq_true'] at h
  have := h.2
  simpa using this

/-- A valid template body survives printing: the wikitext of the body parses back
to the body itself. -/
theorem Template.valid_body_roundTrip : parsePage (render t.body) = some t.body :=
  parsePage_render (Template.valid_body_clean h)

end Valid

/-! ## What validity buys -/

theorem toList_expandStr (t : Template) (args : List Arg) :
    (t.expandStr args).toList = substChars (bindArgs args) t.text := by
  rw [Template.expandStr, String.toList_ofList]

/-- **A satisfied call leaves no parameter behind.**  If a call to a valid template
supplies every declared parameter, and the values it supplies contain no `{`, then
the expansion contains no parameter reference. -/
theorem Template.expand_no_refs {t : Template} (h : t.ValidB = true) (args : List Arg)
    (hb : ∀ n ∈ t.declared, ∃ v, lookupBind (bindArgs args) n = some v ∧
      ∀ c ∈ v.toList, c ≠ '{') :
    paramRefsChars (t.expandStr args).toList = [] := by
  rw [toList_expandStr]
  refine paramRefsChars_substChars _ t.text (Template.valid_refs_wellFormed h) ?_
  intro p hp
  exact hb p.1 (Template.valid_refs_declared h p hp)

/-! ### Undeclared arguments are irrelevant -/

theorem bindFrom_append (i : ℕ) (xs ys : List Arg) :
    bindFrom i (xs ++ ys) = bindFrom i xs ++ bindFrom (i + positionalCount xs) ys := by
  induction xs generalizing i with
  | nil => simp [bindFrom, positionalCount]
  | cons a as ih =>
      cases a with
      | mk key value =>
          cases key with
          | none =>
              rw [show i + (positionalCount (⟨none, value⟩ :: as)) = (i + 1) + positionalCount as by
                simp [positionalCount]; omega]
              simp only [List.cons_append, bindFrom, ih, List.cons_append]
          | some k => simp only [List.cons_append, bindFrom, positionalCount, ih]

theorem lookupBind_append (b b' : Binding) (k : String) :
    lookupBind (b ++ b') k = (lookupBind b k).or (lookupBind b' k) := by
  simp only [lookupBind, List.find?_append]
  cases b.find? fun p => p.1 == k <;> simp

/-- A binding built from named arguments whose keys avoid `k` says nothing about
`k`. -/
theorem lookupBind_bindFrom_eq_none {args : List Arg} {k : String} (i : ℕ)
    (h : ∀ a ∈ args, ∃ j, a.key = some j ∧ j ≠ k) : lookupBind (bindFrom i args) k = none := by
  induction args generalizing i with
  | nil => simp [bindFrom, lookupBind]
  | cons a as ih =>
      obtain ⟨j, hj, hjk⟩ := h a (by simp)
      cases a with
      | mk key value =>
          cases key with
          | none => simp at hj
          | some k' =>
              simp only [Option.some.injEq] at hj
              have hk'k : k' ≠ k := by rw [hj]; exact hjk
              simp only [bindFrom, lookupBind, List.find?_cons]
              have hbeq : (k' == k) = false := by simpa using hk'k
              rw [hbeq]
              simpa [lookupBind] using ih i (fun x hx => h x (by simp [hx]))

/-- **Arguments a template does not declare cannot change its expansion.**  Adding
named arguments whose keys are not declared parameters of a valid template leaves
the expansion exactly as it was. -/
theorem Template.expandStr_append_named {t : Template} (h : t.ValidB = true)
    (args extra : List Arg) (hextra : ∀ a ∈ extra, ∃ k, a.key = some k ∧ k ∉ t.declared) :
    t.expandStr (args ++ extra) = t.expandStr args := by
  have hagree : ∀ p ∈ paramRefsChars t.text,
      lookupBind (bindArgs (args ++ extra)) p.1 = lookupBind (bindArgs args) p.1 := by
    intro p hp
    have hdecl : p.1 ∈ t.declared := Template.valid_refs_declared h p hp
    have hnone : lookupBind (bindFrom (1 + positionalCount args) extra) p.1 = none := by
      refine lookupBind_bindFrom_eq_none _ (fun a ha => ?_)
      obtain ⟨k, hk, hkd⟩ := hextra a ha
      exact ⟨k, hk, fun hkp => hkd (hkp ▸ hdecl)⟩
    rw [bindArgs, bindArgs, bindFrom_append, lookupBind_append, hnone]
    cases lookupBind (bindFrom 1 args) p.1 <;> rfl
  rw [Template.expandStr, Template.expandStr, substChars_congr _ _ t.text hagree]

end Wiki
end Wikidata

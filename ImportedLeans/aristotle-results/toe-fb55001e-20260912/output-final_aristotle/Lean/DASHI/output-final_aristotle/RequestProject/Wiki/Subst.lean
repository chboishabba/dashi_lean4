import RequestProject.Wiki.Clean

/-!
# Parameter substitution

A MediaWiki template is a page whose text contains **parameter references**
`{{{key}}}` and `{{{key|default}}}`.  Expanding a call replaces every reference by
the value the call supplies, or by the default when the call supplies nothing.

Because argument values are kept as raw wikitext (see `RequestProject.Wiki.Text`),
substitution is defined once and for all on **characters**: `Wikidata.Wiki.substChars`
walks the text, uses the same brace-aware scanner as the parser to find the end of
each reference, and splices the value in.  Two mirror functions walk the text the
same way:

* `Wikidata.Wiki.paramRefsChars` — the list of references occurring in the text,
  each with the default written at that occurrence (references inside a default are
  reported too);
* `Wikidata.Wiki.refsWellFormedB` — every `{{{` in the text really does open a
  reference that is closed by a matching `}}}`.

Sharing one recursion between the three functions is what makes the theorems in
`RequestProject.Wiki.Template` provable: the case analysis lines up exactly.
-/

namespace Wikidata
namespace Wiki

/-- A binding of parameter names to the raw wikitext supplied for them. -/
abbrev Binding := List (String × String)

/-- The value bound to a parameter name, if any; the first binding wins. -/
def lookupBind (b : Binding) (k : String) : Option String :=
  (b.find? fun p => p.1 == k).map Prod.snd

/-- **Parameter substitution.**  Replaces every reference `{{{k}}}` or `{{{k|d}}}`
in the text by the value bound to `k`; when `k` is unbound the default `d` is used
(and is itself substituted), and a reference with no default is left standing, as
MediaWiki does.  Text that is not a reference is copied unchanged. -/
def substChars (b : Binding) : List Char → List Char
  | [] => []
  | '{' :: '{' :: '{' :: cs =>
      match _h : scanChunk [] cs with
      | some (k, '}' :: '}' :: '}' :: r) =>
          match lookupBind b (String.ofList k) with
          | some v => v.toList ++ substChars b r
          | none => '{' :: '{' :: '{' :: (k ++ '}' :: '}' :: '}' :: substChars b r)
      | some (k, '|' :: r) =>
          match _h2 : scanChunk [] r with
          | some (d, '}' :: '}' :: '}' :: r2) =>
              match lookupBind b (String.ofList k) with
              | some v => v.toList ++ substChars b r2
              | none => substChars b d ++ substChars b r2
          | _ => '{' :: '{' :: '{' :: substChars b cs
      | _ => '{' :: '{' :: '{' :: substChars b cs
  | c :: cs => c :: substChars b cs
termination_by cs => cs.length
decreasing_by
  all_goals
    first
      | (try (have hh := congrArg List.length (scanChunk_append _h); simp at hh)
         try (have hh2 := congrArg List.length (scanChunk_append _h2); simp at hh2)
         simp only [List.length_cons]
         omega)

/-- The parameter references occurring in a piece of wikitext, each paired with the
default written at that occurrence.  References occurring inside a default are
listed as well. -/
def paramRefsChars : List Char → List (String × Option String)
  | [] => []
  | '{' :: '{' :: '{' :: cs =>
      match _h : scanChunk [] cs with
      | some (k, '}' :: '}' :: '}' :: r) => (String.ofList k, none) :: paramRefsChars r
      | some (k, '|' :: r) =>
          match _h2 : scanChunk [] r with
          | some (d, '}' :: '}' :: '}' :: r2) =>
              (String.ofList k, some (String.ofList d)) :: (paramRefsChars d ++ paramRefsChars r2)
          | _ => paramRefsChars cs
      | _ => paramRefsChars cs
  | _ :: cs => paramRefsChars cs
termination_by cs => cs.length
decreasing_by
  all_goals
    first
      | (try (have hh := congrArg List.length (scanChunk_append _h); simp at hh)
         try (have hh2 := congrArg List.length (scanChunk_append _h2); simp at hh2)
         simp only [List.length_cons]
         omega)

/-- Every `{{{` in the text opens a parameter reference that is closed by a
matching `}}}`. -/
def refsWellFormedB : List Char → Bool
  | [] => true
  | '{' :: '{' :: '{' :: cs =>
      match _h : scanChunk [] cs with
      | some (_, '}' :: '}' :: '}' :: r) => refsWellFormedB r
      | some (_, '|' :: r) =>
          match _h2 : scanChunk [] r with
          | some (d, '}' :: '}' :: '}' :: r2) => refsWellFormedB d && refsWellFormedB r2
          | _ => false
      | _ => false
  | _ :: cs => refsWellFormedB cs
termination_by cs => cs.length
decreasing_by
  all_goals
    first
      | (try (have hh := congrArg List.length (scanChunk_append _h); simp at hh)
         try (have hh2 := congrArg List.length (scanChunk_append _h2); simp at hh2)
         simp only [List.length_cons]
         omega)

/-- The template calls occurring in a piece of wikitext, outermost first; the text
inside a call is scanned as well. -/
def tmplRefsChars : List Char → List String
  | [] => []
  | '{' :: '{' :: '{' :: cs => tmplRefsChars cs
  | '{' :: '{' :: cs =>
      match _h : scanChunk [] cs with
      | some (nm, r) => String.ofList nm :: tmplRefsChars r
      | none => tmplRefsChars cs
  | _ :: cs => tmplRefsChars cs
termination_by cs => cs.length
decreasing_by
  all_goals
    first
      | (try (have hh := congrArg List.length (scanChunk_append _h); simp at hh)
         simp only [List.length_cons]
         omega)

/-! ## Reduction lemmas

One lemma per branch of the shared recursion; every proof about substitution goes
through these rather than unfolding the definitions again. -/

section Reductions

variable {b : Binding} {cs k r d r2 : List Char} {v : String}

theorem substChars_nil : substChars b [] = [] := by rw [substChars]

theorem substChars_bound (h : scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r))
    (hv : lookupBind b (String.ofList k) = some v) :
    substChars b ('{' :: '{' :: '{' :: cs) = v.toList ++ substChars b r := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_unbound (h : scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r))
    (hv : lookupBind b (String.ofList k) = none) :
    substChars b ('{' :: '{' :: '{' :: cs) =
      '{' :: '{' :: '{' :: (k ++ '}' :: '}' :: '}' :: substChars b r) := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_dflt_bound (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2))
    (hv : lookupBind b (String.ofList k) = some v) :
    substChars b ('{' :: '{' :: '{' :: cs) = v.toList ++ substChars b r2 := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_dflt_unbound (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2))
    (hv : lookupBind b (String.ofList k) = none) :
    substChars b ('{' :: '{' :: '{' :: cs) = substChars b d ++ substChars b r2 := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_bad_dflt (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : ∀ d r2, scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2) → False) :
    substChars b ('{' :: '{' :: '{' :: cs) = '{' :: '{' :: '{' :: substChars b cs := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_bad (h1 : ∀ k r, scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r) → False)
    (h2 : ∀ k r, scanChunk [] cs = some (k, '|' :: r) → False) :
    substChars b ('{' :: '{' :: '{' :: cs) = '{' :: '{' :: '{' :: substChars b cs := by
  rw [substChars.eq_2]
  split <;> (try split) <;> simp_all

theorem substChars_cons {c : Char} (h : ∀ t, c = '{' → cs = '{' :: '{' :: t → False) :
    substChars b (c :: cs) = c :: substChars b cs :=
  substChars.eq_3 b c cs h

theorem paramRefsChars_nil : paramRefsChars [] = [] := by rw [paramRefsChars]

theorem paramRefsChars_ref (h : scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r)) :
    paramRefsChars ('{' :: '{' :: '{' :: cs) = (String.ofList k, none) :: paramRefsChars r := by
  rw [paramRefsChars.eq_2]
  split <;> (try split) <;> simp_all

theorem paramRefsChars_dflt (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2)) :
    paramRefsChars ('{' :: '{' :: '{' :: cs) =
      (String.ofList k, some (String.ofList d)) :: (paramRefsChars d ++ paramRefsChars r2) := by
  rw [paramRefsChars.eq_2]
  split <;> (try split) <;> simp_all

theorem paramRefsChars_bad_dflt (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : ∀ d r2, scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2) → False) :
    paramRefsChars ('{' :: '{' :: '{' :: cs) = paramRefsChars cs := by
  rw [paramRefsChars.eq_2]
  split <;> (try split) <;> simp_all

theorem paramRefsChars_bad
    (h1 : ∀ k r, scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r) → False)
    (h2 : ∀ k r, scanChunk [] cs = some (k, '|' :: r) → False) :
    paramRefsChars ('{' :: '{' :: '{' :: cs) = paramRefsChars cs := by
  rw [paramRefsChars.eq_2]
  split <;> (try split) <;> simp_all

theorem paramRefsChars_cons {c : Char} (h : ∀ t, c = '{' → cs = '{' :: '{' :: t → False) :
    paramRefsChars (c :: cs) = paramRefsChars cs :=
  paramRefsChars.eq_3 c cs h

theorem refsWellFormedB_nil : refsWellFormedB [] = true := by rw [refsWellFormedB]

theorem refsWellFormedB_ref (h : scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r)) :
    refsWellFormedB ('{' :: '{' :: '{' :: cs) = refsWellFormedB r := by
  rw [refsWellFormedB.eq_2]
  split <;> (try split) <;> simp_all

theorem refsWellFormedB_dflt (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2)) :
    refsWellFormedB ('{' :: '{' :: '{' :: cs) = (refsWellFormedB d && refsWellFormedB r2) := by
  rw [refsWellFormedB.eq_2]
  split <;> (try split) <;> simp_all

theorem refsWellFormedB_bad_dflt (h : scanChunk [] cs = some (k, '|' :: r))
    (h2 : ∀ d r2, scanChunk [] r = some (d, '}' :: '}' :: '}' :: r2) → False) :
    refsWellFormedB ('{' :: '{' :: '{' :: cs) = false := by
  rw [refsWellFormedB.eq_2]
  split <;> (try split) <;> simp_all

theorem refsWellFormedB_bad
    (h1 : ∀ k r, scanChunk [] cs = some (k, '}' :: '}' :: '}' :: r) → False)
    (h2 : ∀ k r, scanChunk [] cs = some (k, '|' :: r) → False) :
    refsWellFormedB ('{' :: '{' :: '{' :: cs) = false := by
  rw [refsWellFormedB.eq_2]
  split <;> (try split) <;> simp_all

theorem refsWellFormedB_cons {c : Char} (h : ∀ t, c = '{' → cs = '{' :: '{' :: t → False) :
    refsWellFormedB (c :: cs) = refsWellFormedB cs :=
  refsWellFormedB.eq_3 c cs h

end Reductions

/-! ## Substitution theorems -/

/-- Text without a `{` carries no parameter reference, so it may be prefixed to any
text without changing the references found. -/
theorem paramRefsChars_plain_append : ∀ (pre : List Char), (∀ c ∈ pre, c ≠ '{') →
    ∀ rest, paramRefsChars (pre ++ rest) = paramRefsChars rest := by
  intro pre
  induction pre with
  | nil => intro _ rest; simp
  | cons c pre ih =>
      intro hpre rest
      have hc : c ≠ '{' := hpre c (by simp)
      rw [List.cons_append, paramRefsChars_cons (fun _ hb _ => hc hb),
        ih (fun x hx => hpre x (by simp [hx])) rest]

/-- **Substitution changes nothing when there is nothing to substitute.** -/
theorem substChars_of_no_refs (b : Binding) : ∀ cs : List Char,
    paramRefsChars cs = [] → substChars b cs = cs := by
  intro cs
  induction cs using substChars.induct b with
  | case1 => intro _; exact substChars_nil
  | case2 cs k r h v hv _ => intro hno; rw [paramRefsChars_ref h] at hno; simp at hno
  | case3 cs k r h hv _ => intro hno; rw [paramRefsChars_ref h] at hno; simp at hno
  | case4 cs k r h d r2 h2 v hv _ => intro hno; rw [paramRefsChars_dflt h h2] at hno; simp at hno
  | case5 cs k r h d r2 h2 hv _ _ => intro hno; rw [paramRefsChars_dflt h h2] at hno; simp at hno
  | case6 cs k r h hbad ih =>
      intro hno
      rw [paramRefsChars_bad_dflt h hbad] at hno
      rw [substChars_bad_dflt h hbad, ih hno]
  | case7 cs h1 h2 ih =>
      intro hno
      rw [paramRefsChars_bad h1 h2] at hno
      rw [substChars_bad h1 h2, ih hno]
  | case8 c cs h ih =>
      intro hno
      rw [paramRefsChars_cons h] at hno
      rw [substChars_cons h, ih hno]

/-- **Only the referenced parameters matter.**  Two bindings that agree on every
parameter the text refers to substitute the same way — in particular, arguments
that the template never mentions cannot change the expansion. -/
theorem substChars_congr (b b' : Binding) : ∀ cs : List Char,
    (∀ p ∈ paramRefsChars cs, lookupBind b p.1 = lookupBind b' p.1) →
    substChars b cs = substChars b' cs := by
  intro cs
  induction cs using substChars.induct b with
  | case1 => intro _; rw [substChars_nil, substChars_nil]
  | case2 cs k r h v hv ih =>
      intro hag
      rw [paramRefsChars_ref h] at hag
      have hk : lookupBind b' (String.ofList k) = some v := by
        have hp := hag (String.ofList k, none) (by simp)
        rw [← hp, hv]
      rw [substChars_bound h hv, substChars_bound h hk,
        ih (fun p hp => hag p (by simp [hp]))]
  | case3 cs k r h hv ih =>
      intro hag
      rw [paramRefsChars_ref h] at hag
      have hk : lookupBind b' (String.ofList k) = none := by
        have hp := hag (String.ofList k, none) (by simp)
        rw [← hp, hv]
      rw [substChars_unbound h hv, substChars_unbound h hk,
        ih (fun p hp => hag p (by simp [hp]))]
  | case4 cs k r h d r2 h2 v hv ih =>
      intro hag
      rw [paramRefsChars_dflt h h2] at hag
      have hk : lookupBind b' (String.ofList k) = some v := by
        have hp := hag (String.ofList k, some (String.ofList d)) (by simp)
        rw [← hp, hv]
      rw [substChars_dflt_bound h h2 hv, substChars_dflt_bound h h2 hk,
        ih (fun p hp => hag p (by simp [hp]))]
  | case5 cs k r h d r2 h2 hv ihd ihr =>
      intro hag
      rw [paramRefsChars_dflt h h2] at hag
      have hk : lookupBind b' (String.ofList k) = none := by
        have hp := hag (String.ofList k, some (String.ofList d)) (by simp)
        rw [← hp, hv]
      rw [substChars_dflt_unbound h h2 hv, substChars_dflt_unbound h h2 hk,
        ihd (fun p hp => hag p (by simp [hp])), ihr (fun p hp => hag p (by simp [hp]))]
  | case6 cs k r h hbad ih =>
      intro hag
      rw [paramRefsChars_bad_dflt h hbad] at hag
      rw [substChars_bad_dflt h hbad, substChars_bad_dflt h hbad, ih hag]
  | case7 cs h1 h2 ih =>
      intro hag
      rw [paramRefsChars_bad h1 h2] at hag
      rw [substChars_bad h1 h2, substChars_bad h1 h2, ih hag]
  | case8 c cs h ih =>
      intro hag
      rw [paramRefsChars_cons h] at hag
      rw [substChars_cons h, substChars_cons h, ih hag]

/-- Substitution cannot create a leading `{` where there was none. -/
theorem substChars_no_lead_brace {b : Binding} {cs : List Char} (h : ∀ t, cs ≠ '{' :: t) :
    ∀ t, substChars b cs ≠ '{' :: t := by
  cases cs with
  | nil => intro t; rw [substChars_nil]; simp
  | cons c rest =>
      have hc : c ≠ '{' := fun hc => h rest (by rw [hc])
      intro t
      rw [substChars_cons (fun _ hb _ => hc hb)]
      simp [hc]

/-- Substitution cannot create a leading `{{` where there was none. -/
theorem substChars_no_lead_brace2 {b : Binding} {cs : List Char}
    (h : ∀ t, cs ≠ '{' :: '{' :: t) : ∀ t, substChars b cs ≠ '{' :: '{' :: t := by
  cases cs with
  | nil => intro t; rw [substChars_nil]; simp
  | cons c rest =>
      by_cases hc : c = '{'
      · subst hc
        have hr : ∀ t, rest ≠ '{' :: t := fun t ht => h t (by rw [ht])
        intro t
        rw [substChars_cons (fun t' _ ht => hr ('{' :: t') ht)]
        simp only [ne_eq, List.cons.injEq, true_and]
        exact substChars_no_lead_brace hr t
      · intro t
        rw [substChars_cons (fun _ hb _ => hc hb)]
        simp [hc]

/-- **Substitution is complete.**  If every `{{{` in the text really opens a
reference, and every parameter referred to is bound to a value that contains no
`{`, then the substituted text has no parameter reference left in it. -/
theorem paramRefsChars_substChars (b : Binding) : ∀ cs : List Char,
    refsWellFormedB cs = true →
    (∀ p ∈ paramRefsChars cs, ∃ v, lookupBind b p.1 = some v ∧ ∀ c ∈ v.toList, c ≠ '{') →
    paramRefsChars (substChars b cs) = [] := by
  intro cs
  induction cs using substChars.induct b with
  | case1 => intro _ _; rw [substChars_nil, paramRefsChars_nil]
  | case2 cs k r h v hv ih =>
      intro hwf hb
      rw [refsWellFormedB_ref h] at hwf
      rw [paramRefsChars_ref h] at hb
      obtain ⟨v', hv', hplain⟩ := hb (String.ofList k, none) (by simp)
      rw [hv] at hv'
      cases Option.some.inj hv'
      rw [substChars_bound h hv, paramRefsChars_plain_append _ hplain,
        ih hwf (fun p hp => hb p (by simp [hp]))]
  | case3 cs k r h hv _ =>
      intro _ hb
      rw [paramRefsChars_ref h] at hb
      obtain ⟨v', hv', _⟩ := hb (String.ofList k, none) (by simp)
      rw [hv] at hv'
      exact absurd hv' (by simp)
  | case4 cs k r h d r2 h2 v hv ih =>
      intro hwf hb
      rw [refsWellFormedB_dflt h h2, Bool.and_eq_true] at hwf
      rw [paramRefsChars_dflt h h2] at hb
      obtain ⟨v', hv', hplain⟩ := hb (String.ofList k, some (String.ofList d)) (by simp)
      rw [hv] at hv'
      cases Option.some.inj hv'
      rw [substChars_dflt_bound h h2 hv, paramRefsChars_plain_append _ hplain,
        ih hwf.2 (fun p hp => hb p (by simp [hp]))]
  | case5 cs k r h d r2 h2 hv _ _ =>
      intro _ hb
      rw [paramRefsChars_dflt h h2] at hb
      obtain ⟨v', hv', _⟩ := hb (String.ofList k, some (String.ofList d)) (by simp)
      rw [hv] at hv'
      exact absurd hv' (by simp)
  | case6 cs k r h hbad _ =>
      intro hwf _
      rw [refsWellFormedB_bad_dflt h hbad] at hwf
      exact absurd hwf (by simp)
  | case7 cs h1 h2 _ =>
      intro hwf _
      rw [refsWellFormedB_bad h1 h2] at hwf
      exact absurd hwf (by simp)
  | case8 c cs h ih =>
      intro hwf hb
      rw [refsWellFormedB_cons h] at hwf
      rw [paramRefsChars_cons h] at hb
      rw [substChars_cons h]
      by_cases hc : c = '{'
      · subst hc
        have h2 : ∀ t, cs ≠ '{' :: '{' :: t := fun t ht => h t rfl ht
        rw [paramRefsChars_cons (fun t _ ht => substChars_no_lead_brace2 h2 t ht)]
        exact ih hwf hb
      · rw [paramRefsChars_cons (fun _ hb' _ => hc hb')]
        exact ih hwf hb

end Wiki
end Wikidata

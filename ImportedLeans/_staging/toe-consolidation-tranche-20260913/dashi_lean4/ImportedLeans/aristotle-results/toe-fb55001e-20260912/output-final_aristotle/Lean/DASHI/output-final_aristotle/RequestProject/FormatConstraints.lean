import RequestProject.Ranks

/-!
# The format constraint and a certified matcher for it

Wikidata's **format constraint** (Q21502404) restricts the *string* values of a
property — typically an external identifier such as `VIAF ID` (P214) — to those
matching a regular expression given by `format as a regular expression` (P1793).
This file gives the constraint a precise meaning and a *certified* decision
procedure: a regular expression is matched by Brzozowski derivatives, and the
executable matcher is proved to agree exactly with the inductive definition of
matching.

* `Wikidata.Format.Pat` is a small regular-expression language — `never`, `eps`, a
  character class `cls`, concatenation, alternation and Kleene star — and
  `Wikidata.Format.Matches` its meaning, defined inductively on strings of
  characters.  Convenience builders are `lit` (a literal string), `plus`, `opt`,
  `rep` (exactly `n` copies) and `upTo` (at most `n` copies), each characterised
  (`matches_lit`, `matches_plus`, `matches_opt`, `matches_upTo_iff`, and
  `matches_rep_iff_replicate` for a single-character body).
* `Wikidata.Format.nullable` decides whether the empty string matches
  (`nullable_iff`), `Wikidata.Format.deriv` is the Brzozowski derivative, proved
  correct by `deriv_matches` (`Matches (deriv c p) s ↔ Matches p (c :: s)`), and
  `Wikidata.Format.matchB` is the resulting matcher, proved correct by
  `matchB_iff`.  A star is decomposed by `star_cons_decomp`, the lemma that makes
  the derivative of a star work.
* `Wikidata.FormatSpec` is the constraint of one property and
  `Wikidata.formatOk` the check of a claim set against a table of them,
  characterised exactly by `formatOk_iff`.  Consequences: conformance is downward
  closed along sublists (`formatOk_sublist`), so it holds of the truthy fragment
  of a conforming base (`formatOk_truthy`); it splits over concatenation
  (`formatOk_append`) and is monotone in the table (`formatOk_sublist_specs`); a
  property mentioned by no constraint is unconstrained (`formatOk_of_no_spec`);
  a pattern that does not match the empty string forbids empty identifiers
  (`ne_empty_of_formatOk`); the `never` pattern forbids string values outright
  (`no_str_of_never`); and only string values are constrained, so item, quantity
  and time values always pass (`FormatSpec.valueOk_of_not_str`).

The worked fragment gives `VIAF ID` (P214) the pattern "a nonzero digit followed
by up to twenty-one digits" and `ISNI` (P213) the pattern "four groups of four
digits separated by spaces".  Well-formed identifiers are accepted; an identifier
with a leading zero, one containing a letter, an empty one and a misgrouped ISNI
are each rejected, and a base whose only offence sits on a deprecated statement is
rejected while its truthy fragment passes.

As elsewhere in this development the identifiers follow Wikidata, but the example
fragment is a stylised excerpt; the theorems about it are statements about that
fragment.
-/

namespace Wikidata

namespace Format

/-! ### Regular expressions -/

/-- A regular expression over characters, in the fragment used by Wikidata's
`format as a regular expression` (P1793) values. -/
inductive Pat where
  /-- Matches no string at all. -/
  | never
  /-- Matches the empty string. -/
  | eps
  /-- Matches a single character from the given class. -/
  | cls (cs : List Char)
  /-- Concatenation. -/
  | cat (p q : Pat)
  /-- Alternation. -/
  | alt (p q : Pat)
  /-- Kleene star. -/
  | star (p : Pat)
deriving DecidableEq, Repr, Inhabited

/-- The strings matched by a pattern.  In the `star` case the body is required to
match a nonempty string, which loses no generality and makes the recursion on the
matched string well founded. -/
inductive Matches : Pat → List Char → Prop
  /-- The empty pattern matches the empty string. -/
  | eps : Matches .eps []
  /-- A character class matches any one of its characters. -/
  | cls {c : Char} {cs : List Char} : c ∈ cs → Matches (.cls cs) [c]
  /-- A concatenation matches a concatenation. -/
  | cat {p q : Pat} {s t : List Char} : Matches p s → Matches q t → Matches (.cat p q) (s ++ t)
  /-- Alternation, left. -/
  | altL {p q : Pat} {s : List Char} : Matches p s → Matches (.alt p q) s
  /-- Alternation, right. -/
  | altR {p q : Pat} {s : List Char} : Matches q s → Matches (.alt p q) s
  /-- A star matches the empty string. -/
  | starNil {p : Pat} : Matches (.star p) []
  /-- A star matches a nonempty body followed by a star. -/
  | starCons {p : Pat} {s t : List Char} :
      Matches p s → s ≠ [] → Matches (.star p) t → Matches (.star p) (s ++ t)

@[simp] theorem not_matches_never (s : List Char) : ¬ Matches .never s := by
  intro h; cases h

theorem matches_eps_iff (s : List Char) : Matches .eps s ↔ s = [] := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact .eps

theorem matches_cls_iff (cs : List Char) (s : List Char) :
    Matches (.cls cs) s ↔ ∃ c ∈ cs, s = [c] := by
  constructor
  · intro h; cases h with | cls hc => exact ⟨_, hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩; exact .cls hc

theorem matches_alt_iff (p q : Pat) (s : List Char) :
    Matches (.alt p q) s ↔ Matches p s ∨ Matches q s := by
  constructor
  · intro h; cases h with
    | altL h => exact Or.inl h
    | altR h => exact Or.inr h
  · rintro (h | h)
    · exact .altL h
    · exact .altR h

theorem matches_cat_iff (p q : Pat) (s : List Char) :
    Matches (.cat p q) s ↔ ∃ u v, s = u ++ v ∧ Matches p u ∧ Matches q v := by
  constructor
  · intro h; cases h with | cat hu hv => exact ⟨_, _, rfl, hu, hv⟩
  · rintro ⟨u, v, rfl, hu, hv⟩; exact .cat hu hv

/-! ### Derived constructors -/

/-- The pattern matching exactly the given string. -/
def lit : List Char → Pat
  | [] => .eps
  | c :: s => .cat (.cls [c]) (lit s)

theorem matches_lit (s t : List Char) : Matches (lit s) t ↔ t = s := by
  induction s generalizing t with
  | nil => simpa [lit] using matches_eps_iff t
  | cons c s ih =>
      simp only [lit, matches_cat_iff, matches_cls_iff]
      constructor
      · rintro ⟨u, v, rfl, ⟨d, hd, rfl⟩, hv⟩
        simp only [List.mem_singleton] at hd
        subst hd
        rw [(ih v).1 hv]
        simp
      · rintro rfl
        exact ⟨[c], s, rfl, ⟨c, by simp, rfl⟩, (ih s).2 rfl⟩

/-- One or more copies. -/
def plus (p : Pat) : Pat := .cat p (.star p)

/-- Zero or one copy. -/
def opt (p : Pat) : Pat := .alt .eps p

theorem matches_plus (p : Pat) (s : List Char) :
    Matches (plus p) s ↔ ∃ u v, s = u ++ v ∧ Matches p u ∧ Matches (.star p) v :=
  matches_cat_iff _ _ _

theorem matches_opt (p : Pat) (s : List Char) :
    Matches (opt p) s ↔ s = [] ∨ Matches p s := by
  rw [opt, matches_alt_iff, matches_eps_iff]

/-- Exactly `n` copies. -/
def rep (p : Pat) : Nat → Pat
  | 0 => .eps
  | n + 1 => .cat p (rep p n)

/-- At most `n` copies. -/
def upTo (p : Pat) : Nat → Pat
  | 0 => .eps
  | n + 1 => .alt .eps (.cat p (upTo p n))

/-- For a single-character body, `rep` matches exactly the strings of `n` copies of
that character. -/
theorem matches_rep_iff_replicate (c : Char) (n : Nat) (s : List Char) :
    Matches (rep (.cls [c]) n) s ↔ s = List.replicate n c := by
  induction n generalizing s with
  | zero => simpa [rep] using matches_eps_iff s
  | succ n ih =>
      simp only [rep, matches_cat_iff, matches_cls_iff, List.replicate_succ]
      constructor
      · rintro ⟨u, v, rfl, ⟨d, hd, rfl⟩, hv⟩
        simp only [List.mem_singleton] at hd
        subst hd
        rw [(ih v).1 hv]
        simp
      · rintro rfl
        exact ⟨[c], List.replicate n c, rfl, ⟨c, by simp, rfl⟩, (ih _).2 rfl⟩

/-- `upTo p n` matches exactly the strings matched by some `rep p k` with `k ≤ n`:
bounded repetition really is repetition at most `n` times. -/
theorem matches_upTo_iff (p : Pat) (n : Nat) (s : List Char) :
    Matches (upTo p n) s ↔ ∃ k, k ≤ n ∧ Matches (rep p k) s := by
  induction n generalizing s with
  | zero =>
      simp only [upTo, matches_eps_iff]
      constructor
      · rintro rfl; exact ⟨0, le_refl 0, Matches.eps⟩
      · rintro ⟨k, hk, hm⟩
        interval_cases k
        simpa [rep] using (matches_eps_iff s).1 hm
  | succ n ih =>
      simp only [upTo, matches_alt_iff, matches_eps_iff, matches_cat_iff]
      constructor
      · rintro (rfl | ⟨u, v, rfl, hu, hv⟩)
        · exact ⟨0, Nat.zero_le _, Matches.eps⟩
        · obtain ⟨k, hk, hm⟩ := (ih v).1 hv
          exact ⟨k + 1, Nat.succ_le_succ hk, (matches_cat_iff _ _ _).2 ⟨u, v, rfl, hu, hm⟩⟩
      · rintro ⟨k, hk, hm⟩
        cases k with
        | zero => exact Or.inl ((matches_eps_iff s).1 hm)
        | succ j =>
            obtain ⟨u, v, rfl, hu, hv⟩ := (matches_cat_iff _ _ _).1 hm
            exact Or.inr ⟨u, v, rfl, hu, (ih v).2 ⟨j, Nat.le_of_succ_le_succ hk, hv⟩⟩

/-! ### Brzozowski derivatives -/

/-- Whether the pattern matches the empty string. -/
def nullable : Pat → Bool
  | .never => false
  | .eps => true
  | .cls _ => false
  | .cat p q => nullable p && nullable q
  | .alt p q => nullable p || nullable q
  | .star _ => true

theorem nullable_iff (p : Pat) : nullable p = true ↔ Matches p [] := by
  induction p with
  | never => simp [nullable]
  | eps => simp [nullable, matches_eps_iff]
  | cls cs => simp [nullable, matches_cls_iff]
  | cat p q ihp ihq =>
      simp only [nullable, Bool.and_eq_true, ihp, ihq, matches_cat_iff]
      constructor
      · rintro ⟨hp, hq⟩; exact ⟨[], [], rfl, hp, hq⟩
      · rintro ⟨u, v, huv, hu, hv⟩
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 huv.symm
        exact ⟨hu, hv⟩
  | alt p q ihp ihq => simp [nullable, ihp, ihq, matches_alt_iff]
  | star p _ => simp [nullable, Matches.starNil]

/-- The Brzozowski derivative of a pattern by a character: the strings `s` matched
by `deriv c p` are exactly those with `c :: s` matched by `p`. -/
def deriv (c : Char) : Pat → Pat
  | .never => .never
  | .eps => .never
  | .cls cs => if c ∈ cs then .eps else .never
  | .cat p q => if nullable p then .alt (.cat (deriv c p) q) (deriv c q) else .cat (deriv c p) q
  | .alt p q => .alt (deriv c p) (deriv c q)
  | .star p => .cat (deriv c p) (.star p)

/-- A star matching a nonempty string splits off a first nonempty piece. -/
theorem star_cons_decomp {p : Pat} {c : Char} {s : List Char} (h : Matches (.star p) (c :: s)) :
    ∃ u v, s = u ++ v ∧ Matches p (c :: u) ∧ Matches (.star p) v := by
  have H : ∀ (q : Pat) (w : List Char), Matches q w → ∀ (p : Pat) (c : Char) (s : List Char),
      q = .star p → w = c :: s →
      ∃ u v, s = u ++ v ∧ Matches p (c :: u) ∧ Matches (.star p) v := by
    intro q w hm
    induction hm with
    | eps => intro p c s hq _; simp at hq
    | cls _ => intro p c s hq _; simp at hq
    | cat _ _ => intro p c s hq _; simp at hq
    | altL _ => intro p c s hq _; simp at hq
    | altR _ => intro p c s hq _; simp at hq
    | starNil => intro p c s _ hw; simp at hw
    | @starCons p' s₁ t h₁ hne h₂ _ _ =>
        intro p c s hq hw
        injection hq with hq'
        subst hq'
        cases s₁ with
        | nil => exact absurd rfl hne
        | cons d u =>
            simp only [List.cons_append, List.cons.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            exact ⟨u, t, rfl, h₁, h₂⟩
  exact H _ _ h p c s rfl rfl

/-- Correctness of the derivative. -/
theorem deriv_matches (c : Char) (p : Pat) (s : List Char) :
    Matches (deriv c p) s ↔ Matches p (c :: s) := by
  induction p generalizing s with
  | never => simp [deriv]
  | eps =>
      simp only [deriv, not_matches_never, false_iff]
      intro h; cases h
  | cls cs =>
      by_cases hc : c ∈ cs
      · simp [deriv, hc, matches_eps_iff, matches_cls_iff]
      · simp only [deriv, hc, if_false, not_matches_never, false_iff]
        intro h
        rw [matches_cls_iff] at h
        obtain ⟨d, hd, he⟩ := h
        simp only [List.cons.injEq] at he
        exact hc (he.1 ▸ hd)
  | cat p q ihp ihq =>
      constructor
      · intro h
        cases hn : nullable p with
        | true =>
            simp only [deriv, hn, if_true, matches_alt_iff, matches_cat_iff] at h
            rcases h with ⟨u, v, rfl, hu, hv⟩ | h
            · exact (matches_cat_iff _ _ _).2 ⟨c :: u, v, rfl, (ihp u).1 hu, hv⟩
            · exact (matches_cat_iff _ _ _).2
                ⟨[], c :: s, rfl, (nullable_iff p).1 hn, (ihq s).1 h⟩
        | false =>
            simp only [deriv, hn, Bool.false_eq_true, if_false, matches_cat_iff] at h
            obtain ⟨u, v, rfl, hu, hv⟩ := h
            exact (matches_cat_iff _ _ _).2 ⟨c :: u, v, rfl, (ihp u).1 hu, hv⟩
      · intro h
        rw [matches_cat_iff] at h
        obtain ⟨u, v, huv, hu, hv⟩ := h
        cases u with
        | nil =>
            have hn : nullable p = true := (nullable_iff p).2 hu
            simp only [List.nil_append] at huv
            subst huv
            simp only [deriv, hn, if_true, matches_alt_iff]
            exact Or.inr ((ihq s).2 hv)
        | cons d u =>
            simp only [List.cons_append, List.cons.injEq] at huv
            obtain ⟨rfl, rfl⟩ := huv
            have hcat : Matches (.cat (deriv c p) q) (u ++ v) :=
              (matches_cat_iff _ _ _).2 ⟨u, v, rfl, (ihp u).2 hu, hv⟩
            cases hn : nullable p with
            | true =>
                simp only [deriv, hn, if_true, matches_alt_iff]
                exact Or.inl hcat
            | false => simpa only [deriv, hn, Bool.false_eq_true, if_false] using hcat
  | alt p q ihp ihq =>
      simp only [deriv, matches_alt_iff, ihp, ihq]
  | star p ihp =>
      constructor
      · intro h
        simp only [deriv, matches_cat_iff] at h
        obtain ⟨u, v, rfl, hu, hv⟩ := h
        have : Matches (.star p) ((c :: u) ++ v) :=
          Matches.starCons ((ihp u).1 hu) (by simp) hv
        simpa using this
      · intro h
        obtain ⟨u, v, rfl, hu, hv⟩ := star_cons_decomp h
        exact (matches_cat_iff _ _ _).2 ⟨u, v, rfl, (ihp u).2 hu, hv⟩

/-- The matcher: differentiate along the string, then ask whether the empty string
is matched. -/
def matchB (p : Pat) : List Char → Bool
  | [] => nullable p
  | c :: s => matchB (deriv c p) s

/-- The matcher decides matching. -/
theorem matchB_iff (p : Pat) (s : List Char) : matchB p s = true ↔ Matches p s := by
  induction s generalizing p with
  | nil => simpa [matchB] using nullable_iff p
  | cons c s ih => rw [matchB, ih, deriv_matches]

instance (p : Pat) (s : List Char) : Decidable (Matches p s) :=
  decidable_of_iff _ (matchB_iff p s)

/-- Matching a `String`. -/
def matchS (p : Pat) (s : String) : Bool := matchB p s.toList

/-! ### Character classes used by the examples -/

/-- The decimal digits. -/
def digits : List Char := ['0', '1', '2', '3', '4', '5', '6', '7', '8', '9']

/-- The nonzero decimal digits. -/
def nonzeroDigits : List Char := ['1', '2', '3', '4', '5', '6', '7', '8', '9']

/-- One decimal digit. -/
def digit : Pat := .cls digits

/-- One nonzero decimal digit. -/
def nonzeroDigit : Pat := .cls nonzeroDigits

end Format

/-! ### The constraint layer -/

/-- A **format constraint** (Q21502404) on one property: the regular expression its
string values must match (`format as a regular expression`, P1793). -/
structure FormatSpec where
  /-- The constrained property. -/
  pid : Pid
  /-- The pattern the string values must match. -/
  pat : Format.Pat
deriving DecidableEq, Repr, Inhabited

namespace FormatSpec

variable (f : FormatSpec)

/-- A value passes when, being a string, it matches the pattern; values of other
datatypes are outside the scope of a format constraint. -/
def valueOk : Value → Bool
  | .str s => Format.matchS f.pat s
  | _ => true

theorem valueOk_iff (v : Value) :
    f.valueOk v = true ↔ ∀ s : String, v = .str s → Format.Matches f.pat s.toList := by
  cases v <;> simp [valueOk, Format.matchS, Format.matchB_iff]

/-- Item, quantity and time values are unconstrained. -/
theorem valueOk_of_not_str {v : Value} (h : ∀ s : String, v ≠ .str s) : f.valueOk v = true := by
  cases v <;> simp_all [valueOk]

/-- A claim passes when it is about another property, or its value passes. -/
def claimOk (c : Claim) : Bool :=
  if c.pid = f.pid then f.valueOk c.value else true

theorem claimOk_iff (c : Claim) :
    f.claimOk c = true ↔
      ∀ s : String, c.pid = f.pid → c.value = .str s → Format.Matches f.pat s.toList := by
  unfold claimOk
  by_cases h : c.pid = f.pid
  · simp [h, valueOk_iff]
  · simp [h]

theorem claimOk_of_pid_ne {c : Claim} (h : c.pid ≠ f.pid) : f.claimOk c = true := by
  simp [claimOk, h]

end FormatSpec

/-- A claim set passes a table of format constraints. -/
def formatOk (specs : List FormatSpec) (cs : Claim.Set) : Bool :=
  cs.all fun c => specs.all fun f => f.claimOk c

theorem formatOk_iff (specs : List FormatSpec) (cs : Claim.Set) :
    formatOk specs cs = true ↔
      ∀ c ∈ cs, ∀ f ∈ specs, ∀ s : String, c.pid = f.pid → c.value = .str s →
        Format.Matches f.pat s.toList := by
  simp [formatOk, List.all_eq_true, FormatSpec.claimOk_iff]

/-- Conformance is downward closed along sublists. -/
theorem formatOk_sublist {specs : List FormatSpec} {cs ds : Claim.Set} (hsub : ds.Sublist cs)
    (h : formatOk specs cs = true) : formatOk specs ds = true := by
  rw [formatOk_iff] at h ⊢
  exact fun c hc => h c (hsub.mem hc)

/-- Filtering by rank can never introduce a format defect. -/
theorem formatOk_truthy {specs : List FormatSpec} {cs : Claim.Set} (h : formatOk specs cs = true) :
    formatOk specs (Claim.truthy cs) = true :=
  formatOk_sublist List.filter_sublist h

/-- Conformance splits over concatenation. -/
theorem formatOk_append (specs : List FormatSpec) (cs ds : Claim.Set) :
    formatOk specs (cs ++ ds) = true ↔ formatOk specs cs = true ∧ formatOk specs ds = true := by
  simp only [formatOk_iff, List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨h1, h2⟩ c (hc | hc)
    · exact h1 c hc
    · exact h2 c hc

/-- Dropping constraints preserves conformance. -/
theorem formatOk_sublist_specs {specs specs' : List FormatSpec} {cs : Claim.Set}
    (hsub : specs'.Sublist specs) (h : formatOk specs cs = true) : formatOk specs' cs = true := by
  rw [formatOk_iff] at h ⊢
  exact fun c hc f hf => h c hc f (hsub.mem hf)

/-- A property mentioned by no constraint of the table is unconstrained. -/
theorem formatOk_of_no_spec {specs : List FormatSpec} {cs : Claim.Set}
    (h : ∀ c ∈ cs, ∀ f ∈ specs, c.pid ≠ f.pid) : formatOk specs cs = true := by
  rw [formatOk_iff]
  intro c hc f hf s hp
  exact absurd hp (h c hc f hf)

/-- A pattern that does not match the empty string forbids empty identifiers. -/
theorem ne_empty_of_formatOk {specs : List FormatSpec} {cs : Claim.Set}
    (h : formatOk specs cs = true) {f : FormatSpec} (hf : f ∈ specs)
    (hn : Format.nullable f.pat = false) {c : Claim} (hc : c ∈ cs) (hp : c.pid = f.pid)
    {s : String} (hv : c.value = .str s) : s ≠ "" := by
  intro hs
  have hm := (formatOk_iff specs cs).1 h c hc f hf s hp hv
  rw [hs] at hm
  simp only [String.toList] at hm
  have : Format.nullable f.pat = true := (Format.nullable_iff f.pat).2 (by simpa using hm)
  simp [this] at hn

/-- A property constrained by the empty pattern has no string values at all. -/
theorem no_str_of_never {specs : List FormatSpec} {cs : Claim.Set}
    (h : formatOk specs cs = true) {f : FormatSpec} (hf : f ∈ specs) (hpat : f.pat = .never)
    {c : Claim} (hc : c ∈ cs) (hp : c.pid = f.pid) : ∀ s : String, c.value ≠ .str s := by
  intro s hv
  have hm := (formatOk_iff specs cs).1 h c hc f hf s hp hv
  rw [hpat] at hm
  exact (Format.not_matches_never _) hm

/-! ### A worked fragment -/

namespace FormatExample

open Format
open RankExample (Q P)

/-- `VIAF ID` (P214): a nonzero digit followed by up to twenty-one further digits.
The example uses a smaller bound, five, to keep the checks small. -/
def viafPat : Pat := .cat nonzeroDigit (upTo digit 5)

/-- `ISNI` (P213): four groups of four digits separated by spaces. -/
def isniPat : Pat :=
  let group := rep digit 4
  let sp := Pat.cls [' ']
  .cat group (.cat sp (.cat group (.cat sp (.cat group (.cat sp group)))))

/-- The format constraints of the fragment. -/
def specs : List FormatSpec :=
  [ { pid := P "P214", pat := viafPat }, { pid := P "P213", pat := isniPat } ]

/-- Douglas Adams (Q42) with his authority-control identifiers.  The VIAF
identifier is truncated to six digits, to stay inside the bound of `viafPat`. -/
def adamsIds : Claim.Set :=
  [ { subject := Q "Q42", pid := P "P214", value := .str "113230" },
    { subject := Q "Q42", pid := P "P213", value := .str "0000 0001 2103 2683" } ]

theorem adamsIds_ok : formatOk specs adamsIds = true := by decide

/-- A VIAF identifier with a leading zero is rejected. -/
theorem leading_zero_rejected :
    formatOk specs [{ subject := Q "Q42", pid := P "P214", value := .str "013230" }] = false := by
  decide

/-- A VIAF identifier containing a letter is rejected. -/
theorem letter_rejected :
    formatOk specs [{ subject := Q "Q42", pid := P "P214", value := .str "1x3230" }] = false := by
  decide

/-- An empty identifier is rejected. -/
theorem empty_rejected :
    formatOk specs [{ subject := Q "Q42", pid := P "P214", value := .str "" }] = false := by
  decide

/-- A misgrouped ISNI is rejected. -/
theorem misgrouped_isni_rejected :
    formatOk specs
      [{ subject := Q "Q42", pid := P "P213", value := .str "000 00001 2103 2683" }] = false := by
  decide

/-- An item-valued statement of a constrained property is outside the scope of the
constraint. -/
theorem item_value_unconstrained :
    formatOk specs [{ subject := Q "Q42", pid := P "P214", value := .item (Q "Q5") }] = true := by
  decide

/-- A statement of an unconstrained property passes. -/
theorem other_property_unconstrained :
    formatOk specs [{ subject := Q "Q42", pid := P "P227", value := .str "!!!" }] = true := by
  decide

/-- A base whose only offence sits on a deprecated statement is rejected, while its
truthy fragment -- what a default query returns -- passes. -/
def withDeprecated : Claim.Set :=
  { subject := Q "Q42", pid := P "P214", value := .str "0bad", rank := .deprecated } ::
    { subject := Q "Q42", pid := P "P214", value := .str "113230", rank := .preferred } :: []

theorem withDeprecated_rejected : formatOk specs withDeprecated = false := by decide

theorem withDeprecated_truthy_ok : formatOk specs (Claim.truthy withDeprecated) = true := by decide

end FormatExample

end Wikidata

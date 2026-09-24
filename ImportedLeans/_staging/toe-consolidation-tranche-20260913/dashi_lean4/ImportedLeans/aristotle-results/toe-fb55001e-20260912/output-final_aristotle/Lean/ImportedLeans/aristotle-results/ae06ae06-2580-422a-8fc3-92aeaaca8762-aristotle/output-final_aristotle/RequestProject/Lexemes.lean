import RequestProject.Engine

/-!
# Lexemes: the lexicographical data of Wikidata

Besides items, Wikidata stores **lexemes**: words of a given language, each with a
`lexical category` (noun, verb, ...), a list of **forms** (each with its
grammatical features — plural, genitive, ...) and a list of **senses**, a sense
being linked to the ontology by `item for this sense` (P5137).

This file formalises that layer and its interaction with the item ontology of
`RequestProject.Engine`.

The results are:

* **forms are addressed by their grammatical features**: if no two forms of a
  lexeme carry the same feature set, the lookup by features returns exactly the
  form with those features (`formByFeatures_eq_some_iff`);
* **senses connect the lexicon to the ontology**: a lexeme *means* a class when one
  of its senses denotes an instance of it, decided by `LexBase.meansB` and
  certified against the abstract `instance of` (`meansB_iff_instanceOf`);
* **translation is meaning-preserving**: a lexeme found by looking up the lexemes
  of another language that denote the same item means everything the original
  means through that item (`meansB_of_mem_translationsOf`);
* **but sharing a sense is not transitive**: a polysemous word links two lexemes
  that have nothing to do with one another, which is exhibited on the classical
  *bank* fragment (`shares_not_transitive`);
* **polysemy is detectable from the ontology**: a lexeme with denotations in two
  disjoint classes necessarily has at least two senses
  (`two_senses_of_disjoint_denotations`).

As elsewhere, the identifiers follow Wikidata but the fragment is a stylised
excerpt.
-/

namespace Wikidata

/-- A grammatical form of a lexeme: its identifier, its written representation and
its grammatical features (items such as `plural`, Q146786). -/
structure Form where
  /-- The identifier of the form, e.g. `"L3354-F2"`. -/
  fid : String
  /-- The written representation of the form. -/
  representation : String
  /-- The grammatical features of the form. -/
  features : List Qid := []
deriving Repr, DecidableEq, Inhabited

/-- A sense of a lexeme, optionally linked to an item by `item for this sense`
(P5137). -/
structure Sense where
  /-- The identifier of the sense, e.g. `"L3354-S1"`. -/
  sid : String
  /-- The item the sense denotes (`item for this sense`, P5137), if recorded. -/
  denotes : Option Qid := none
deriving Repr, DecidableEq, Inhabited

/-- A Wikidata lexeme: a word of a language, in a lexical category, with its forms
and senses. -/
structure Lexeme where
  /-- The identifier of the lexeme, e.g. `"L3354"`. -/
  lid : String
  /-- The lemma (dictionary form) of the lexeme. -/
  lemmaForm : String
  /-- The language of the lexeme, an item (e.g. `English`, Q1860). -/
  language : Qid
  /-- The lexical category of the lexeme, an item (e.g. `noun`, Q1084). -/
  category : Qid
  /-- The forms of the lexeme. -/
  forms : List Form := []
  /-- The senses of the lexeme. -/
  senses : List Sense := []
deriving Repr, DecidableEq, Inhabited

namespace Lexeme

variable (lex : Lexeme)

/-- The forms of the lexeme carrying exactly the given grammatical features. -/
def formsWith (feats : List Qid) : List Form :=
  lex.forms.filter (fun f => f.features.toFinset == feats.toFinset)

/-- Lookup of a form by its grammatical features. -/
def formByFeatures (feats : List Qid) : Option Form := (lex.formsWith feats).head?

/-- No two different forms of the lexeme carry the same grammatical features. -/
def formsDistinctB : Bool :=
  lex.forms.all fun f => lex.forms.all fun g =>
    !(f.features.toFinset == g.features.toFinset) || f == g

/-- The items denoted by the senses of the lexeme. -/
def denotations : List Qid := lex.senses.filterMap Sense.denotes

variable {lex}

theorem mem_formsWith {feats : List Qid} {f : Form} :
    f ∈ lex.formsWith feats ↔ f ∈ lex.forms ∧ f.features.toFinset = feats.toFinset := by
  simp [formsWith, List.mem_filter]

theorem mem_denotations_iff {q : Qid} :
    q ∈ lex.denotations ↔ ∃ s ∈ lex.senses, s.denotes = some q := by
  simp [denotations, List.mem_filterMap]

theorem denotations_length_le : lex.denotations.length ≤ lex.senses.length :=
  List.length_filterMap_le _ _

/-- **Forms are addressed by their features**: when the forms of a lexeme have
pairwise different feature sets, the lookup by features finds exactly the form
carrying them. -/
theorem formByFeatures_eq_some_iff (hd : lex.formsDistinctB = true) {feats : List Qid}
    {f : Form} :
    lex.formByFeatures feats = some f ↔
      f ∈ lex.forms ∧ f.features.toFinset = feats.toFinset := by
  constructor
  · intro h
    exact mem_formsWith.1 (List.mem_of_mem_head? h)
  · rintro ⟨hf, hfeat⟩
    have hmem : f ∈ lex.formsWith feats := mem_formsWith.2 ⟨hf, hfeat⟩
    have hall : ∀ g ∈ lex.formsWith feats, g = f := by
      intro g hg
      obtain ⟨hg1, hg2⟩ := mem_formsWith.1 hg
      simp only [formsDistinctB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        beq_eq_false_iff_ne, beq_iff_eq, ne_eq] at hd
      rcases hd g hg1 f hf with h | h
      · exact absurd (hg2.trans hfeat.symm) h
      · exact h
    rw [formByFeatures]
    rcases hl : lex.formsWith feats with _ | ⟨g, t⟩
    · rw [hl] at hmem; simp at hmem
    · have : g = f := hall g (by rw [hl]; exact List.mem_cons_self ..)
      simp [this]

/-- Two lexemes **share a sense** when some item is denoted by a sense of each. -/
def SharesSense (l m : Lexeme) : Prop := ∃ q, q ∈ l.denotations ∧ q ∈ m.denotations

/-- Sharing a sense is symmetric. -/
theorem sharesSense_symm {l m : Lexeme} (h : SharesSense l m) : SharesSense m l := by
  obtain ⟨q, h1, h2⟩ := h
  exact ⟨q, h2, h1⟩

/-- A lexeme with a denotation shares a sense with itself. -/
theorem sharesSense_refl {l : Lexeme} {q : Qid} (hq : q ∈ l.denotations) :
    SharesSense l l := ⟨q, hq, hq⟩

end Lexeme

/-- A knowledge base together with its lexicographical layer. -/
structure LexBase where
  /-- The item ontology the senses point into. -/
  base : KB
  /-- The lexemes. -/
  lexemes : List Lexeme := []
  /-- The class of lexical categories (`lexical category`, Q22689055 in the
  fragments below): every lexeme's category is expected to be an instance of it. -/
  lexicalCategory : Qid := .wd "Q22689055"
deriving Repr, DecidableEq, Inhabited

namespace LexBase

variable (lb : LexBase)

/-- Lookup of a lexeme by its identifier. -/
def lexemeOf (lid : String) : Option Lexeme := lb.lexemes.find? (fun l => l.lid == lid)

/-- Decides whether a lexeme *means* a class: one of its senses denotes an instance
of it. -/
def meansB (lex : Lexeme) (c : Qid) : Bool :=
  lex.denotations.any (fun q => lb.base.isInstanceOf q c)

/-- The lexemes of a given language having a sense that denotes the given item —
the translations of that meaning into that language. -/
def translationsOf (q : Qid) (lang : Qid) : List Lexeme :=
  lb.lexemes.filter (fun l => (l.language == lang) && (q ∈ l.denotations))

/-- The validator of the lexicographical layer: languages, categories and
denotations are declared items, every category is an instance of `lexical
category`, and the lexeme identifiers are distinct. -/
def lexValid : Bool :=
  lb.base.valid &&
  lb.lexemes.all (fun l =>
    l.language ∈ lb.base.items &&
    lb.base.isInstanceOf l.category lb.lexicalCategory &&
    l.denotations.all (fun q => q ∈ lb.base.items)) &&
  (lb.lexemes.map Lexeme.lid).Nodup

variable {lb}

theorem mem_translationsOf_iff {q lang : Qid} {m : Lexeme} :
    m ∈ lb.translationsOf q lang ↔ m ∈ lb.lexemes ∧ m.language = lang ∧ q ∈ m.denotations := by
  simp [translationsOf, List.mem_filter]

theorem meansB_iff {lex : Lexeme} {c : Qid} :
    lb.meansB lex c = true ↔ ∃ q ∈ lex.denotations, lb.base.isInstanceOf q c = true := by
  simp [meansB, List.any_eq_true]

/-- The meaning relation, certified against the abstract semantics: a lexeme means
a class exactly when one of its senses denotes an item that is an instance of the
class in the sense of `RequestProject.Core`. -/
theorem meansB_iff_instanceOf (hv : lb.base.valid = true) {lex : Lexeme} {c : Qid} :
    lb.meansB lex c = true ↔
      ∃ q ∈ lex.denotations, (lb.base.toOntology hv).InstanceOf q c := by
  rw [meansB_iff]
  exact exists_congr fun q => and_congr_right fun _ => KB.isInstanceOf_iff_instanceOf hv q c

/-- **Translation preserves meaning**: a lexeme of another language reached through
a shared denotation means everything that denotation is an instance of. -/
theorem meansB_of_mem_translationsOf {q lang c : Qid} {m : Lexeme}
    (hm : m ∈ lb.translationsOf q lang) (hq : lb.base.isInstanceOf q c = true) :
    lb.meansB m c = true :=
  meansB_iff.2 ⟨q, (mem_translationsOf_iff.1 hm).2.2, hq⟩

/-- A list containing two different elements has at least two entries. -/
theorem one_lt_length_of_ne {α : Type*} {l : List α} {a b : α} (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : 1 < l.length := by
  match l, ha, hb with
  | x :: y :: t, _, _ => simp
  | [x], ha, hb =>
      simp only [List.mem_singleton] at ha hb
      exact absurd (ha.trans hb.symm) hab

/-- **Polysemy is visible in the ontology**: if two of a lexeme's denotations are
instances of classes declared disjoint, the lexeme has at least two senses. -/
theorem two_senses_of_disjoint_denotations (hv : lb.base.valid = true) {lex : Lexeme}
    {q r c d : Qid} (hq : q ∈ lex.denotations) (hr : r ∈ lex.denotations)
    (hqc : lb.base.isInstanceOf q c = true) (hrd : lb.base.isInstanceOf r d = true)
    (hdisj : lb.base.Disj c d) : 1 < lex.senses.length := by
  have hne : q ≠ r := by
    rintro rfl
    exact (lb.base.toWithDisjointness hv).disjointWith_spec hdisj
      ((KB.isInstanceOf_iff_instanceOf hv q c).1 hqc)
      ((KB.isInstanceOf_iff_instanceOf hv q d).1 hrd)
  exact lt_of_lt_of_le (one_lt_length_of_ne hq hr hne) Lexeme.denotations_length_le

end LexBase

/-! ## A worked fragment: *bank*

The English lexeme *bank* has two senses, denoting a `bank` (Q22687, a financial
institution) and a `river bank` (Q468756, a landform); the two items are instances
of classes declared disjoint.  German has a separate lexeme for each, so *Bank*
and *Ufer* both share a sense with *bank* while sharing none with each other. -/

namespace LexemeExample

open Lexeme LexBase

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- The item layer: the two meanings of *bank*, their disjoint classes, the two
languages and the lexical category `noun`. -/
def items : KB where
  name := "wd-lexemes"
  items := [Q "Q22687", Q "Q468756", Q "Q43229", Q "Q271669",
            Q "Q1860", Q "Q188", Q "Q1084", Q "Q22689055", Q "Q34770", Q "Q35120"]
  levels := [(Q "Q22687", 0), (Q "Q468756", 0), (Q "Q43229", 1), (Q "Q271669", 1),
             (Q "Q1860", 0), (Q "Q188", 0), (Q "Q1084", 1), (Q "Q22689055", 2),
             (Q "Q34770", 1), (Q "Q35120", 1)]
  sub := [(Q "Q43229", Q "Q35120"), (Q "Q271669", Q "Q35120")]
  inst := [(Q "Q22687", Q "Q43229"), (Q "Q468756", Q "Q271669"),
           (Q "Q1860", Q "Q34770"), (Q "Q188", Q "Q34770"),
           (Q "Q1084", Q "Q22689055")]
  disj := [(Q "Q43229", Q "Q271669")]

set_option maxRecDepth 100000 in
theorem items_valid : items.valid = true := by decide

/-- The English lexeme *bank*, with a singular and a plural form and two senses. -/
def bankEn : Lexeme where
  lid := "L3354"
  lemmaForm := "bank"
  language := Q "Q1860"
  category := Q "Q1084"
  forms := [⟨"L3354-F1", "bank", [Q "Q110786"]⟩, ⟨"L3354-F2", "banks", [Q "Q146786"]⟩]
  senses := [⟨"L3354-S1", some (Q "Q22687")⟩, ⟨"L3354-S2", some (Q "Q468756")⟩]

/-- The German lexeme *Bank* — the financial institution only. -/
def bankDe : Lexeme where
  lid := "L1000"
  lemmaForm := "Bank"
  language := Q "Q188"
  category := Q "Q1084"
  senses := [⟨"L1000-S1", some (Q "Q22687")⟩]

/-- The German lexeme *Ufer* — the river bank only. -/
def uferDe : Lexeme where
  lid := "L1001"
  lemmaForm := "Ufer"
  language := Q "Q188"
  category := Q "Q1084"
  senses := [⟨"L1001-S1", some (Q "Q468756")⟩]

/-- The lexicographical layer. -/
def lexicon : LexBase where
  base := items
  lexemes := [bankEn, bankDe, uferDe]
  lexicalCategory := Q "Q22689055"

set_option maxRecDepth 100000 in
theorem lexicon_valid : lexicon.lexValid = true := by decide

set_option maxRecDepth 100000 in
theorem bankEn_formsDistinct : bankEn.formsDistinctB = true := by decide

set_option maxRecDepth 100000 in
/-- The plural form is found by its grammatical feature. -/
theorem plural_form :
    bankEn.formByFeatures [Q "Q146786"] = some ⟨"L3354-F2", "banks", [Q "Q146786"]⟩ := by
  decide

set_option maxRecDepth 100000 in
/-- *bank* means an organisation ... -/
theorem bankEn_means_org : lexicon.meansB bankEn (Q "Q43229") = true := by decide

set_option maxRecDepth 100000 in
/-- ... and also a landform: it is polysemous. -/
theorem bankEn_means_landform : lexicon.meansB bankEn (Q "Q271669") = true := by decide

set_option maxRecDepth 100000 in
theorem bankDe_not_landform : lexicon.meansB bankDe (Q "Q271669") = false := by decide

set_option maxRecDepth 100000 in
/-- The German translation of the financial sense is *Bank*, not *Ufer*. -/
theorem translations_de :
    (lexicon.translationsOf (Q "Q22687") (Q "Q188")).map Lexeme.lemmaForm = ["Bank"] := by decide

/-- The two senses of *bank* denote instances of disjoint classes, so — by the
general theorem — the lexeme must have at least two senses. -/
theorem bankEn_two_senses : 1 < bankEn.senses.length :=
  LexBase.two_senses_of_disjoint_denotations (lb := lexicon) items_valid
    (q := Q "Q22687") (r := Q "Q468756") (c := Q "Q43229") (d := Q "Q271669")
    (by decide) (by decide) (by decide) (by decide) (Or.inl (by decide))

/-- **Sharing a sense is not transitive**: *Bank* shares one with *bank*, and
*bank* with *Ufer*, but *Bank* and *Ufer* share none. -/
theorem shares_not_transitive :
    Lexeme.SharesSense bankDe bankEn ∧ Lexeme.SharesSense bankEn uferDe ∧
      ¬ Lexeme.SharesSense bankDe uferDe := by
  refine ⟨⟨Q "Q22687", by decide, by decide⟩, ⟨Q "Q468756", by decide, by decide⟩, ?_⟩
  rintro ⟨q, h1, h2⟩
  have hbd : bankDe.denotations = [Q "Q22687"] := by decide
  have hud : uferDe.denotations = [Q "Q468756"] := by decide
  rw [hbd, List.mem_singleton] at h1
  rw [hud, List.mem_singleton] at h2
  rw [h1] at h2
  exact absurd h2 (by decide)

end LexemeExample

end Wikidata

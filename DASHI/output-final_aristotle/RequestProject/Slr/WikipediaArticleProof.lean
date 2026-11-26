import Lean

/-!
Source-backed Wikipedia article candidate proof checker for JMD.

This verifies *observations about text*, NOT the events of the world:
* every person/date mention matches the literal Wikipedia source and the
  unchanged SLR trained-spaCy named-entity output;
* every action candidate's predicate/agent/patient row is present in the
  original SLR source-unit dependency graph, with exact token-source spans,
  and actor/patient dependency heads pointing to the same predicate;
* every textual-order edge matches two retained event candidates and
  their source coordinates, without asserting historical temporal order;
* the article text SHA-256 matches both SLR and extraction output;
* neither the producer nor the projection has paid semantic/world authority.

Original Wikidata getter, ontology checker and proof-owner attribution:
meta-introspector/JMD. Existing SLR generic producer: chboishabba/dashi_agda.
The checker does NOT reparse prose or invent an independent NLP ontology.
-/

namespace Wikidata
namespace Slr
namespace ArticleProof

open Lean

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption

private def nat? (j : Json) (key : String) : Option Nat :=
  (j.getObjValAs? Nat key).toOption

private def bool? (j : Json) (key : String) : Option Bool :=
  (j.getObjValAs? Bool key).toOption

private def arr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) key).toOption

private def substring (text : String) (start stop : Nat) : String :=
  String.ofList ((text.toList.drop start).take (stop - start))

/-- Concrete span support is determined by the actual source characters,
    not by the candidate's claimed label, SHA or source reference alone. -/
def spanExact (text : String) (j : Json) : Bool :=
  match nat? j "start_char", nat? j "end_char", str? j "surface" with
  | some start, some stop, some surface =>
      decide (start < stop ∧ stop ≤ text.toList.length) &&
        substring text start stop == surface
  | _, _, _ => false

/-- Proof-bearing carrier: a source-bound string fragment can only be built
    when Lean has an actual equality witness for the specified source slice. -/
structure VerifiedSourceFragment (text : String) where
  start : Nat
  stop : Nat
  surface : String
  bounded : start < stop ∧ stop ≤ text.toList.length
  exact : substring text start stop = surface

def verifySourceFragment? (text : String) (j : Json) :
    Option (VerifiedSourceFragment text) := do
  let start ← nat? j "start_char"
  let stop ← nat? j "end_char"
  let surface ← str? j "surface"
  if hBounded : start < stop ∧ stop ≤ text.toList.length then
    if hExact : substring text start stop = surface then
      some ⟨start, stop, surface, hBounded, hExact⟩
    else none
  else none

theorem verifiedFragmentExact
    {text : String} (f : VerifiedSourceFragment text) :
    substring text f.start f.stop = f.surface :=
  f.exact

/-- The source-text order relation has its ordinary mathematical laws.
    It says NOTHING about narrated/actual event chronology. -/
theorem sourceTextOrderTransitive
    (a b c : Nat) (ab : a < b) (bc : b < c) : a < c :=
  Nat.lt_trans ab bc

private def rawMatchesProjection (text : String) (raw proj : Json) : Bool :=
  match nat? raw "idx", str? raw "text", nat? proj "start_char",
        nat? proj "end_char", str? proj "surface" with
  | some start, some word, some a, some b, some surface =>
      start == a && b == start + word.toList.length &&
      surface == word && spanExact text proj &&
      nat? raw "i" == nat? proj "i" &&
      nat? raw "head_i" == nat? proj "head_i" &&
      str? raw "dep" == str? proj "dep" &&
      str? raw "lemma" == str? proj "lemma" &&
      str? raw "pos" == str? proj "pos"
  | _, _, _, _, _ => false

private def originalToken (text : String) (rows : Array Json) (proj : Json) : Bool :=
  rows.toList.any (fun row => rawMatchesProjection text row proj)

private def roleSupported
    (text : String) (rows : Array Json) (predicate actor : Json)
    (allowed : List String) : Bool :=
  originalToken text rows actor &&
  allowed.contains ((str? actor "dep").getD "") &&
  nat? actor "head_i" == nat? predicate "i"

/-- Complete syntax-role enumeration. An arbitrary subset of the original
    children is NOT sufficient evidence for an 'all actors/patients' query.
    It still certifies grammar only, not resolved semantic participants. -/
private def exactDirectRoleProjection
    (text : String) (rows : Array Json) (predicate : Json)
    (chosen : Array Json) (allowed : List String) : Bool :=
  let expected := rows.filter (fun raw =>
    allowed.contains ((str? raw "dep").getD "") &&
    nat? raw "head_i" == nat? predicate "i")
  expected.size == chosen.size &&
    expected.toList.all (fun raw =>
      chosen.toList.any (fun projected => rawMatchesProjection text raw projected)) &&
    chosen.toList.all (fun projected =>
      roleSupported text rows predicate projected allowed)

/-- The original predicate-selection rule remains an explicit source-facing
    acceptance requirement, not a generated semantic ontology. -/
private def selectedOriginalPredicate (raw : Json) : Bool :=
  str? raw "pos" == some "VERB" &&
  List.contains ["ROOT", "conj", "ccomp", "xcomp", "advcl", "acl", "relcl"]
    ((str? raw "dep").getD "")

private def expectedOriginalPredicateCount (original : Array Json) : Nat :=
  original.foldl (fun acc sentence =>
    acc + (((arr? sentence "dependency_rows").getD #[]).filter
      selectedOriginalPredicate).size) 0

private def projectedPredicateKey (event : Json) : Option (String × Nat) := do
  let candidate ← str? event "slr_claim_candidate_id"
  let predicate ← (event.getObjVal? "predicate").toOption
  let i ← nat? predicate "i"
  pure (candidate, i)

private def originalProperNounCount (original : Array Json) : Nat :=
  original.foldl (fun acc sentence =>
    acc + (((arr? sentence "dependency_rows").getD #[]).filter
      (fun raw => str? raw "pos" == some "PROPN")).size) 0

private def projectedTokenKey (token : Json) : Option (Nat × Nat) := do
  let sentence ← nat? token "sentence_index"
  let i ← nat? token "i"
  pure (sentence, i)

private def yearSpanKey (row : Json) : Option (Nat × Nat) := do
  let start ← nat? row "start_char"
  let stop ← nat? row "end_char"
  pure (start, stop)

private def validateEvent
    (text : String) (original : Array Json) (event : Json) : Bool :=
  match str? event "slr_claim_candidate_id",
        (event.getObjVal? "predicate").toOption,
        arr? event "actors", arr? event "patients",
        nat? event "sentence_index", nat? event "sentence_start",
        nat? event "sentence_end" with
  | some cid, some predicate, some actors, some patients,
    some idx, some a, some b =>
      let found := original.toList.any fun candidate =>
        match arr? candidate "dependency_rows" with
        | none => false
        | some rows =>
            str? candidate "claim_candidate_id" == some cid &&
            nat? candidate "sentence_index" == some idx &&
            nat? candidate "source_span_start" == some a &&
            nat? candidate "source_span_end" == some b &&
            originalToken text rows predicate &&
            str? predicate "pos" == some "VERB" &&
            (["ROOT", "conj", "ccomp", "xcomp", "advcl",
               "acl", "relcl"].contains ((str? predicate "dep").getD "")) &&
            exactDirectRoleProjection text rows predicate actors
              ["nsubj", "csubj", "nsubjpass", "csubjpass", "agent"] &&
            exactDirectRoleProjection text rows predicate patients
              ["dobj", "obj", "iobj", "pobj", "attr", "oprd", "dative"]
      found &&
      decide (a < b ∧ b ≤ text.toList.length) &&
      bool? event "candidate_only" == some true &&
      bool? event "semantic_licence_paid" == some false &&
      bool? event "world_event_occurrence_paid" == some false
  | _, _, _, _, _, _, _ => false

private def validateEntity
    (text : String) (original : Array Json)
    (entity : Json) (labels : List String) : Bool :=
  let label := (str? entity "label_ref").getD ""
  labels.contains label && spanExact text entity &&
    original.toList.any (fun row =>
      str? row "surface" == str? entity "surface" &&
      nat? row "start_char" == nat? entity "start_char" &&
      nat? row "end_char" == nat? entity "end_char" &&
      str? row "label_ref" == str? entity "label_ref" &&
      bool? row "candidate_only" == some true &&
      bool? row "semantic_promotion" == some false)

private def eventStart? (event : Json) : Option Nat := do
  let predicate ← (event.getObjVal? "predicate").toOption
  nat? predicate "start_char"

private def validateTextOrder (events : Array Json) (edge : Json) : Bool :=
  let before := (str? edge "before").getD ""
  let after := (str? edge "after").getD ""
  let lhs := events.toList.find? (fun e =>
    str? e "event_candidate_ref" == some before)
  let rhs := events.toList.find? (fun e =>
    str? e "event_candidate_ref" == some after)
  match lhs, rhs with
  | some a, some b =>
      match eventStart? a, eventStart? b with
      | some x, some y =>
          x == (nat? edge "before_start").getD (y + 1) &&
          y == (nat? edge "after_start").getD (x + 1) &&
          decide (x < y) && str? edge "kind" == some "source-text-order-only"
      | _, _ => false
  | _, _ => false

/-- A raw PROPN tag is a proper-noun TOKEN, not a named person identity.
    The proof reopens the same sentence and parser dependency row. -/
private def validateProperNounToken
    (text : String) (original : Array Json) (token : Json) : Bool :=
  str? token "pos" == some "PROPN" &&
  bool? token "candidate_only" == some true &&
  bool? token "entity_identity_paid" == some false &&
  bool? token "person_type_paid" == some false &&
  original.toList.any (fun candidate =>
    nat? candidate "sentence_index" == nat? token "sentence_index" &&
    match arr? candidate "dependency_rows" with
    | some rows => originalToken text rows token
    | none => false)

/-- Even when NER is absent, a four-digit literal-year substring can
    have a stronger exact-source + ORIGINAL spaCy token witness.
    It remains a date-like lexical observation, NOT an event date. -/
private def validateLexicalYear
    (text : String) (original : Array Json) (row : Json) : Bool :=
  match nat? row "year_candidate", nat? row "start_char",
        nat? row "end_char", nat? row "sentence_index",
        nat? row "parser_token_i", nat? row "parser_token_start",
        nat? row "parser_token_end", str? row "parser_token_surface" with
  | some year, some start, some stop, some idx,
    some tokenI, some tokenStart, some tokenStop, some tokenSurface =>
      decide (1800 ≤ year ∧ year ≤ 2099) &&
      str? row "surface" == some (toString year) &&
      spanExact text row &&
      decide (tokenStart ≤ start ∧ start < stop ∧ stop ≤ tokenStop ∧
              tokenStop ≤ text.toList.length) &&
      substring text tokenStart tokenStop == tokenSurface &&
      str? row "evidence_kind" ==
        some "literal-year-inside-original-parser-token" &&
      bool? row "candidate_only" == some true &&
      bool? row "event_time_paid" == some false &&
      original.toList.any (fun candidate =>
        str? candidate "claim_candidate_id" ==
          str? row "slr_claim_candidate_id" &&
        nat? candidate "sentence_index" == some idx &&
        match arr? candidate "dependency_rows" with
        | some rows => rows.toList.any (fun raw =>
            nat? raw "i" == some tokenI &&
            nat? raw "idx" == some tokenStart &&
            str? raw "text" == some tokenSurface &&
            tokenStop == tokenStart + tokenSurface.toList.length)
        | none => false)
  | _, _, _, _, _, _, _, _ => false

/-- Lexical year index with bounded candidate co-occurrences, not a
    world-level before/after relation or licensed event timestamp. -/
private def validateTimeline
    (text : String) (original events : Array Json) (row : Json) : Bool :=
  validateLexicalYear text original row &&
  str? row "kind" == some "source-year-mention-not-event-date" &&
  match nat? row "sentence_index", arr? row "co_sentential_event_refs" with
  | some idx, some refs =>
      refs.toList.all (fun ref =>
        events.toList.any (fun event =>
          str? event "event_candidate_ref" == ref.getStr?.toOption &&
          nat? event "sentence_index" == some idx))
  | _, _ => false

/-- The full article's paragraphs and headings must cover the exact
    supplied source in order. This is a structural source hierarchy ONLY;
    the semantic sentence-to-paragraph fusion contract remains separate. -/
def articleSectionCoverageExact (text : String) (sections : Array Json) : Bool :=
  Id.run do
    if sections.isEmpty then return false
    let sourceLength := text.toList.length
    let mut expectedStart := 0
    let mut currentHeading := "Lead"
    for block in sections.toList do
      let some start := nat? block "start_char"
        | return false
      let some stop := nat? block "end_char"
        | return false
      let some kind := str? block "kind"
        | return false
      let some heading := str? block "heading"
        | return false
      if start != expectedStart || start >= stop || stop > sourceLength then
        return false
      let fragment := substring text start stop
      if kind == "heading" then
        if heading != fragment then return false
        currentHeading := fragment
      else if kind == "paragraph" then
        if heading != currentHeading then return false
      else
        return false
      if stop < sourceLength && substring text stop (stop + 2) != "\n\n" then
        return false
      expectedStart := stop + 2
    return expectedStart == sourceLength + 2

/-- A source-verification success never implies that an extracted event
    occurred: it certifies the relation to source/parser observations only. -/
def checkProjection (text : String) (source projection : Json) : Bool :=
  match arr? source "pnf_candidates",
        arr? projection "sections",
        arr? projection "event_candidates",
        arr? projection "people_mentions",
        arr? projection "time_mentions",
        arr? projection "proper_noun_tokens",
        arr? projection "literal_year_mentions",
        arr? projection "timeline_candidates",
        arr? projection "text_order_edges" with
  | some original, some sections, some events, some people, some dates,
    some proper, some years, some timeline, some order =>
      let rawNamed := (source.getObjVal? "named_entities").toOption
      let entities := (arr? source "named_entities").getD #[]
      let nerPresent := rawNamed.isSome
      str? source "schema" == some "slr-source-unit-pnf-record-v1" &&
      str? projection "schema" == some "slr-jmd-wikipedia-article-candidates-v1" &&
      str? projection "wikidata_item_qid" == some "Q207" &&
      str? source "source_unit_ref" == str? projection "source_unit_ref" &&
      str? source "revision_ref" == str? projection "source_revision_ref" &&
      bool? projection "ner_observations_present" == some nerPresent &&
      (!nerPresent || (arr? source "named_entities").isSome) &&
      (nerPresent || (people.isEmpty && dates.isEmpty)) &&
      bool? source "candidate_only" == some true &&
      bool? source "semantic_promotion" == some false &&
      bool? source "parser_output_creates_ontology_truth" == some false &&
      bool? source "source_role_creates_claim_truth" == some false &&
      original.toList.all (fun row =>
        bool? row "candidate_only" == some true &&
        bool? row "semantic_promotion" == some false) &&
      bool? projection "source_assertion_is_world_truth" == some false &&
      bool? projection "parser_carries_semantic_licence" == some false &&
      bool? projection "text_order_is_event_chronology" == some false &&
      bool? projection "cross_sentence_identity_paid" == some false &&
      articleSectionCoverageExact text sections &&
      events.size == expectedOriginalPredicateCount original &&
      decide ((events.toList.map projectedPredicateKey).Nodup) &&
      events.toList.all (validateEvent text original) &&
      people.toList.all (fun p => validateEntity text entities p ["PERSON"]) &&
      dates.toList.all (fun d => validateEntity text entities d ["DATE", "TIME"]) &&
      proper.size == originalProperNounCount original &&
      decide ((proper.toList.map projectedTokenKey).Nodup) &&
      proper.toList.all (validateProperNounToken text original) &&
      decide ((years.toList.map yearSpanKey).Nodup) &&
      years.toList.all (validateLexicalYear text original) &&
      timeline.size == years.size &&
      decide ((timeline.toList.map yearSpanKey).Nodup) &&
      years.toList.all (fun year => timeline.toList.any (fun row =>
        yearSpanKey year == yearSpanKey row &&
        nat? year "year_candidate" == nat? row "year_candidate")) &&
      timeline.toList.all (validateTimeline text original events) &&
      order.toList.all (validateTextOrder events)
  | _, _, _, _, _, _, _, _, _ => false

/-- This exact-source certificate is obtained only after checking the
    literal article, SLR original parser rows and projected evidence. -/
structure CheckedArticleExtraction (text : String) (source projection : Json) where
  checked : checkProjection text source projection = true

theorem checkedArticleHasStructuralEvidence
    {text : String} {source projection : Json}
    (receipt : CheckedArticleExtraction text source projection) :
    checkProjection text source projection = true :=
  receipt.checked

/-- A source-observation query, not a world-claim or identity query. The
    results retain the entire original candidate row and exact coordinates.
    Missing NER or lexical candidates never imply absence from the article. -/
inductive ArticleQuery where
  | person (surface : String)
  | properNoun (surface : String)
  | year (surface : String)
  | predicate (lemmaOrSurface : String)
  | negationToken (surface : String)
  deriving Repr

def parseArticleQuery? (kind value : String) : Option ArticleQuery :=
  if value.isEmpty then none else
    match kind with
    | "person" => some (.person value)
    | "proper-noun" => some (.properNoun value)
    | "year" => some (.year value)
    | "predicate" => some (.predicate value)
    | "negation-token" => some (.negationToken value)
    | _ => none

def queryRows (source projection : Json) : ArticleQuery → List Json
  | .person _ => ((arr? projection "people_mentions").getD #[]).toList
  | .properNoun _ => ((arr? projection "proper_noun_tokens").getD #[]).toList
  | .year _ => ((arr? projection "literal_year_mentions").getD #[]).toList
  | .predicate _ => ((arr? projection "event_candidates").getD #[]).toList
  | .negationToken _ => ((arr? source "pnf_candidates").getD #[]).toList

def queryMatches (text : String) (q : ArticleQuery) (row : Json) : Bool :=
  match q with
  | .person value | .properNoun value | .year value =>
    str? row "surface" == some value
  | .predicate value =>
    match (row.getObjVal? "predicate").toOption with
    | some p => str? p "lemma" == some value || str? p "surface" == some value
    | none => false
  | .negationToken value =>
    let tokens := ((arr? row "dependency_rows").getD #[]).toList
    tokens.any (fun token =>
      match nat? token "idx", nat? token "head_i" with
      | some start, some head =>
        str? token "dep" == some "neg" && str? token "text" == some value &&
        decide (start + value.toList.length ≤ text.toList.length) &&
        substring text start (start + value.toList.length) == value &&
        tokens.any (fun parent => nat? parent "i" == some head)
      | _, _ => false)

/-- The original checker is a proof premise, not a claimed JSON flag.
    For negation, retain the whole original sentence/dependency row so the
    negation head and scope are not silently turned into a semantic denial. -/
def queryCheckedArticle
    {text : String} {source projection : Json}
    (_receipt : CheckedArticleExtraction text source projection)
    (q : ArticleQuery) : List Json :=
  (queryRows source projection q).filter (queryMatches text q)

/-- Exact two-way membership over the observed rows, not over all possible
    semantic readings or missing parser observations. -/
theorem queryCheckedArticleExact
    {text : String} {source projection : Json}
    (receipt : CheckedArticleExtraction text source projection)
    (q : ArticleQuery) (row : Json) :
    row ∈ queryCheckedArticle receipt q ↔
      row ∈ queryRows source projection q ∧ queryMatches text q row = true := by
  simp only [queryCheckedArticle, List.mem_filter]

/-- Every returned row belongs to the checked source/projection and matches
    the requested observation. Zero matches means no matching observed row,
    not refutation or evidence that no matching world event exists. -/
theorem checkedArticleQuerySound
    {text : String} {source projection : Json}
    (receipt : CheckedArticleExtraction text source projection)
    (q : ArticleQuery) (row : Json)
    (h : row ∈ queryCheckedArticle receipt q) :
    checkProjection text source projection = true ∧
      row ∈ queryRows source projection q ∧ queryMatches text q row = true :=
  ⟨receipt.checked, (queryCheckedArticleExact receipt q row).mp h⟩

private def hashFile (path : String) : IO String := do
  let output ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  if output.exitCode != 0 then
    throw (IO.userError s!"sha256sum failed: {output.stderr}")
  return (output.stdout.splitOn " ").head!

private def readJson (path : String) : IO Json := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .ok value => return value
  | .error err => throw (IO.userError s!"Invalid evidence JSON ({path}): {err}")

/-- JMD proof run over actual revision-pinned Wikipedia text and original
    SLR PNF rows. This provides a checkable observation claim; the additional
    DASHI SourceQueryLicence still governs semantic or occurrence questions. -/
def verifyFiles
    (articlePath slrRecordPath projectionPath : String)
    (query : Option (String × String) := none) : IO Bool := do
  let text ← IO.FS.readFile articlePath
  let source ← readJson slrRecordPath
  let projection ← readJson projectionPath
  let manifestation ← match (source.getObjVal? "manifestation").toOption with
    | some v => pure v
    | none => throw (IO.userError "SLR manifestation missing")
  let sha ← hashFile articlePath
  if str? manifestation "source_text_sha256" != some sha ||
      str? projection "source_text_sha256" != some sha then
    throw (IO.userError "Source digest mismatch: SLR/projection do not match article")
  if h : checkProjection text source projection = true then
    let receipt : CheckedArticleExtraction text source projection := ⟨h⟩
    let _ := checkedArticleHasStructuralEvidence receipt
    if let some (kind, value) := query then
      let some q := parseArticleQuery? kind value
        | throw (IO.userError "Unsupported or empty article observation query")
      let rows := queryCheckedArticle receipt q
      IO.println (Json.mkObj [
        ("schema", Json.str "jmd-checked-article-observation-query-v1"),
        ("source_sha256", Json.str sha),
        ("source_revision_ref", (projection.getObjVal? "source_revision_ref").toOption.getD Json.null),
        ("kind", Json.str kind), ("value", Json.str value),
        ("rows", Json.arr rows.toArray),
        ("scope", Json.str "original-observed-rows-only"),
        ("semantic_licence_paid", Json.bool false),
        ("world_truth_paid", Json.bool false)]).compress
      return true
    let sections := (arr? projection "sections").getD #[]
    let events := (arr? projection "event_candidates").getD #[]
    let persons := (arr? projection "people_mentions").getD #[]
    let dates := (arr? projection "time_mentions").getD #[]
    let years := (arr? projection "literal_year_mentions").getD #[]
    let proper := (arr? projection "proper_noun_tokens").getD #[]
    let order := (arr? projection "text_order_edges").getD #[]
    let timeline := (arr? projection "timeline_candidates").getD #[]
    IO.println s!"JMD_LEAN_SOURCE_PROOF_OK sha256={sha}"
    IO.println s!"source_blocks={sections.size} (heading/paragraph spans fully covered)"
    IO.println s!"ner_people_mentions={persons.size} proper_noun_tokens={proper.size} event_candidates={events.size} ner_date_mentions={dates.size} literal_year_mentions={years.size} timeline_candidates={timeline.size} text_order_edges={order.size}"
    IO.println "PROVED: exact source spans and original SLR parser-row support; textual ordering only."
    IO.println "OPEN: entity identity, interpretation licence, event occurrence, historical chronology."
    return true
  else
    throw (IO.userError "JMD Lean rejected a forged or unsupported source/PNF projection")

end ArticleProof
end Slr
end Wikidata

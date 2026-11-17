import RequestProject.Slr.WikipediaArticleProof

/-!
Source-bound GWB consumer of REAL SLR Rust candidate fibres and residuals.

The Rust crate sl-semantic-expansion explicitly marks itself experimental.
This verifier never promotes an alternate reading, semantic transport,
reviewed S28 identity or world-event truth. It checks the actual emitted
rows against the *same* 643-sentence original dependency observations,
and checks query-specific missing-axis receipts from production SLR
consumer adequacy. The direct/reference algorithm parity itself remains
an independent Rust execution premise.
-/

namespace Wikidata
namespace Slr
namespace GwbNativeFibre

open Lean

private def str? (j : Json) (key : String) : Option String :=
  (j.getObjValAs? String key).toOption
private def nat? (j : Json) (key : String) : Option Nat :=
  (j.getObjValAs? Nat key).toOption
private def bool? (j : Json) (key : String) : Option Bool :=
  (j.getObjValAs? Bool key).toOption
private def arr? (j : Json) (key : String) : Option (Array Json) :=
  (j.getObjValAs? (Array Json) key).toOption

private def spanPair? (j : Json) : Option (Nat × Nat) := do
  let pair ← arr? j "source_span"
  if pair.size != 2 then none else do
    let a ← (pair[0]!).getNat?.toOption
    let b ← (pair[1]!).getNat?.toOption
    some (a, b)

private def rowAt? (rows : Array Json) (local : Nat) : Option Json :=
  rows[local]?

private def candidateSourceBound (rows : Array Json) (c : Json) : Bool :=
  match nat? c "token_ordinal", spanPair? c, str? c "kind",
        nat? c "source_revision" with
  | some ordinal, some (a, b), some kind, some rev =>
      match rowAt? rows ordinal with
      | none => false
      | some raw =>
          nat? raw "idx" == some a &&
          str? raw "text" |>.isSome &&
          (match str? raw "text" with
           | none => false
           | some surface => b == a + surface.toList.length) &&
          rev == 1385850169 &&
          bool? c "candidate_only" == some true &&
          (if kind == "Role(Actor)" then
            (["nsubj", "nsubjpass", "csubj", "csubjpass"].contains
              ((str? raw "dep").getD ""))
          else if kind == "ReferenceRelation" then
            str? raw "dep" == some "agent"
          else true)
  | _, _, _, _ => false

private def alternativeSourceBound (rows : Array Json) (a : Json) : Bool :=
  match nat? a "token_ordinal", arr? a "alternatives" with
  | some ordinal, some alts =>
      match rowAt? rows ordinal with
      | none => false
      | some raw =>
          (["acl", "relcl", "advcl", "ccomp", "xcomp"].contains
             ((str? raw "dep").getD "")) &&
          alts.toList == [Json.str "Condition", Json.str "Temporal",
                         Json.str "Qualifier"] &&
          bool? a "semantic_admission_paid" == some false
  | _, _ => false

private def residualSourceBound (rows : Array Json) (r : Json) : Bool :=
  match nat? r "token_ordinal", str? r "kind" with
  | some ordinal, some kind =>
      match rowAt? rows ordinal with
      | none => false
      | some raw =>
          bool? r "consumer_closed" == some false &&
          (if kind == "ReferenceAttachmentUnresolved" then
            str? raw "dep" == some "agent"
           else if kind == "ClauseInterpretationAmbiguous" then
            (["acl", "relcl", "advcl", "ccomp", "xcomp"].contains
              ((str? raw "dep").getD ""))
           else if kind == "UnsupportedDependency" then
            !((["nsubj", "nsubjpass", "csubj", "csubjpass",
                "dobj", "obj", "iobj", "neg",
                "acl", "relcl", "advcl", "ccomp", "xcomp", "agent"].contains
                ((str? raw "dep").getD "")))
           else true)
  | _, _ => false

private def observationSourceBound (original : Array Json) (o : Json) : Bool :=
  match nat? o "sentence_index", arr? o "candidates",
        arr? o "alternative_fibres", arr? o "residuals",
        arr? o "projection_failures" with
  | some idx, some candidates, some alternatives, some residuals, some failures =>
      match original.toList.find? (fun c => nat? c "sentence_index" == some idx) with
      | none => false
      | some source =>
          match arr? source "dependency_rows" with
          | none => false
          | some rows =>
              failures.isEmpty &&
              candidates.toList.all (candidateSourceBound rows) &&
              alternatives.toList.all (alternativeSourceBound rows) &&
              residuals.toList.all (residualSourceBound rows) &&
              alternatives.toList.all (fun a =>
                nat? a "sentence_index" == some idx) &&
              residuals.toList.all (fun r =>
                nat? r "sentence_index" == some idx)
  | _, _, _, _, _ => false

private def hasQuery (outcomes : Array Json) (name status : String)
    (mandatoryMissing : List String) : Bool :=
  outcomes.toList.any (fun o =>
    str? o "query_ref" == some name &&
    str? o "disposition" == some status &&
    bool? o "candidate_only" == some true &&
    bool? o "factors_through_formally_proved" == some false &&
    bool? o "creates_semantic_authority" == some false &&
    bool? o "creates_claim_truth" == some false &&
    (match arr? o "missing_axes" with
     | none => false
     | some missing => mandatoryMissing.all (fun axis =>
         missing.toList.contains (Json.str axis))))

/-- The actual Rust alternatives/residuals are source-bound observations.
    The source-only consumers reach operational adequacy while the identity,
    event-date and occurrence questions retain exact missing axes.
    This is NOT a proof of full semantic fibre transport or world truth. -/
def checkRealGwbNativeFibreReceipt (article : String)
    (slr projection receipt : Json) : Bool :=
  let original := (arr? slr "pnf_candidates").getD #[]
  let observations := (arr? receipt "sentence_observations").getD #[]
  let consumers := (receipt.getObjVal? "consumer_adequacy").toOption
  let candidateCount := observations.foldl (fun count row =>
    count + ((arr? row "candidates").getD #[]).size) 0
  let fibreCount := observations.foldl (fun count row =>
    count + ((arr? row "alternative_fibres").getD #[]).size) 0
  let residualCount := observations.foldl (fun count row =>
    count + ((arr? row "residuals").getD #[]).size) 0
  ArticleProof.checkProjection article slr projection &&
  str? receipt "schema" ==
    some "gwb-slr-native-semantic-expansion-observations-v1" &&
  str? receipt "source_revision" == str? slr "revision_ref" &&
  str? receipt "source_text_sha256" ==
    str? projection "source_text_sha256" &&
  str? receipt "engine" == some "sensiblaw-semantic-expansion" &&
  str? receipt "engine_certification" ==
    some "EXPERIMENTAL_CANDIDATE_ONLY_OUTSIDE_CERTIFIED_DIRECT_PATH" &&
  bool? receipt "parser_rerun" == some false &&
  bool? receipt "nlp_model_invoked" == some false &&
  bool? receipt "direct_reference_parity_complete" == some true &&
  bool? receipt "full_production_s28_or_hyperfabric_closure" == some false &&
  bool? receipt "consumer_specific_semantic_licence_paid" == some false &&
  bool? receipt "world_occurrence_paid" == some false &&
  nat? receipt "projection_failures" == some 0 &&
  nat? receipt "source_sentences" == some original.size &&
  nat? receipt "source_tokens" ==
    nat? ((slr.getObjVal? "parser_receipt").toOption.getD Json.null) "token_count" &&
  observations.size == original.size &&
  decide ((observations.toList.map (fun o => nat? o "sentence_index")).Nodup) &&
  observations.toList.all (observationSourceBound original) &&
  nat? receipt "native_candidate_count" == some candidateCount &&
  nat? receipt "alternative_fibre_count" == some fibreCount &&
  nat? receipt "typed_residual_count" == some residualCount &&
  (match consumers with
   | none => false
   | some c =>
       str? c "engine" ==
         some "sensiblaw-legal-runtime::assess_consumer_adequacy" &&
       bool? c "factors_through_kernel_proof_paid" == some false &&
       bool? c "semantic_identity_temporal_and_truth_remain_unpaid" ==
         some true &&
       (match arr? c "runtime_outcomes" with
        | none => false
        | some outs =>
            outs.size == 5 &&
            hasQuery outs "gwb:source:observed-mentions" "Adequate" [] &&
            hasQuery outs "gwb:source:syntactic-role-candidates" "Adequate" [] &&
            hasQuery outs "gwb:person:who-was-agent" "NeedsResearch"
              ["SemanticIdentity"] &&
            hasQuery outs "gwb:event:when" "NeedsResearch"
              ["SemanticIdentity", "Temporal"] &&
            hasQuery outs "gwb:world:occurrence" "NeedsResearch"
              ["SemanticIdentity", "FactualPredicate"]))

structure CheckedRealGwbNativeFibre
    (article : String) (slr projection receipt : Json) where
  checked : checkRealGwbNativeFibreReceipt article slr projection receipt = true

theorem checkedGwbFibreObservationsRetainResiduals
    {article : String} {slr projection receipt : Json}
    (e : CheckedRealGwbNativeFibre article slr projection receipt) :
    checkRealGwbNativeFibreReceipt article slr projection receipt = true :=
  e.checked

end GwbNativeFibre
end Slr
end Wikidata

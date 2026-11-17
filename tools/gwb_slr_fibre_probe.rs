//! Read-only SLR Rust semantic-expansion replay of original GWB parser evidence.
//!
//! NO parser, no identity resolver, no admission or source-truth promotion.
//! This invokes SLR's existing sl-semantic-expansion reference + direct
//! projectors on the identical saved token graph and records actual alternatives
//! and residuals. That SLR crate is experimental, not the DB-native certified
//! semantic runtime: never label this output a reviewed GWB semantic fibre.
//!
//! Usage: gwb_slr_fibre_probe ARTICLE.txt SLR-RECORD.json OUTPUT.json
use std::collections::BTreeMap;
use std::env;
use std::fs;

use sensiblaw_core::{Annotation, Capability, HeadDeclaration, TextSpan, TokenObservation};
use sensiblaw_semantic_expansion::{
    check_expanded_parity, ExpandedConsumerObservation, ExpansionSignal,
};
use sensiblaw_legal_runtime::{
    assess_consumer_adequacy, ConsumerAxis, ConsumerCoverage, ConsumerQueryDemand,
    ProjectionGraph, ProjectionKind,
};
use std::collections::BTreeSet;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};

const REVISION: &str = "enwiki-revid:1385850169";
const SOURCE_SHA: &str =
    "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233";

fn require(condition: bool, why: &str) -> Result<(), String> {
    if condition { Ok(()) } else { Err(why.to_owned()) }
}

fn string<'a>(v: &'a Value, key: &str) -> Result<&'a str, String> {
    v.get(key).and_then(Value::as_str)
        .ok_or_else(|| format!("missing string {key}"))
}
fn number(v: &Value, key: &str) -> Result<u64, String> {
    v.get(key).and_then(Value::as_u64)
        .ok_or_else(|| format!("missing nonnegative integer {key}"))
}
fn array<'a>(v: &'a Value, key: &str) -> Result<&'a [Value], String> {
    v.get(key).and_then(Value::as_array).map(Vec::as_slice)
        .ok_or_else(|| format!("missing array {key}"))
}
fn text_sha(text: &str) -> String { format!("{:x}", Sha256::digest(text.as_bytes())) }

struct Interner {
    next: u32,
    ids: BTreeMap<String, u32>,
}
impl Interner {
    fn new() -> Self { Self { next: 1, ids: BTreeMap::new() } }
    fn id(&mut self, family: &str, text: &str) -> Result<u32, String> {
        let key = format!("{family}\u{0}{text}");
        if let Some(id) = self.ids.get(&key) { return Ok(*id); }
        let id = self.next;
        self.next = self.next.checked_add(1).ok_or("symbol table overflow")?;
        self.ids.insert(key, id);
        Ok(id)
    }
}

fn classify(dep: &str, tag: &str, surface: &str) -> ExpansionSignal {
    match dep {
        "nsubj" | "nsubjpass" | "csubj" | "csubjpass" =>
            ExpansionSignal::NominalSubject,
        "dobj" | "obj" | "iobj" =>
            ExpansionSignal::DirectObject,
        "neg" => ExpansionSignal::Negation,
        // An auxiliary is not necessarily a modal verb.
        "aux" if tag == "MD" => ExpansionSignal::ModalAuxiliary,
        // An adverbial temporal adjunct is still only a *candidate* anchor.
        "npadvmod" => ExpansionSignal::TemporalModifier,
        "mark" if matches!(surface.to_ascii_lowercase().as_str(),
                            "if" | "unless" | "provided" | "whether") =>
            ExpansionSignal::ConditionalMarker,
        "acl" | "relcl" | "advcl" | "ccomp" | "xcomp" =>
            ExpansionSignal::ClausalModifier,
        "agent" => ExpansionSignal::ReferenceAttachment,
        "prep" => ExpansionSignal::QualifierAttachment,
        // In particular CONJ is not interpreted as independent assertion.
        // Its dependency parent remains in the original source graph.
        _ => ExpansionSignal::Unsupported,
    }
}

fn spans(text: &str) -> Vec<usize> {
    let mut starts: Vec<usize> = text.char_indices().map(|(byte, _)| byte).collect();
    starts.push(text.len());
    starts
}

fn slice<'a>(text: &'a str, starts: &[usize], a: u64, b: u64)
    -> Result<&'a str, String> {
    let a = usize::try_from(a).map_err(|_| "span overflow")?;
    let b = usize::try_from(b).map_err(|_| "span overflow")?;
    require(a < b && b < starts.len(), "out of bounds source span")?;
    Ok(&text[starts[a]..starts[b]])
}

fn receipt_json(observation: &ExpandedConsumerObservation) -> Value {
    json!({
        "sentence_index": observation.sentence_id,
        "candidates": observation.candidates.iter().map(|c| json!({
            "kind": format!("{:?}", c.kind),
            "source_span": [c.span.start_char, c.span.end_char],
            "source_revision": c.span.revision_id,
            "token_ordinal": c.address.local_ordinal,
            "head": format!("{:?}", c.head),
            "scope": format!("{:?}", c.scope),
            "candidate_only": c.candidate_only
        })).collect::<Vec<_>>(),
        "alternative_fibres": observation.alternative_fibres.iter().map(|f| json!({
            "sentence_index": f.address.sentence_id,
            "token_ordinal": f.address.local_ordinal,
            "alternatives": f.alternatives.iter().map(|x| format!("{x:?}")).collect::<Vec<_>>(),
            "semantic_admission_paid": false
        })).collect::<Vec<_>>(),
        "residuals": observation.residuals.iter().map(|r| json!({
            "sentence_index": r.address.sentence_id,
            "token_ordinal": r.address.local_ordinal,
            "kind": format!("{:?}", r.kind),
            "consumer_closed": false
        })).collect::<Vec<_>>(),
        "projection_failures": observation.projection_failures.iter()
            .map(|err| format!("{err:?}")).collect::<Vec<_>>()
    })
}

/// Existing SLR production consumer adequacy runtime, not an invented
/// consumer-label heuristic. Coverage is limited to independently checked
/// revision/character-span provenance. No semantic identity, temporal or
/// factual coordinate is paid by a candidate-only parser/expansion.
fn consumer_receipts(source_sha: &str) -> Result<Value, String> {
    let graph = ProjectionGraph {
        kind: ProjectionKind::IssueProof,
        nodes: vec![],
        edges: vec![],
        deterministic_digest: format!("sha256:{source_sha}"),
        projection_only: true,
        creates_semantic_authority: false,
    };
    let observed = BTreeSet::from([
        ConsumerAxis::SourceRevision,
        ConsumerAxis::SourceSpan,
        ConsumerAxis::Provenance,
    ]);
    let coverage = ConsumerCoverage {
        paid_axes: observed.clone(),
        closed_unresolved_axes: BTreeSet::new(),
        unresolved_refs: BTreeSet::new(),
    };
    let query_definitions = [
        ("gwb:source:observed-mentions", observed.clone()),
        ("gwb:source:syntactic-role-candidates", observed.clone()),
        ("gwb:person:who-was-agent",
            observed.iter().copied().chain([ConsumerAxis::SemanticIdentity]).collect()),
        ("gwb:event:when",
            observed.iter().copied().chain([
                ConsumerAxis::SemanticIdentity, ConsumerAxis::Temporal]).collect()),
        ("gwb:world:occurrence",
            observed.iter().copied().chain([
                ConsumerAxis::SemanticIdentity,
                ConsumerAxis::FactualPredicate]).collect()),
    ];
    let mut outcomes = Vec::new();
    for (name, axes) in query_definitions {
        let demand = ConsumerQueryDemand {
            query_ref: name.to_owned(),
            required_axes: axes,
            required_semantic_refs: BTreeSet::new(),
            candidate_only: true,
            creates_semantic_authority: false,
        };
        let result = assess_consumer_adequacy(&demand, &graph, &coverage)?;
        require(!result.factors_through_formally_proved &&
                !result.creates_semantic_authority &&
                !result.creates_claim_truth,
                "SLR candidate-only consumer falsely claims semantic theorem/truth")?;
        outcomes.push(serde_json::to_value(result).map_err(|e| e.to_string())?);
    }
    Ok(json!({
        "engine": "sensiblaw-legal-runtime::assess_consumer_adequacy",
        "real_input_revision_sha256": source_sha,
        "runtime_outcomes": outcomes,
        "factors_through_kernel_proof_paid": false,
        "semantic_identity_temporal_and_truth_remain_unpaid": true
    }))
}

fn run(article: &str, record: &Value) -> Result<Value, String> {
    require(string(record, "revision_ref")? == REVISION, "wrong article revision")?;
    require(text_sha(article) == SOURCE_SHA, "original source raw UTF-8 SHA mismatch")?;
    require(string(&record["manifestation"], "source_text_sha256")? == SOURCE_SHA,
            "original parser record source hash mismatch")?;
    require(record["candidate_only"] == true && record["semantic_promotion"] == false,
            "original parser record promotes semantic authority")?;
    require(record["parser_receipt"]["dependency_capable"] == true,
            "not an original dependency-capable parser")?;
    let offsets = spans(article);
    let mut interner = Interner::new();
    let mut observations = Vec::new();
    let mut parity_sentences = 0usize;
    let mut actual_tokens = 0usize;
    let mut actual_candidates = 0usize;
    let mut actual_alternatives = 0usize;
    let mut actual_residuals = 0usize;
    let mut kinds: BTreeMap<String, usize> = BTreeMap::new();
    let mut sample_witnesses = Vec::new();
    let original = array(record, "pnf_candidates")?;
    for sentence in original {
        let sentence_id = number(sentence, "sentence_index")?;
        let start = number(sentence, "source_span_start")?;
        let end = number(sentence, "source_span_end")?;
        let exact_sentence = slice(article, &offsets, start, end)?;
        require(text_sha(exact_sentence) ==
                string(sentence, "sentence_text_sha256")?,
                "original sentence SHA changed")?;
        require(sentence["candidate_only"] == true && sentence["semantic_promotion"] == false,
                "promoted sentence candidate")?;
        let rows = array(sentence, "dependency_rows")?;
        require(!rows.is_empty(), "sentence with no original dependency rows")?;
        let index: BTreeMap<u64, u32> = rows.iter().enumerate()
            .map(|(local, row)| Ok((number(row, "i")?,
                                  u32::try_from(local).map_err(|_| "too many tokens")?)))
            .collect::<Result<_, String>>()?;
        require(index.len() == rows.len(), "duplicate original parser ordinal")?;
        let mut tokens = Vec::new();
        let mut signals = Vec::new();
        let mut source_rows = Vec::new();
        for (local, row) in rows.iter().enumerate() {
            let ordinal = number(row, "i")?;
            let head_i = number(row, "head_i")?;
            let a = number(row, "idx")?;
            let surface = string(row, "text")?;
            let end = a + u64::try_from(surface.chars().count()).map_err(|_| "long token")?;
            require(slice(article, &offsets, a, end)? == surface,
                    "token differs from original source characters")?;
            let dep = string(row, "dep")?;
            let lemma = string(row, "lemma")?;
            let pos = string(row, "pos")?;
            let tag = row.get("tag").and_then(Value::as_str).unwrap_or("");
            let head = if head_i == ordinal {
                HeadDeclaration::SelfHead
            } else {
                HeadDeclaration::LocalOrdinal(
                    *index.get(&head_i).ok_or("original parser dependency head missing")?)
            };
            let signal = classify(dep, tag, surface);
            // AUX/mark signals can depend on tag/surface, not merely dep.
            // Preserve this distinction in the SymbolId -> signal map.
            let dep_symbol = interner.id("dep-signal", &format!("{dep}:{signal:?}"))?;
            let dep_slot = usize::try_from(dep_symbol).map_err(|_| "symbol overflow")?;
            if signals.len() <= dep_slot {
                signals.resize(dep_slot + 1, ExpansionSignal::Unsupported);
            }
            signals[dep_slot] = signal;
            tokens.push(TokenObservation {
                token_id: (sentence_id << 32) | local as u64,
                sentence_id,
                local_ordinal: u32::try_from(local).map_err(|_| "token index overflow")?,
                span: TextSpan::new(1385850169, a as u32, end as u32)
                    .map_err(|_| "invalid original text span")?,
                orth: interner.id("orth", surface)?,
                lemma: Annotation::Present(interner.id("lemma", lemma)?),
                pos: Annotation::Present(interner.id("pos", pos)?),
                tag: if tag.is_empty() {
                    Annotation::Unavailable(Capability::Tag)
                } else {
                    Annotation::Present(interner.id("tag", tag)?)
                },
                dependency: Annotation::Present(dep_symbol),
                declared_head: head,
            });
            source_rows.push(json!({
                "original_parser_i": ordinal,
                "token_ordinal": local,
                "dep": dep,
                "head_original_i": head_i,
                "source_span": [a,end],
                "surface": surface,
                "signal": format!("{signal:?}"),
                "is_syntactic_attachment_not_resolved_actor": dep == "agent",
            }));
        }
        let parity = check_expanded_parity(tokens, |symbol| {
            signals.get(symbol as usize).copied().unwrap_or(ExpansionSignal::Unsupported)
        });
        require(parity.holds(), "SLR direct/reference semantic expansion parity failure")?;
        require(parity.direct.projection_failures.is_empty(),
                "SLR original parser dependency graph projection failure")?;
        actual_tokens += rows.len();
        actual_candidates += parity.direct.candidates.len();
        actual_alternatives += parity.direct.alternative_fibres.len();
        actual_residuals += parity.direct.residuals.len();
        for residual in &parity.direct.residuals {
            *kinds.entry(format!("{:?}", residual.kind)).or_default() += 1;
        }
        parity_sentences += 1;
        if sentence_id == 18 || sentence_id == 5 ||
            sentence_id == 9 || sentence_id == 131 {
            sample_witnesses.push(json!({
                "sentence_index": sentence_id,
                "source_sentence": exact_sentence,
                "source_token_map": source_rows,
                "native_observation": receipt_json(&parity.direct),
                "consumer_answers": {
                    "mentions_and_syntactic_roles":
                        "source-bound candidate observations only",
                    "which_historical_person": "NOT_CLOSED",
                    "what_event_occurred": "NOT_CLOSED",
                    "which_year_is_an_event_date": "NOT_CLOSED",
                    "embedded_conjunction_scope": "SOURCE_GRAPH_AVAILABLE; SEMANTIC_CLOSURE_UNPAID"
                }
            }));
        }
        observations.push(receipt_json(&parity.direct));
    }
    require(parity_sentences == number(&record["parser_receipt"], "sentence_count")? as usize,
            "sentence count mismatch");
    require(actual_tokens == number(&record["parser_receipt"], "token_count")? as usize,
            "token count mismatch");
    Ok(json!({
        "schema": "gwb-slr-native-semantic-expansion-observations-v1",
        "source_revision": REVISION,
        "source_text_sha256": SOURCE_SHA,
        "engine": "sensiblaw-semantic-expansion",
        "engine_certification": "EXPERIMENTAL_CANDIDATE_ONLY_OUTSIDE_CERTIFIED_DIRECT_PATH",
        "parser_rerun": false,
        "nlp_model_invoked": false,
        "original_parser_receipt_backend": record["parser_receipt"]["parser_backend"],
        "fibre_replay": "ACTUAL_SLR_RUST_DIRECT_AND_REFERENCE_PROJECTORS",
        "source_sentences": parity_sentences,
        "source_tokens": actual_tokens,
        "native_candidate_count": actual_candidates,
        "alternative_fibre_count": actual_alternatives,
        "typed_residual_count": actual_residuals,
        "typed_residual_kinds": kinds,
        "direct_reference_parity_complete": true,
        "projection_failures": 0,
        "full_production_s28_or_hyperfabric_closure": false,
        "consumer_specific_semantic_licence_paid": false,
        "world_occurrence_paid": false,
        "scope_and_role_contract": {
            "conj_is_not_automatically_source_assertion": true,
            "agent_preposition_is_not_automatically_Actor": true,
            "clausal_alternatives_are_retained_as_unresolved": true,
            "unresolved_temporal_modifier_never_asserts_event_time": true
        },
        "real_source_witnesses": sample_witnesses,
        "consumer_adequacy": consumer_receipts(SOURCE_SHA)?,
        "sentence_observations": observations
    }))
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<String> = env::args().collect();
    if args.len() != 4 {
        return Err("usage: gwb_slr_fibre_probe ARTICLE.txt SLR-RECORD.json OUTPUT.json".into());
    }
    let article = fs::read_to_string(&args[1])?;
    let record: Value = serde_json::from_slice(&fs::read(&args[2])?)?;
    let receipt = run(&article, &record)?;
    fs::write(&args[3], serde_json::to_vec_pretty(&receipt)?)?;
    println!(
        "GWB_SLR_RUST_SEMANTIC_EXPANSION_PARITY_PASS sentences={} candidates={} alternatives={} residuals={}",
        receipt["source_sentences"], receipt["native_candidate_count"],
        receipt["alternative_fibre_count"], receipt["typed_residual_count"]
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn passive_agent_marker_does_not_promote_preposition_to_actor() {
        assert!(matches!(classify("agent", "IN", "by"),
            ExpansionSignal::ReferenceAttachment));
    }
    #[test]
    fn coordination_is_not_a_standalone_world_assertion() {
        assert!(matches!(classify("conj", "VBD", "had"),
            ExpansionSignal::Unsupported));
        assert!(matches!(classify("acl", "VBD", "possessed"),
            ExpansionSignal::ClausalModifier));
    }
    #[test]
    fn arbitrary_number_is_not_automatically_a_temporal_anchor() {
        assert!(matches!(classify("nummod", "CD", "2003"),
            ExpansionSignal::Unsupported));
    }
    #[test]
    fn modal_typed_but_nonmodal_auxiliary_not_falsely_licensed() {
        assert!(matches!(classify("aux", "MD", "may"),
            ExpansionSignal::ModalAuxiliary));
        assert!(matches!(classify("aux", "VB", "have"),
            ExpansionSignal::Unsupported));
    }
}

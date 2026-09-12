import Integration.Kernel.Quotient

/-!
# An admission instance: candidate ≠ admitted object

`Agda/DASHI/Cognition/PNF/SensibLawLegalSemanticAdmissionFrontierExact.agda`
describes a pipeline in which a parser proposes *candidates*, and a candidate
becomes an admitted semantic object only against an exact receipt that names a
non-parser authority, a policy and a resolver.  Its positive part (the receipt
record carrying `sameCandidate`) is a genuine Agda definition; its refusals —
`ParserCandidateAloneAuthorizesAdmission`, `ResidualFrequencyIsSemanticQuality`,
`ResidualPriorityScoreIsTruthConfidence` — are *empty datatypes* refuted by the
absurd pattern.  An uninhabited type refuted by `()` says only that the name has
no constructor; it carries no information about admission at all.

This module supplies the missing content: the same refusals as theorems about
the pipeline itself.

## What is proved

* `admits_iff_hasValidReceipt`, `resolve_admitted_iff` — the resolver admits
  exactly when a valid receipt for that exact candidate exists.
* `parser_receipt_never_valid` — a receipt whose authority is the parser is
  never valid: **the producer cannot certify its own output** (the pipeline form
  of `Integration.Kernel.Authority.report_cannot_certify_itself`).
* `receipt_for_other_candidate_never_valid` — candidate identity is matched
  exactly, so a receipt cannot be reused for a neighbouring candidate.
* **`resolve_is_lossless`** — the outcome of resolution always carries the
  candidate back, whether it was admitted or not; `resolve_failure` shows the
  failure branch returns the candidate *together with* its residuals and
  alternatives.  Failure is a retained fibre, not a deletion.
* **`admission_does_not_descend_through_frequency`** and
  `admission_does_not_descend_through_score` — no rule reading only how often
  the pattern occurred, or only how the runtime scored it, decides admission.
  These are instances of `Quotient.not_descendsThrough_of_collision`, i.e. of
  the general fact that a coordinate the quotient forgets is not recoverable.
* `admission_monotone_in_receipts` and `admission_is_not_monotone_in_candidates`
  — more receipts can only admit more; more candidates never admit more.

**Claim boundary.** A "candidate" is a record of numbers and labels, an
"authority" is one of three labels, and a "policy reference" is a string that is
only ever tested for emptiness.  Nothing here is a legal, regulatory or
linguistic claim, and no statement is made about any actual document,
instrument or parser.
-/

namespace Integration.Kernel.Instances.Admission

open Integration.Kernel.Quotient

/-! ## §1 Candidates and receipts -/

/-- What kind of unresolved scope the parser reports. -/
inductive Scope
  /-- Resolved by local syntax alone. -/
  | local'
  /-- Scope of a negation or modality is unresolved. -/
  | scopeUnresolved
  /-- Attachment is unresolved. -/
  | attachmentUnresolved
  deriving DecidableEq, Fintype, Repr

/-- Who is standing behind a resolution. -/
inductive Authority
  /-- The parser that produced the candidate. -/
  | parser
  /-- A reviewed deterministic policy. -/
  | reviewedPolicy
  /-- A human reviewer. -/
  | humanReview
  deriving DecidableEq, Fintype, Repr

/-- A parser proposal, keyed so that it can be matched exactly. -/
structure Candidate where
  /-- Sentence identifier. -/
  sentence : ℕ
  /-- Ordinal within the sentence. -/
  ordinal : ℕ
  /-- The unresolved scope class. -/
  scope : Scope
  /-- How often this pattern occurred in the corpus. -/
  frequency : ℕ
  /-- What the runtime scored it. -/
  score : ℕ
  deriving DecidableEq, Repr

/-- A resolution receipt. -/
structure Receipt where
  /-- The exact candidate this receipt resolves. -/
  candidate : Candidate
  /-- The authority standing behind the resolution. -/
  authority : Authority
  /-- The policy the resolution was taken under. -/
  policyRef : String
  /-- The resolver that produced it. -/
  resolverRef : String
  deriving DecidableEq, Repr

/-- A receipt is valid for a candidate when it matches that exact candidate and
carries a non-parser authority together with both references. -/
def Valid (r : Receipt) (c : Candidate) : Prop :=
  r.candidate = c ∧ r.authority ≠ Authority.parser ∧ r.policyRef ≠ "" ∧ r.resolverRef ≠ ""

instance (r : Receipt) (c : Candidate) : Decidable (Valid r c) := by
  unfold Valid; infer_instance

/-- The candidate is admissible against a receipt store. -/
def Admissible (rs : List Receipt) (c : Candidate) : Prop := ∃ r ∈ rs, Valid r c

instance (rs : List Receipt) (c : Candidate) : Decidable (Admissible rs c) := by
  unfold Admissible; infer_instance

theorem admits_iff_hasValidReceipt (rs : List Receipt) (c : Candidate) :
    Admissible rs c ↔ ∃ r ∈ rs, Valid r c := Iff.rfl

/-- **The producer cannot certify its own output.** -/
theorem parser_receipt_never_valid {r : Receipt} {c : Candidate}
    (h : r.authority = Authority.parser) : ¬ Valid r c := fun hv => hv.2.1 h

/-- Candidate identity is matched exactly. -/
theorem receipt_for_other_candidate_never_valid {r : Receipt} {c : Candidate}
    (h : r.candidate ≠ c) : ¬ Valid r c := fun hv => h hv.1

/-! ## §2 Lossless resolution -/

/-- A residual left behind when a candidate is not admitted. -/
inductive Residual
  /-- Negation scope unresolved. -/
  | negationScope
  /-- Attachment unresolved. -/
  | attachment
  /-- A dependency the pipeline does not support. -/
  | unsupported
  deriving DecidableEq, Fintype, Repr

/-- The result of trying to admit a candidate. -/
inductive Outcome
  /-- Admitted, against the receipt that carried it. -/
  | admitted (c : Candidate) (r : Receipt)
  /-- Not admitted: the candidate is retained, with its residuals and the
  alternatives that were still open. -/
  | retained (c : Candidate) (residuals : List Residual) (alternatives : List Candidate)
  deriving Repr

/-- Resolution: admit against the first valid receipt, otherwise retain
everything. -/
def resolve (rs : List Receipt) (c : Candidate) (residuals : List Residual)
    (alternatives : List Candidate) : Outcome :=
  match rs.find? (fun r => decide (Valid r c)) with
  | some r => Outcome.admitted c r
  | none => Outcome.retained c residuals alternatives

/-- The candidate carried by an outcome. -/
def outcomeCandidate : Outcome → Candidate
  | Outcome.admitted c _ => c
  | Outcome.retained c _ _ => c

/-- **Resolution is lossless in the candidate**: whichever branch is taken, the
candidate itself is returned. -/
theorem resolve_is_lossless (rs : List Receipt) (c : Candidate) (residuals : List Residual)
    (alternatives : List Candidate) :
    outcomeCandidate (resolve rs c residuals alternatives) = c := by
  unfold resolve
  cases rs.find? (fun r => decide (Valid r c)) <;> rfl

/-- With no valid receipt, the candidate is retained together with its residuals
and alternatives — nothing is deleted. -/
theorem resolve_failure (rs : List Receipt) (c : Candidate) (residuals : List Residual)
    (alternatives : List Candidate) (h : ¬ Admissible rs c) :
    resolve rs c residuals alternatives = Outcome.retained c residuals alternatives := by
  unfold resolve
  rcases hfind : rs.find? (fun r => decide (Valid r c)) with _ | r₀
  · rfl
  · exact absurd (⟨r₀, List.mem_of_find?_eq_some hfind,
      of_decide_eq_true (List.find?_some (p := fun r => decide (Valid r c)) hfind)⟩ : Admissible rs c) h

/-- With a valid receipt, resolution admits. -/
theorem resolve_admitted_iff (rs : List Receipt) (c : Candidate) (residuals : List Residual)
    (alternatives : List Candidate) :
    (∃ r, resolve rs c residuals alternatives = Outcome.admitted c r) ↔ Admissible rs c := by
  unfold resolve
  rcases hfind : rs.find? (fun r => decide (Valid r c)) with _ | r₀
  · constructor
    · rintro ⟨r₁, hr₁⟩
      exact absurd hr₁ (by simp)
    · rintro ⟨r₁, hr₁, hv⟩
      exact absurd (decide_eq_true hv) (List.find?_eq_none.1 hfind r₁ hr₁)
  · exact ⟨fun _ => ⟨r₀, List.mem_of_find?_eq_some hfind,
      of_decide_eq_true (List.find?_some (p := fun r => decide (Valid r c)) hfind)⟩, fun _ => ⟨r₀, rfl⟩⟩

/-! ## §3 What admission is not a function of -/

/-- Two candidates with the same occurrence count, only one of which has a
receipt. -/
def commonCandidate : Candidate := ⟨0, 0, Scope.scopeUnresolved, 7, 3⟩

/-- A second candidate with the *same* frequency and score as the first. -/
def rivalCandidate : Candidate := ⟨0, 1, Scope.scopeUnresolved, 7, 3⟩

/-- The store holds a receipt for the first candidate only. -/
def store : List Receipt :=
  [⟨commonCandidate, Authority.reviewedPolicy, "policy-1", "resolver-1"⟩]

theorem common_admissible : Admissible store commonCandidate :=
  ⟨store.head (by simp [store]), by simp [store], ⟨rfl, by decide, by decide, by decide⟩⟩

theorem rival_not_admissible : ¬ Admissible store rivalCandidate := by
  rintro ⟨r, hr, hv⟩
  simp only [store, List.mem_singleton] at hr
  subst hr
  exact absurd hv.1 (by decide)

theorem frequencies_agree : commonCandidate.frequency = rivalCandidate.frequency := rfl

theorem scores_agree : commonCandidate.score = rivalCandidate.score := rfl

/-- **How often a pattern occurs does not decide whether it is admitted.**  No
function of the frequency reproduces the admission status. -/
theorem admission_does_not_descend_through_frequency :
    ¬ DescendsThrough (fun c => decide (Admissible store c)) Candidate.frequency := by
  refine not_descendsThrough_of_collision (x := commonCandidate) (y := rivalCandidate)
    frequencies_agree ?_
  simp only [ne_eq, decide_eq_decide]
  exact fun h => rival_not_admissible (h.1 common_admissible)

/-- **Runtime score is not semantic authority** either. -/
theorem admission_does_not_descend_through_score :
    ¬ DescendsThrough (fun c => decide (Admissible store c)) Candidate.score := by
  refine not_descendsThrough_of_collision (x := commonCandidate) (y := rivalCandidate)
    scores_agree ?_
  simp only [ne_eq, decide_eq_decide]
  exact fun h => rival_not_admissible (h.1 common_admissible)

/-! ## §4 Monotonicity -/

theorem admission_monotone_in_receipts {rs rs' : List Receipt} (h : rs ⊆ rs')
    {c : Candidate} (hc : Admissible rs c) : Admissible rs' c := by
  obtain ⟨r, hr, hv⟩ := hc
  exact ⟨r, h hr, hv⟩

/-- Proposing more candidates does not admit more: admission is per candidate
and needs its own receipt. -/
theorem admission_is_not_monotone_in_candidates :
    ∃ (rs : List Receipt) (c c' : Candidate), Admissible rs c ∧ ¬ Admissible rs c' :=
  ⟨store, commonCandidate, rivalCandidate, common_admissible, rival_not_admissible⟩

end Integration.Kernel.Instances.Admission

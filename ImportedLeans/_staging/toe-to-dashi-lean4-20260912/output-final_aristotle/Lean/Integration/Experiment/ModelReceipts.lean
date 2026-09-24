import Integration.Experiment.ParameterRegion

/-!
# Stage 4, lane 4 — receipts, and the typed repair frontier

Two things are guarded here.

## 1. Sophistication is not authority

The anti-pattern this lane exists to block is

```
more mathematical sophistication  ⇒  appearance of more empirical authority.
```

An ODE with ten parameters is not more trustworthy than an algebraic model
because it looks more like physics.  So a model carries **three separate
receipts**, and they are proved to be independent coordinates:

* `ModelStructureReceipt` — what the model is made of (state dimension,
  parameter count, mechanistic terms);
* `ParameterEvidenceReceipt` — which data pinned the parameters, and how many of
  them are actually pinned;
* `ValidationReceipt` — how many independent predictions were tested, and how
  badly the worst one missed.

Proved:

* `receipts_are_independent` — any combination of the three occurs, so no
  receipt can be inferred from another;
* `structure_does_not_determine_validation` — two models with the *same*
  structure and different validation records;
* `finer_structure_does_not_imply_better_prediction` — a strictly more
  mechanistic model with a strictly worse validation error: mechanistic
  resolution does not imply empirical adequacy;
* `adding_parameters_without_evidence_is_underdetermined` — and the cost is
  explicit: extending a fully-constrained model with new parameters and no new
  evidence leaves it underdetermined.

## 2. A repair proposal is not a repair acceptance

`Integration.Experiment.ParameterRegion.FamilyFalsified` opens a typed frontier.
The repairs are *classified* (`RepairKind`: a new parameter range, a new latent
state, a new dynamical term, a new model class, a measurement failure, an
incorrect source assumption) but proposing one is not accepting it:

* a `RepairProposal` that `Explains` the anomaly is only that;
* a `RepairAcceptance` additionally demands a **novel prediction that could have
  failed**: an observation at the novel time that would empty the repaired
  family, and the actual observation that did not;
* `accepted_repair_is_refutable` — acceptance therefore always exhibits a
  possible refutation;
* `unfalsifiable_repair_admits_no_acceptance` — and a model class flexible
  enough to fit any observation (`flexibleFamily`, the function-space family)
  can never be accepted, however well it explains the anomaly.  This is the
  moving-target anti-pattern, blocked at the type level;
* `repair_does_not_rehabilitate_the_old_family` — the falsified family stays
  falsified: a repair replaces a model, it does not clear one.

**Claim boundary.** Receipts are records of numbers and strings; nothing checks
that a `ModelStructureReceipt` describes any particular Lean model, exactly the
free-field caveat Stage 3 recorded for `assumptions` and `provenance`.  The
repair results are about the `ParamFamily` objects named in them.
-/

namespace Integration.Experiment.ModelReceipts

open Set
open Integration.Experiment.ParameterRegion

/-! ## §1 Three receipts, kept apart -/

/-- **What the model is made of.** -/
structure ModelStructureReceipt where
  /-- A label. -/
  name : String
  /-- The dimension of the state vector. -/
  stateDimension : ℕ
  /-- How many free parameters the structure has. -/
  parameterCount : ℕ
  /-- The mechanistic terms the model claims to represent. -/
  mechanisticTerms : List String
  deriving DecidableEq

/-- **What pinned the parameters.** -/
structure ParameterEvidenceReceipt where
  /-- The data sets the parameters were derived from. -/
  sources : List String
  /-- How many of the structure's parameters the evidence actually
  constrains. -/
  constrained : ℕ
  deriving DecidableEq

/-- **What was tested afterwards.**  `heldOutTests` counts predictions made
before the corresponding measurement was seen; `worstError` is the largest miss
among them. -/
structure ValidationReceipt where
  /-- Number of independent, held-out predictions tested. -/
  heldOutTests : ℕ
  /-- The largest error among them. -/
  worstError : ℚ
  deriving DecidableEq

/-- A model's three receipts, carried separately (the model dossier). -/
structure ModelDossier where
  /-- The structure receipt. -/
  structureR : ModelStructureReceipt
  /-- The parameter-evidence receipt. -/
  paramR : ParameterEvidenceReceipt
  /-- The validation receipt. -/
  validationR : ValidationReceipt

/-- **The three receipts are independent coordinates**: every combination
occurs, so none of them can be read off another. -/
theorem receipts_are_independent (s : ModelStructureReceipt) (p : ParameterEvidenceReceipt)
    (v : ValidationReceipt) :
    ∃ m : ModelDossier, m.structureR = s ∧ m.paramR = p ∧ m.validationR = v :=
  ⟨⟨s, p, v⟩, rfl, rfl, rfl⟩

/-- **Structure does not determine validation.**  Two models with identical
structure receipts can have different validation records, so "what the model is
made of" is never evidence about "how well it predicted". -/
theorem structure_does_not_determine_validation :
    ∃ m₁ m₂ : ModelDossier, m₁.structureR = m₂.structureR ∧ m₁.validationR ≠ m₂.validationR := by
  refine ⟨⟨⟨"m", 1, 1, []⟩, ⟨[], 1⟩, ⟨5, 1/100⟩⟩, ⟨⟨"m", 1, 1, []⟩, ⟨[], 1⟩, ⟨5, 1⟩⟩, rfl, ?_⟩
  intro hcon
  have : (1/100 : ℚ) = 1 := congrArg ValidationReceipt.worstError hcon
  norm_num at this

/-- `m₂` is **mechanistically finer** than `m₁`: a larger state and strictly more
mechanistic terms. -/
def MechanisticallyFiner (m₂ m₁ : ModelDossier) : Prop :=
  m₁.structureR.stateDimension < m₂.structureR.stateDimension ∧
    m₁.structureR.mechanisticTerms.length < m₂.structureR.mechanisticTerms.length

/-- `m₂` is **empirically better** than `m₁`: at least as many held-out tests and
a strictly smaller worst error. -/
def EmpiricallyBetter (m₂ m₁ : ModelDossier) : Prop :=
  m₁.validationR.heldOutTests ≤ m₂.validationR.heldOutTests ∧
    m₂.validationR.worstError < m₁.validationR.worstError

/-- **Better mechanistic resolution does not imply better empirical
prediction.**  A model with a richer state and more mechanistic terms can have a
strictly worse validation record; without calibration and validation evidence,
sophistication carries no empirical authority. -/
theorem finer_structure_does_not_imply_better_prediction :
    ∃ m₁ m₂ : ModelDossier, MechanisticallyFiner m₂ m₁ ∧ ¬ EmpiricallyBetter m₂ m₁ := by
  refine ⟨⟨⟨"algebraic", 1, 1, ["ohmic"]⟩, ⟨["bench"], 1⟩, ⟨10, 1/100⟩⟩,
    ⟨⟨"mechanistic", 4, 9, ["ohmic", "diffusion", "thermal"]⟩, ⟨["bench"], 1⟩, ⟨10, 1/2⟩⟩,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨-, hlt⟩
  norm_num at hlt

/-- Nor conversely: an empirically better model need not be finer. -/
theorem better_prediction_does_not_imply_finer_structure :
    ∃ m₁ m₂ : ModelDossier, EmpiricallyBetter m₂ m₁ ∧ ¬ MechanisticallyFiner m₂ m₁ := by
  refine ⟨⟨⟨"mechanistic", 4, 9, ["ohmic", "diffusion", "thermal"]⟩, ⟨["bench"], 1⟩, ⟨10, 1/2⟩⟩,
    ⟨⟨"algebraic", 1, 1, ["ohmic"]⟩, ⟨["bench"], 1⟩, ⟨10, 1/100⟩⟩,
    ⟨by norm_num, by norm_num⟩, ?_⟩
  rintro ⟨hlt, -⟩
  norm_num at hlt

/-- A model is **underdetermined** when the evidence constrains fewer parameters
than the structure has. -/
def Underdetermined (m : ModelDossier) : Prop :=
  m.paramR.constrained < m.structureR.parameterCount

/-- **The cost of sophistication, made explicit.**  Extend a fully constrained
model with extra parameters and no extra evidence, and the result is
underdetermined — the new mechanism is unpaid for. -/
theorem adding_parameters_without_evidence_is_underdetermined (m m' : ModelDossier)
    (hdet : m.structureR.parameterCount ≤ m.paramR.constrained)
    (hmore : m.structureR.parameterCount < m'.structureR.parameterCount)
    (hsame : m'.paramR.constrained ≤ m.paramR.constrained)
    (hpaid : m.paramR.constrained ≤ m.structureR.parameterCount) :
    Underdetermined m' := by
  unfold Underdetermined
  omega

/-! ## §2 The typed repair frontier -/

/-- **How a falsified model family may be repaired.**  The classification is
declared, and a proposal must say which kind it is; nothing here ranks the
kinds. -/
inductive RepairKind
  /-- Keep the model, widen or move the parameter region. -/
  | newParameterRange
  /-- Add a latent state the old model did not carry. -/
  | newLatentState
  /-- Add a term to the dynamics. -/
  | newDynamicalTerm
  /-- Replace the model class. -/
  | newModelClass
  /-- Blame the instrument rather than the model. -/
  | measurementFailure
  /-- Blame an assumption about the data's provenance. -/
  | incorrectSourceAssumption
  deriving DecidableEq, Repr

/-- **A repair proposal**: a classified replacement family for one that the
evidence falsified. -/
structure RepairProposal (Θ : Type*) where
  /-- Which kind of repair this is. -/
  kind : RepairKind
  /-- The replacement family. -/
  repaired : ParamFamily Θ
  /-- The analyst's stated reason. -/
  rationale : String

/-- A proposal **explains** the anomalous evidence when some parameter of the
replacement family survives it. -/
def Explains {Θ : Type*} (P : RepairProposal Θ) (E : List Reading) : Prop :=
  (Compatible P.repaired E).Nonempty

/-- **A repair acceptance.**  Explaining the anomaly is not enough: the repair
must make a prediction that *could have failed* — an observation at the novel
time that would have emptied the repaired family — and must then survive the
observation actually taken. -/
structure RepairAcceptance {Θ : Type*} (P : RepairProposal Θ) (E : List Reading) where
  /-- It accounts for the anomaly. -/
  explains : Explains P E
  /-- A measurement the repair commits to. -/
  novel : Reading
  /-- The commitment has teeth: some possible reading at that time would refute
  the repaired family outright. -/
  refutable : ∃ y : Reading, y.time = novel.time ∧ FamilyFalsified P.repaired (y :: E)
  /-- And the observation actually taken did not. -/
  survived : (Compatible P.repaired (novel :: E)).Nonempty

/-- **An accepted repair is refutable.**  Acceptance always exhibits an
observation that would have killed the repaired family: this is the projection
that makes the distinction between proposal and acceptance load-bearing. -/
theorem accepted_repair_is_refutable {Θ : Type*} {P : RepairProposal Θ} {E : List Reading}
    (A : RepairAcceptance P E) : ∃ y : Reading, FamilyFalsified P.repaired (y :: E) := by
  obtain ⟨y, -, hy⟩ := A.refutable
  exact ⟨y, hy⟩

/-- The family-space analogue of "fit anything": parameters are arbitrary
functions of time, and the prediction is the function itself. -/
def flexibleFamily : ParamFamily (ℝ → ℝ) where
  prior := univ
  predict := fun f t => f t

/-- **The flexible family explains any single observation.** -/
theorem flexible_explains_everything (y : Reading) :
    (Compatible flexibleFamily [y]).Nonempty := by
  refine ⟨fun _ => y.value, mem_univ _, ?_⟩
  rintro r hr
  rcases List.mem_singleton.mp hr with rfl
  show |r.value - r.value| ≤ r.tol
  simpa using r.tol_nonneg

/-- Hence it is never falsified by one reading. -/
theorem flexible_is_never_falsified (y : Reading) :
    ¬ FamilyFalsified flexibleFamily [y] := by
  intro hfail
  obtain ⟨f, hf⟩ := flexible_explains_everything y
  exact (Set.eq_empty_iff_forall_notMem.mp hfail f) hf

/-- **A repair that cannot fail cannot be accepted.**  A proposal whose
replacement is the arbitrarily flexible family explains the anomaly, but admits
no `RepairAcceptance`: there is no observation it could not absorb, so it has no
novel prediction with teeth.  This is the moving-target anti-pattern blocked at
the type level — the repair stays conjectural forever, by construction. -/
theorem unfalsifiable_repair_admits_no_acceptance (k : RepairKind) (why : String) :
    Explains ⟨k, flexibleFamily, why⟩ [] ∧
      ¬ Nonempty (RepairAcceptance (⟨k, flexibleFamily, why⟩ : RepairProposal (ℝ → ℝ)) []) := by
  constructor
  · exact ⟨fun _ => 0, mem_univ _, by rintro r hr; cases hr⟩
  · rintro ⟨A⟩
    obtain ⟨y, -, hy⟩ := A.refutable
    exact flexible_is_never_falsified y hy

/-- **A repair does not rehabilitate the family it replaces.**  Whatever the
proposal, the falsified family stays falsified under the same evidence, and
under any extension of it. -/
theorem repair_does_not_rehabilitate_the_old_family {Θ : Type*} (F : ParamFamily Θ)
    {E E' : List Reading} (hsub : ∀ r ∈ E, r ∈ E') (hfail : FamilyFalsified F E) :
    FamilyFalsified F E' :=
  falsified_is_permanent F hsub hfail

/-- **Proposal is not acceptance**, as a single statement: there is a proposal
that explains the evidence and yet cannot be accepted. -/
theorem proposal_is_not_acceptance :
    ∃ (P : RepairProposal (ℝ → ℝ)) (E : List Reading),
      Explains P E ∧ ¬ Nonempty (RepairAcceptance P E) :=
  ⟨⟨RepairKind.newModelClass, flexibleFamily, "fit a free curve"⟩, [],
    (unfalsifiable_repair_admits_no_acceptance RepairKind.newModelClass "fit a free curve").1,
    (unfalsifiable_repair_admits_no_acceptance RepairKind.newModelClass "fit a free curve").2⟩

end Integration.Experiment.ModelReceipts

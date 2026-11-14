import Mathlib

/-!
# BCH 2026 Appendix A: explicitly conditional computational-hardness interface

Original source: Alexander Bastounis, Fabian Circelli and Anders C. Hansen,
arXiv:2610.08144v1 (2026-10-06), Appendix A.2,
Theorems A.3 and A.4. The source's deep results rely on
Davis–Putnam–Robinson–Matiyasevich (DPRM), its nine-unknown refinement,
uniform coding of polynomial enumerations, computable many-one reductions,
Post's theorem, and strictness of the arithmetical hierarchy.

This file *does not* formalise any of those external theorems. Instead it
(1) encodes the source's existential/universal presupposition shape,
(2) proves a reduction transports a candidate Bool-decider, and
(3) makes effectiveness and undecidability separate explicit hypotheses.

Passing a noncomputable mathematical function as "an algorithm" would
be unsound. Therefore all actual computability premises appear as a
separate abstract predicate, with an explicit closure law. There is no
claim here that SCI=infinity has been proved in the Lean kernel.
-/

namespace RequestProject.Autoformalisation.LostInTranslationSCI

/-- Level-two presupposition family (A.3) after encoding the tuple of
root variables as one natural number. This alone does not assert any
uniform computable polynomial encoding or DPRM equivalence. -/
def WitnesslessAt (R : ℕ → ℕ → ℕ → Prop)
    (e n : ℕ) : Prop :=
  ∀ x : ℕ, ¬ R e n x

def ExistencePresupposition (R : ℕ → ℕ → ℕ → Prop)
    (e : ℕ) : Prop :=
  ∃ n : ℕ, WitnesslessAt R e n

/-- Any *source-faithful* least-number object carries its defining
existence proof, rather than manufacturing a default witness. -/
noncomputable def leastPresupposition
    (R : ℕ → ℕ → ℕ → Prop) (e : ℕ)
    (hExists : ExistencePresupposition R e) : ℕ := by
  classical
  exact Nat.find hExists

theorem leastPresupposition_is_admissible
    (R : ℕ → ℕ → ℕ → Prop) (e : ℕ)
    (hExists : ExistencePresupposition R e) :
    WitnesslessAt R e (leastPresupposition R e hExists) := by
  classical
  exact Nat.find_spec hExists

/-- A Boolean candidate is *extensionally correct* as a decision
function. This contains no computability promise by itself. -/
def CorrectBoolResolver (P : ℕ → Prop) (f : ℕ → Bool) : Prop :=
  ∀ n : ℕ, (f n = true ↔ P n)

/-- A many-one reduction is the source's semantic equivalence.
Computability is kept in a separate predicate, not inferred. -/
def ManyOneProperty
    (Hard Target : ℕ → Prop) (reduce : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, (Hard n ↔ Target (reduce n))

theorem bool_resolution_transfers_under_reduction
    (Hard Target : ℕ → Prop)
    (reduce : ℕ → ℕ) (hReduce : ManyOneProperty Hard Target reduce)
    (resolver : ℕ → Bool) (hResolver : CorrectBoolResolver Target resolver) :
    CorrectBoolResolver Hard (fun n => resolver (reduce n)) := by
  intro n
  exact (hResolver (reduce n)).trans (hReduce n).symm

/-- The parameter 'Effective' is *required* to mean the chosen
computational model's computable Boolean functions. If its closure
under precomposition is not supplied, no undecidability conclusion
is justified. In particular, Effective := fun _ => True is not
silently conflated with computability. -/
theorem no_effective_resolution_of_many_one_hardness
    (Hard Target : ℕ → Prop)
    (Effective : (ℕ → Bool) → Prop)
    (reduce : ℕ → ℕ)
    (hReduce : ManyOneProperty Hard Target reduce)
    (hEffectiveClosure :
      ∀ f : ℕ → Bool, Effective f →
        Effective (fun n => f (reduce n)))
    (hardUndecidable :
      ¬ ∃ f : ℕ → Bool,
        Effective f ∧ CorrectBoolResolver Hard f) :
    ¬ ∃ f : ℕ → Bool,
      Effective f ∧ CorrectBoolResolver Target f := by
  rintro ⟨resolver, hEff, hCorrect⟩
  apply hardUndecidable
  refine ⟨(fun n => resolver (reduce n)), ?_, ?_⟩
  · exact hEffectiveClosure resolver hEff
  · exact bool_resolution_transfers_under_reduction
      Hard Target reduce hReduce resolver hCorrect

/-- The paper's A.4 hierarchy ranges over arbitrary finite alternation
levels. We encode the quantified *family* by an external predicate;
we do not construct the DPRM polynomials or prove Σ⁰_l-completeness. -/
structure ArithmeticalHardnessObligation
    (level : ℕ) (Target : ℕ → Prop)
    (SigmaComplete : ℕ → (ℕ → Prop) → Prop)
    (HasDPRMReduction : ℕ → (ℕ → Prop) → Prop)
    (PostTheoremCondition : ℕ → (ℕ → Prop) → Prop) : Prop where
  levelAtLeastTwo : 2 ≤ level
  sigmaLevelPaid : SigmaComplete level Target
  dprmReductionPaid : HasDPRMReduction level Target
  postConditionPaid : PostTheoremCondition level Target

/-- The three exact statements are supplied by the source's chosen formal
interpretation; a consumer must supply proofs of EACH. These predicates
are NOT constructed or asserted by this module. -/
theorem paid_appendix_requirements
    {level : ℕ} {Target : ℕ → Prop}
    {SigmaComplete : ℕ → (ℕ → Prop) → Prop}
    {HasDPRMReduction : ℕ → (ℕ → Prop) → Prop}
    {PostTheoremCondition : ℕ → (ℕ → Prop) → Prop}
    (receipt : ArithmeticalHardnessObligation
      level Target SigmaComplete HasDPRMReduction PostTheoremCondition) :
    SigmaComplete level Target ∧
      HasDPRMReduction level Target ∧
      PostTheoremCondition level Target :=
  ⟨receipt.sigmaLevelPaid, receipt.dprmReductionPaid,
   receipt.postConditionPaid⟩

/-!
## Cameron Freer's Hilbert10 (2026): exact donor-compatibility barrier

Original external theorem declaration, attributed to Cameron Freer,
`Hilbert10.exists_universal_mvPolynomial`, is of the form
  ∃ k U, ∀ e x y, evaluation ↔ ∃ z : Fin k → ℕ, U(...,z)=0.
This is an impressive universal *existence* theorem. It does NOT
supply a numerical bound k ≤ 9. BCH2026 Theorem A.3 invokes a
NINE-unknown DPRM refinement and A.4 adds the Σ_l arithmetical
hierarchy/strictness step. A successful direct import of Freer's
library thus would not discharge those separate requirements.

This theorem is a finite logical discriminator, NOT a judgement about
the correctness of Freer's Lean proofs or a substitute for importing
his exact original source. Never infer a 9-unknown statement from an
unbounded existential quantifier.
-/

/-- Existential representation with some witness count. -/
def HasSomeWitnessCount (R : ℕ → Prop) : Prop :=
  ∃ k : ℕ, R k

/-- The additional nine-unknown acceptance obligation. -/
def HasAtMostNineWitnesses (R : ℕ → Prop) : Prop :=
  ∃ k : ℕ, k ≤ 9 ∧ R k

theorem nine_unknown_representation_implies_some_representation
    (R : ℕ → Prop) :
    HasAtMostNineWitnesses R → HasSomeWitnessCount R := by
  rintro ⟨k, _, hk⟩
  exact ⟨k, hk⟩

/-- A finite model witnesses failure of the converse as a *general*
logical implication. This does NOT say Freer's actual universal
polynomial needs ten witnesses; only that his unbounded theorem
alone does not contain the additional nine-variable bound. -/
theorem some_witness_count_not_enough_for_nine :
    HasSomeWitnessCount (fun k : ℕ => k = 10) ∧
      ¬ HasAtMostNineWitnesses (fun k : ℕ => k = 10) := by
  constructor
  · exact ⟨10, rfl⟩
  · rintro ⟨k, hk, hEq⟩
    omega

/-!
## Appendix A.5: exact logical unboundedness consequence

The original paper's Corollary A.5 asserts that the *fixed-level*
SCI_A(chi_(d_l)) equals l, for every l>=2. It then infers that one
algorithm which correctly resolves *all* levels has no finite uniform
SCI height, when a uniform height would bound each fixed-level task.

This file certifies only THAT elementary mathematical deduction from
an external proof of the fixed-level SCI equalities and the required
restriction semantics. It does not define or prove the arithmetic
tower SCI, Sigma_l completeness, Post's theorem, the nine-unknown
polynomial encoding, or the level-to-uniform restriction theorem.
-/

/-- From the source's A.5 *as an explicit premise*, no finite
uniform ceiling can bound all fixed-level SCI values. -/
theorem fixed_level_sci_unbounded_of_corollary_A5
    (fixedLevelSCI : ℕ → ℕ)
    (hA5 : ∀ l : ℕ, 2 ≤ l → fixedLevelSCI l = l) :
    ∀ height : ℕ, ∃ l : ℕ,
      2 ≤ l ∧ height < fixedLevelSCI l := by
  intro height
  refine ⟨max 2 (height + 1), ?_, ?_⟩
  · exact le_max_left _ _
  · rw [hA5 _ (le_max_left _ _)]
    have h : height + 1 ≤ max 2 (height + 1) :=
      le_max_right _ _
    omega

/-- A hypothetical *uniform* finite-height procedure must supply an
independent theorem bounding EVERY fixed-level restriction.
That cannot coexist with the paper's A.5 fixed-level equalities.
This is an exact quantified contradiction, not an SCI definition. -/
theorem no_uniform_finite_height_if_all_fixed_levels_restrict
    (fixedLevelSCI : ℕ → ℕ)
    (hA5 : ∀ l : ℕ, 2 ≤ l → fixedLevelSCI l = l)
    (uniformHeight : ℕ)
    (hRestrictions :
      ∀ l : ℕ, 2 ≤ l → fixedLevelSCI l ≤ uniformHeight) :
    False := by
  obtain ⟨l, hl2, hlUnbounded⟩ :=
    fixed_level_sci_unbounded_of_corollary_A5 fixedLevelSCI hA5
      uniformHeight
  exact (not_lt_of_ge (hRestrictions l hl2)) hlUnbounded

end RequestProject.Autoformalisation.LostInTranslationSCI

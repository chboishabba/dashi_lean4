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
    (hExists : ExistencePresupposition R e) : ℕ :=
  Nat.find hExists

theorem leastPresupposition_is_admissible
    (R : ℕ → ℕ → ℕ → Prop) (e : ℕ)
    (hExists : ExistencePresupposition R e) :
    WitnesslessAt R e (leastPresupposition R e hExists) := by
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

end RequestProject.Autoformalisation.LostInTranslationSCI

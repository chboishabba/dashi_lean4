import Integration.Experiment.ModelDiscrepancy
import Integration.Experiment.DiscrepancyCoverage
import Integration.Experiment.VectorDynamics
import Integration.Experiment.CorrelatedUncertainty
import Integration.Experiment.InformationMatrix
import Integration.Experiment.IdentifiabilityRadius
import Integration.Experiment.LocalIdentifiability
import Integration.Experiment.RepairSearch

/-!
# Stage-7 reconciliation — the robustness frontier as Lean propositions

The Agda side of the corpus carries a Stage-7 *frontier* module which records
the robustness programme in two pieces:

* an enumeration of six outstanding **robustness obligations** — model
  discrepancy, vector state/parameter/control dynamics, correlated uncertainty,
  experiment design, quantitative local identifiability, held-out repair
  validation; and
* a **boundary record** whose four fields are `Bool`s pinned to `false` with a
  proof of the pinning: "calibrated fit determines model adequacy", "a diagonal
  variance budget solves correlated attribution", "local Jacobian rank gives
  global identifiability", "a repair that fits the training data is
  scientifically supported".

A `Bool` field pinned to `false` is a *ledger entry*: it records the intended
reading, but it is not a proof that the claim fails, because the claim is not
stated as a proposition about any inference machinery at all.

This module does the reconciliation on the Lean side, where the machinery does
exist.  Each of the four boundary entries is written out as a proposition
`boundaryClaim c` about the Stage-7 Lean definitions, and each is *refuted*
(`boundary_claims_are_false`).  Each of the six obligations is given a
proposition `genericContent o` naming what the Lean development actually
establishes for it, and all six are discharged
(`every_obligation_has_generic_content`).

## Reading discipline

This is a statement about the Lean development only.  Nothing here typechecks
any Agda module, transports any Agda proof term, or claims that the Agda
obligations are closed: what is shown is that the corresponding *generic*
mathematics is available in Lean, and — for the four boundary entries — that the
`false` pinning is the correct one, as a theorem rather than as a declaration.

## What is proved

* `boundary_claims_are_false` — all four boundary claims fail;
* `every_obligation_has_generic_content` — all six obligations have a proved
  generic Lean statement;
* `boundary_and_obligations_are_different_registers` — the two tables are not
  the same table: a discharged generic obligation does not make the
  corresponding boundary claim true.
-/

namespace Integration.Reconciliation.Stage7Boundary

open Integration.Experiment
open Integration.Experiment.ParameterRegion
open Integration.Experiment.Uncertainty
open Integration.Experiment.VarianceBudget
open Integration.Experiment.InformationMatrix
open Integration.Experiment.JacobianSensitivity

/-- The four boundary entries of the Agda Stage-7 frontier record. -/
inductive BoundaryClaim
  | calibratedFitDeterminesModelAdequacy
  | diagonalVarianceBudgetSolvesCorrelatedAttribution
  | localJacobianRankGivesGlobalIdentifiability
  | repairThatFitsTrainingIsScientificallySupported
  deriving DecidableEq, Repr

/-- The six robustness obligations of the Agda Stage-7 frontier enumeration. -/
inductive RobustnessObligation
  | modelDiscrepancy
  | vectorStateParameterControl
  | correlatedUncertainty
  | experimentDesign
  | quantitativeLocalIdentifiability
  | heldOutRepairValidation
  deriving DecidableEq, Repr

/-- Each boundary entry, written out as a proposition about the Stage-7 Lean
definitions rather than as a `Bool`. -/
def boundaryClaim : BoundaryClaim → Prop
  | .calibratedFitDeterminesModelAdequacy =>
      ∀ (η : ℝ) (F : ParamFamily ℝ) (E : List Reading) (truth : ℝ → ℝ),
        ModelDiscrepancy.Generates truth E →
        ∀ θ ∈ Compatible F E, ModelDiscrepancy.AdequateOn F θ truth Set.univ η
  | .diagonalVarianceBudgetSolvesCorrelatedAttribution =>
      ∀ A B : (Fin 2 → ℝ) → RCov 2 → Fin 2 → ℝ,
        CorrelatedUncertainty.IsAttribution A → CorrelatedUncertainty.IsAttribution B → A = B
  | .localJacobianRankGivesGlobalIdentifiability =>
      ∀ f : ℝ → ℝ, (∃ s ∈ nhds (1 : ℝ), Set.InjOn f s) → Function.Injective f
  | .repairThatFitsTrainingIsScientificallySupported =>
      ∀ (Θ : Type) (F : ParamFamily Θ) (D : List Reading),
        (Compatible F D).Nonempty → RepairObligations.Refutable F →
        ∀ t : ℝ, RepairSearch.RisksSomethingAt F D t

/-- **The four boundary claims are false.**  The Agda record pins each of them
to `false`; here each is refuted against the actual inference machinery. -/
theorem boundary_claims_are_false : ∀ c : BoundaryClaim, ¬ boundaryClaim c := by
  intro c
  cases c with
  | calibratedFitDeterminesModelAdequacy =>
      intro hall
      simp only [boundaryClaim] at hall
      obtain ⟨F, E, truth, hgen, hpin, hbad⟩ :=
        ModelDiscrepancy.fit_precise_yet_arbitrarily_inadequate 1
      have hmem : (2 : ℝ) ∈ Compatible F E := by rw [hpin]; rfl
      obtain ⟨t, ht⟩ := hbad 2 hmem
      have hadq := hall 1 F E truth hgen 2 hmem t (Set.mem_univ t)
      rw [ModelDiscrepancy.discrepancy_apply] at hadq
      linarith
  | diagonalVarianceBudgetSolvesCorrelatedAttribution =>
      intro hall
      simp only [boundaryClaim] at hall
      obtain ⟨A, B, hA, hB, hne⟩ :=
        CorrelatedUncertainty.correlated_variance_has_no_canonical_attribution
      exact hne (hall A B hA hB)
  | localJacobianRankGivesGlobalIdentifiability =>
      intro hall
      simp only [boundaryClaim] at hall
      obtain ⟨f, hloc, hnot⟩ := LocalIdentifiability.local_identifiability_is_not_global
      exact hnot (hall f hloc)
  | repairThatFitsTrainingIsScientificallySupported =>
      intro hall
      simp only [boundaryClaim] at hall
      obtain ⟨hne, hrefut, hblind⟩ :=
        RepairSearch.fit_and_refutability_do_not_give_a_held_out_prediction
      exact hblind (hall (ℝ × ℝ) RepairSearch.blindAfterTwo RepairSearch.earlyData hne hrefut 3)

/-- For each obligation, the generic statement the Lean development actually
proves.  These are representatives, not the whole lane: each names one theorem
whose content is the obligation's mathematical core. -/
def genericContent : RobustnessObligation → Prop
  | .modelDiscrepancy =>
      ∀ (F : ParamFamily ℝ) (θ : ℝ) (truth : ℝ → ℝ) (t : ℝ),
        truth t = F.predict θ t + ModelDiscrepancy.discrepancy F θ truth t
  | .vectorStateParameterControl =>
      ∀ (n p q : ℕ) (hx : Matrix (Fin q) (Fin n) ℝ) (hθ : Matrix (Fin q) (Fin p) ℝ)
        (Smat : Matrix (Fin n) (Fin p) ℝ) (W : RCov q), PosDefWeight W →
        ∀ k : Fin p, (∀ i, Smat i k = 0) → (∀ i, hθ i k = 0) →
          (infoMatrix (VectorDynamics.outputJacobian hx hθ Smat) W).toMatrix.det = 0
  | .correlatedUncertainty =>
      ∀ (n : ℕ) (row : Fin n → ℝ) (S : RCov n),
        totalVariance row S
          = (∑ i, ownShare row S i) + CorrelatedUncertainty.crossTerms row S
  | .experimentDesign =>
      ∃ A B : RCov 2, dCrit B < dCrit A ∧ EigLower B 2 ∧ ¬ EigLower A 2
  | .quantitativeLocalIdentifiability =>
      Set.InjOn IdentifiabilityRadius.quadraticMap (Metric.ball (0 : ℝ) (1 / 2))
  | .heldOutRepairValidation =>
      RepairSearch.statusOfValidated RepairSearch.offsetValidated
          = RepairSearch.RepairStatus.supported ∧
        RepairSearch.RepairStatus.fitRestored ≠ RepairSearch.RepairStatus.supported

/-- **Every Stage-7 obligation has a proved generic Lean statement.** -/
theorem every_obligation_has_generic_content :
    ∀ o : RobustnessObligation, genericContent o := by
  intro o
  cases o with
  | modelDiscrepancy =>
      simp only [genericContent]
      exact fun F θ truth t => ModelDiscrepancy.truth_eq_model_add_discrepancy F θ truth t
  | vectorStateParameterControl =>
      simp only [genericContent]
      exact fun _ _ _ hx hθ Smat W hW k hS hh =>
        VectorDynamics.unexcited_parameter_makes_information_singular hx hθ Smat W hW k hS hh
  | correlatedUncertainty =>
      simp only [genericContent]
      exact fun _ row S => CorrelatedUncertainty.totalVariance_split row S
  | experimentDesign =>
      simp only [genericContent]
      exact criteria_disagree
  | quantitativeLocalIdentifiability =>
      simp only [genericContent]
      exact IdentifiabilityRadius.quadraticMap_certified_radius
  | heldOutRepairValidation =>
      simp only [genericContent]
      exact RepairSearch.offset_repair_is_promoted

/-- **The two tables are different registers.**  Every obligation has generic
content *and* every boundary claim is false: discharging the generic
mathematics of an obligation does not turn any of the boundary claims true.  In
particular the model-discrepancy lane is developed and "fit determines
adequacy" still fails. -/
theorem boundary_and_obligations_are_different_registers :
    (∀ o : RobustnessObligation, genericContent o) ∧
      (∀ c : BoundaryClaim, ¬ boundaryClaim c) :=
  ⟨every_obligation_has_generic_content, boundary_claims_are_false⟩

end Integration.Reconciliation.Stage7Boundary

/-
# Lean mirror of the canonical Agda proof-debt router

`DASHI.Core.ProofDebtRouterExact` is **canonical**.  This module is a thin
cross-prover mirror of it, not a second router: every constructor, every case of
`routeDebt` and `scheduleAction`, and every routing fact the Agda owner asserts
by `refl` is reproduced here and re-checked by the Lean kernel.  No routing
decision is invented, altered or extended on this side.

Crosswalk (Agda ⟶ Lean, all in `DASHI.Core.ProofDebtRouterExact`):

| Agda | Lean |
|---|---|
| `ClaimKind`, `MathematicalStatus`, `StatementStatus`, `CertificationStatus` | same constructors |
| `PreferredBackend`, `DebtClass`, `LocalResourceClass`, `ProofWorkload`, `SchedulerAction` | same constructors |
| `routeDebt`, `scheduleAction`, `scheduleExternalCertification` | same clause order |
| `SourceIdentity`, `StatementAlignmentReceipt`, `FullyAligned`, `SourceAlignedDeferredTheorem` | same fields |
| `sourceEstablishedAlignedDeferredIsCertificationDebt` etc. | `…_crosswalk` theorems below |

## The one thing this mirror adds

The Agda owner states its critical firewall in a comment:

> There is intentionally no function `SourceAlignedDeferredTheorem T -> T`.

Here that is a **theorem** rather than a comment: `no_receipt_to_theorem` proves
that no such function can exist, for any `T`, because receipts are pure data and
can be manufactured for `T = False`.  So a provenance/alignment receipt provably
cannot discharge a mathematical obligation, in this corpus or any other.
-/
import Mathlib

namespace RequestProject.NavierStokes.ProofDebtRouter

/-! ## 1.  The router's coordinates, mirrored constructor for constructor -/

/-- Agda `ClaimKind`. -/
inductive ClaimKind | deductiveTheorem | empiricalPremise
  deriving DecidableEq, Repr

/-- Agda `MathematicalStatus`. -/
inductive MathematicalStatus
  | novelOpen | sourceEstablished | experimentallySupportedPremise | derivedInRepo
  deriving DecidableEq, Repr

/-- Agda `StatementStatus`. -/
inductive StatementStatus | notTranscribed | transcribedUnaligned | sourceAligned
  deriving DecidableEq, Repr

/-- Agda `CertificationStatus`. -/
inductive CertificationStatus
  | uncertified | proofDeferred | leanKernelCertified | agdaKernelCertified
  deriving DecidableEq, Repr

/-- Agda `PreferredBackend`. -/
inductive PreferredBackend | localAgda | externalLean | aristotleLean | sourceOnly
  deriving DecidableEq, Repr

/-- Agda `DebtClass`. -/
inductive DebtClass
  | mathematicalDebt | transcriptionDebt | certificationDebt | empiricalEvidenceDebt | noDebt
  deriving DecidableEq, Repr

open ClaimKind MathematicalStatus StatementStatus CertificationStatus PreferredBackend DebtClass

/-- Agda `routeDebt`, clause for clause. -/
def routeDebt : ClaimKind → MathematicalStatus → StatementStatus → CertificationStatus → DebtClass
  | _, novelOpen, _, _ => mathematicalDebt
  | _, sourceEstablished, notTranscribed, _ => transcriptionDebt
  | _, sourceEstablished, transcribedUnaligned, _ => transcriptionDebt
  | _, sourceEstablished, sourceAligned, uncertified => certificationDebt
  | _, sourceEstablished, sourceAligned, proofDeferred => certificationDebt
  | _, sourceEstablished, sourceAligned, leanKernelCertified => noDebt
  | _, sourceEstablished, sourceAligned, agdaKernelCertified => noDebt
  | _, derivedInRepo, notTranscribed, _ => transcriptionDebt
  | _, derivedInRepo, transcribedUnaligned, _ => transcriptionDebt
  | _, derivedInRepo, sourceAligned, uncertified => certificationDebt
  | _, derivedInRepo, sourceAligned, proofDeferred => certificationDebt
  | _, derivedInRepo, sourceAligned, leanKernelCertified => noDebt
  | _, derivedInRepo, sourceAligned, agdaKernelCertified => noDebt
  | deductiveTheorem, experimentallySupportedPremise, _, _ => mathematicalDebt
  | empiricalPremise, experimentallySupportedPremise, notTranscribed, _ => transcriptionDebt
  | empiricalPremise, experimentallySupportedPremise, transcribedUnaligned, _ => transcriptionDebt
  | empiricalPremise, experimentallySupportedPremise, sourceAligned, uncertified =>
      empiricalEvidenceDebt
  | empiricalPremise, experimentallySupportedPremise, sourceAligned, proofDeferred =>
      empiricalEvidenceDebt
  | empiricalPremise, experimentallySupportedPremise, sourceAligned, leanKernelCertified => noDebt
  | empiricalPremise, experimentallySupportedPremise, sourceAligned, agdaKernelCertified => noDebt

/-! ### The routing facts the Agda owner asserts by `refl`, re-checked here -/

/-- Agda `sourceEstablishedAlignedDeferredIsCertificationDebt`. -/
theorem sourceEstablishedAlignedDeferred_crosswalk :
    routeDebt deductiveTheorem sourceEstablished sourceAligned proofDeferred
      = certificationDebt := rfl

/-- Agda `sourceEstablishedAlignedDeferredIsNotMathematicalDebt`. -/
theorem sourceEstablishedAlignedDeferred_not_mathematical_crosswalk :
    routeDebt deductiveTheorem sourceEstablished sourceAligned proofDeferred
      ≠ mathematicalDebt := by decide

/-- Agda `experimentDoesNotTurnDeductiveTheoremIntoEstablishedTheorem`. -/
theorem experiment_does_not_establish_theorem_crosswalk :
    routeDebt deductiveTheorem experimentallySupportedPremise sourceAligned proofDeferred
      = mathematicalDebt := rfl

/-- A novel open problem routes to mathematical debt whatever else is recorded:
no certification coordinate can move it.  (This is the discipline that keeps an
unproved Navier–Stokes endpoint out of the certified column.) -/
theorem novelOpen_always_mathematicalDebt (c : ClaimKind) (s : StatementStatus)
    (t : CertificationStatus) : routeDebt c novelOpen s t = mathematicalDebt := by
  cases c <;> cases s <;> cases t <;> rfl

/-! ## 2.  Receipts, and the firewall as a theorem -/

/-- Agda `SourceIdentity`. -/
structure SourceIdentity where
  responsibleBody : String
  title : String
  stableIdentifier : String
  exactCarrier : String
  inspectedRevisionOrDate : String

/-- Agda `StatementAlignmentReceipt`. -/
structure StatementAlignmentReceipt where
  exactSourceClaim : String
  exactLocalStatement : String
  hypothesesAligned : Bool
  quantifiersAligned : Bool
  domainAligned : Bool
  uniformityAligned : Bool
  conclusionDirectionAligned : Bool
  allRequiredCoordinatesAligned : Bool

/-- Agda `FullyAligned`. -/
structure FullyAligned (a : StatementAlignmentReceipt) : Prop where
  hypothesesOK : a.hypothesesAligned = true
  quantifiersOK : a.quantifiersAligned = true
  domainOK : a.domainAligned = true
  uniformityOK : a.uniformityAligned = true
  conclusionOK : a.conclusionDirectionAligned = true
  allCoordinatesOK : a.allRequiredCoordinatesAligned = true

/-- Agda `SourceAlignedDeferredTheorem`.  Note the parameter `T` is *phantom*:
the record contains provenance and alignment evidence and deliberately contains
no inhabitant of `T`. -/
structure SourceAlignedDeferredTheorem (T : Prop) where
  source : SourceIdentity
  alignment : StatementAlignmentReceipt
  alignmentVerified : FullyAligned alignment
  preferredBackend : PreferredBackend

/-- Agda `CertifiedKnownTheorem`: promotion requires an actual inhabitant. -/
structure CertifiedKnownTheorem (T : Prop) where
  deferredReceipt : SourceAlignedDeferredTheorem T
  theorem_ : T
  backend : PreferredBackend
  certification : CertificationStatus

/-- A fully aligned receipt can always be manufactured, for *any* proposition:
alignment is bookkeeping about statements, not evidence about truth. -/
def trivialReceipt (T : Prop) : SourceAlignedDeferredTheorem T where
  source :=
    { responsibleBody := "", title := "", stableIdentifier := "", exactCarrier := ""
      inspectedRevisionOrDate := "" }
  alignment :=
    { exactSourceClaim := "", exactLocalStatement := "", hypothesesAligned := true
      quantifiersAligned := true, domainAligned := true, uniformityAligned := true
      conclusionDirectionAligned := true, allRequiredCoordinatesAligned := true }
  alignmentVerified := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  preferredBackend := aristotleLean

/-- **The firewall, as a theorem.**  There is no function taking a
source-aligned deferred receipt to the theorem it is about.  The Agda owner
states this as a design comment; here it is proved, by manufacturing a receipt
for `False`.

Consequence for this project: no amount of provenance, source alignment,
authority record or Boolean ledger entry can pay a mathematical obligation.
Only an inhabitant of the proposition can. -/
theorem no_receipt_to_theorem :
    ¬ Nonempty (∀ T : Prop, SourceAlignedDeferredTheorem T → T) := by
  rintro ⟨f⟩
  exact f False (trivialReceipt False)

/-- The same statement in the form the router uses it: certification is
constructible exactly when a proof is supplied. -/
def certifyDeferred {T : Prop} (receipt : SourceAlignedDeferredTheorem T) (proof : T)
    (backendUsed : PreferredBackend) (status : CertificationStatus) :
    CertifiedKnownTheorem T :=
  ⟨receipt, proof, backendUsed, status⟩

/-- Conditional development is kernel-checkable without manufacturing `T`
(Agda `ConditionalDevelopment` / `runConditionalDevelopment`). -/
def runConditionalDevelopment {T R : Prop} (downstream : T → R) (thm : T) : R :=
  downstream thm

/-! ## 3.  The machine-aware scheduler, mirrored -/

/-- Agda `LocalResourceClass`. -/
inductive LocalResourceClass | constrained32GB | standardWorkstation | largeLocalMachine
  deriving DecidableEq, Repr

/-- Agda `ProofWorkload`. -/
inductive ProofWorkload | tinyGlue | moderateReplay | heavyReplay
  deriving DecidableEq, Repr

/-- Agda `SchedulerAction`. -/
inductive SchedulerAction
  | researchMathematics | auditTranscription | verifyEmpiricalEvidence
  | runLocalAgda | sendExternalLean | sendAristotleLean | alreadyClosed
  deriving DecidableEq, Repr

open LocalResourceClass ProofWorkload SchedulerAction

/-- Agda `scheduleAction`, clause for clause. -/
def scheduleAction : DebtClass → StatementStatus → LocalResourceClass → ProofWorkload →
    SchedulerAction
  | mathematicalDebt, _, _, _ => researchMathematics
  | transcriptionDebt, _, _, _ => auditTranscription
  | empiricalEvidenceDebt, _, _, _ => verifyEmpiricalEvidence
  | noDebt, _, _, _ => alreadyClosed
  | certificationDebt, notTranscribed, _, _ => auditTranscription
  | certificationDebt, transcribedUnaligned, _, _ => auditTranscription
  | certificationDebt, sourceAligned, constrained32GB, tinyGlue => runLocalAgda
  | certificationDebt, sourceAligned, constrained32GB, moderateReplay => sendExternalLean
  | certificationDebt, sourceAligned, constrained32GB, heavyReplay => sendAristotleLean
  | certificationDebt, sourceAligned, standardWorkstation, tinyGlue => runLocalAgda
  | certificationDebt, sourceAligned, standardWorkstation, moderateReplay => runLocalAgda
  | certificationDebt, sourceAligned, standardWorkstation, heavyReplay => sendExternalLean
  | certificationDebt, sourceAligned, largeLocalMachine, _ => runLocalAgda

/-- Agda `constrainedHeavyEstablishedReplayGoesToAristotle`. -/
theorem constrainedHeavyReplay_crosswalk :
    scheduleAction certificationDebt sourceAligned constrained32GB heavyReplay
      = sendAristotleLean := rfl

/-- Agda `constrainedMachineCannotReclassifyNovelMathematics`. -/
theorem resources_cannot_reclassify_novel_crosswalk :
    scheduleAction mathematicalDebt sourceAligned constrained32GB heavyReplay
      = researchMathematics := rfl

/-- Agda `unAlignedCertificationCannotBeDelegatedAsProofReplay`. -/
theorem unaligned_cannot_be_delegated_crosswalk :
    scheduleAction certificationDebt transcribedUnaligned constrained32GB heavyReplay
      = auditTranscription := rfl

/-- **Resource pressure is never epistemic.**  Whatever machine and workload are
recorded, a mathematical debt is scheduled as research: the scheduler has no
clause that can turn an open problem into a replay job. -/
theorem mathematicalDebt_never_delegated (s : StatementStatus) (r : LocalResourceClass)
    (w : ProofWorkload) : scheduleAction mathematicalDebt s r w = researchMathematics := by
  cases s <;> cases r <;> cases w <;> rfl

/-- And a novel open problem is *always* scheduled as research, through the whole
router: `routeDebt` then `scheduleAction`. -/
theorem novelOpen_always_researched (c : ClaimKind) (s : StatementStatus)
    (t : CertificationStatus) (r : LocalResourceClass) (w : ProofWorkload) :
    scheduleAction (routeDebt c novelOpen s t) s r w = researchMathematics := by
  rw [novelOpen_always_mathematicalDebt]
  exact mathematicalDebt_never_delegated s r w

end RequestProject.NavierStokes.ProofDebtRouter

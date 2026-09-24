import Integration.Levels

/-!
# The chemistry transition kernel: what it forbids, and what it leaves open

`Agda/DASHI/Chemistry/TransitionKernel.agda` (429 lines) is the chemistry lane's
central record.  Almost all of its fields are `String` carriers
(`geometryCarrier`, `guardExpression`, `stabilityCriterion`, …) or bare `Bool`
flags (`goalReachable`, `forbiddenRegionAvoided`, `obligationsDischarged`,
`reductionValidated`, `selectionValidated`, `nonemptyWindow`,
`elementConservationChecked`, …).  Four flags are different: they are pinned to
`false` by an accompanying equality field.

That split is the entire formal content of the module, and this file states it.

## What is proved

* `kernel_fail_closed` — **the four pinned flags are the theorem**: *every*
  inhabitant of the kernel record has `quantitativeParametersMeasured`,
  `wetLabValidationAccepted` and `molecularIdentityAuthority` equal to `false`,
  and every conservation certificate has `conservationPromoted` equal to
  `false`.  No instance of the kernel can assert measurement, wet-lab validation,
  molecular-identity authority, or promoted conservation.
* `goalReachable_underdetermined`, `obligationsDischarged_underdetermined`,
  `conservationChecked_underdetermined` — **the open sockets**: for *any*
  transition-system carrier value, two reachability problems exist that agree on
  the system and disagree on the flag.  So none of these flags is a function of
  the model it is attached to: as declared, they constrain nothing.
* `flag_determined_of_sound` — **the candidate bridge**, with its hypothesis
  written out: if a decision procedure `reach` is supplied and the flag is
  *sound* for it (`FlagSound`), then the flag becomes a function of the
  transition system.  The implication is proved here; the hypothesis
  `FlagSound` is exactly what the corpus does not supply, and supplying it is
  the obligation.
* `flagSound_not_automatic` — and the hypothesis is not free: there is a
  reachability problem and a procedure for which `FlagSound` fails.

## Claim boundary

`ReachabilityProblem`, `ConservationCertificate` and `ChemistryTransitionKernel`
here are the *record shapes* of the Agda module, with the `String` carriers
replaced by an abstract parameter.  Nothing in this file is a claim about
chemistry, reaction networks, conservation laws, measurement or any physical
process; the theorems are about `Bool`-valued fields of a record.
-/

namespace Integration.ChemistryKernelSocket

variable {S : Type}

/-! ## The record shapes -/

/-- The Bool-flag part of `ConservationCertificate`.  `conservationPromoted` is
pinned to `false`; the two "checked" flags are not pinned. -/
structure ConservationCertificate where
  /-- Whether all element balances were checked (unconstrained). -/
  allElementBalancesChecked : Bool
  /-- Whether all charge balances were checked (unconstrained). -/
  allChargeBalancesChecked : Bool
  /-- Whether conservation is promoted. -/
  conservationPromoted : Bool
  /-- Pinned to `false`. -/
  conservationPromotedIsFalse : conservationPromoted = false

/-- The Bool-flag part of `ReachabilityProblem`, over an abstract carrier `S`
standing for the transition-system data. -/
structure ReachabilityProblem (S : Type) where
  /-- The transition-system data. -/
  transitionSystem : S
  /-- Whether the goal is reachable (unconstrained). -/
  goalReachable : Bool
  /-- Whether the forbidden region is avoided (unconstrained). -/
  forbiddenRegionAvoided : Bool
  /-- Whether the obligations are discharged (unconstrained). -/
  obligationsDischarged : Bool

/-- The pinned part of `ChemistryTransitionKernel`. -/
structure ChemistryTransitionKernel (S : Type) where
  /-- The reachability problems the kernel carries. -/
  reachabilityProblems : List (ReachabilityProblem S)
  /-- The conservation certificate. -/
  conservation : ConservationCertificate
  /-- Whether quantitative parameters are measured. -/
  quantitativeParametersMeasured : Bool
  /-- Pinned to `false`. -/
  quantitativeParametersMeasuredIsFalse : quantitativeParametersMeasured = false
  /-- Whether wet-lab validation is accepted. -/
  wetLabValidationAccepted : Bool
  /-- Pinned to `false`. -/
  wetLabValidationAcceptedIsFalse : wetLabValidationAccepted = false
  /-- Whether the kernel claims molecular-identity authority. -/
  molecularIdentityAuthority : Bool
  /-- Pinned to `false`. -/
  molecularIdentityAuthorityIsFalse : molecularIdentityAuthority = false

/-! ## What the kernel forbids -/

/-- **Fail-closed.**  Every inhabitant of the kernel — not merely the canonical
one — has all four authority flags `false`. -/
theorem kernel_fail_closed (k : ChemistryTransitionKernel S) :
    k.quantitativeParametersMeasured = false ∧
    k.wetLabValidationAccepted = false ∧
    k.molecularIdentityAuthority = false ∧
    k.conservation.conservationPromoted = false :=
  ⟨k.quantitativeParametersMeasuredIsFalse, k.wetLabValidationAcceptedIsFalse,
   k.molecularIdentityAuthorityIsFalse, k.conservation.conservationPromotedIsFalse⟩

/-! ## What the kernel leaves open -/

/-- **`goalReachable` is an open socket**: for any transition system whatsoever,
both values of the flag are available, so the flag is not a function of the
system. -/
theorem goalReachable_underdetermined (s : S) :
    ∃ p q : ReachabilityProblem S,
      p.transitionSystem = q.transitionSystem ∧ p.goalReachable ≠ q.goalReachable :=
  ⟨⟨s, true, true, true⟩, ⟨s, false, true, true⟩, rfl, Bool.noConfusion⟩

/-- The same for `obligationsDischarged`. -/
theorem obligationsDischarged_underdetermined (s : S) :
    ∃ p q : ReachabilityProblem S,
      p.transitionSystem = q.transitionSystem ∧
        p.obligationsDischarged ≠ q.obligationsDischarged :=
  ⟨⟨s, true, true, true⟩, ⟨s, true, true, false⟩, rfl, Bool.noConfusion⟩

/-- The same for the conservation "checked" flags: pinning
`conservationPromoted` to `false` places no constraint on them. -/
theorem conservationChecked_underdetermined :
    ∃ c d : ConservationCertificate,
      c.conservationPromoted = d.conservationPromoted ∧
        c.allElementBalancesChecked ≠ d.allElementBalancesChecked :=
  ⟨⟨true, true, false, rfl⟩, ⟨false, true, false, rfl⟩, rfl, Bool.noConfusion⟩

/-! ## The candidate bridge -/

/-- The hypothesis the corpus does not supply: the flag agrees with a decision
procedure applied to the transition system. -/
def FlagSound (reach : S → Bool) (P : ReachabilityProblem S → Prop) : Prop :=
  ∀ p, P p → p.goalReachable = reach p.transitionSystem

/-- **The candidate bridge.**  Given a decision procedure and soundness of the
flag for it on a class `P` of problems, the flag *is* a function of the
transition system on that class.  The implication is proved; `FlagSound` is the
open obligation. -/
theorem flag_determined_of_sound {reach : S → Bool} {P : ReachabilityProblem S → Prop}
    (h : FlagSound reach P) {p q : ReachabilityProblem S} (hp : P p) (hq : P q)
    (hs : p.transitionSystem = q.transitionSystem) :
    p.goalReachable = q.goalReachable := by
  rw [h p hp, h q hq, hs]

/-- And the hypothesis is not free: soundness genuinely fails for some flag
assignment, so `flag_determined_of_sound` cannot be discharged by pure logic. -/
theorem flagSound_not_automatic (s : S) :
    ∃ (reach : S → Bool) (P : ReachabilityProblem S → Prop), ¬ FlagSound reach P := by
  refine ⟨fun _ => false, fun _ => True, ?_⟩
  intro h
  have := h ⟨s, true, true, true⟩ trivial
  exact Bool.noConfusion this

end Integration.ChemistryKernelSocket

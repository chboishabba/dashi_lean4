import Synthesis.RiemannPostMergeAnalyticMaxCut

/-!
# Improved zero-free half-plane donor audit

External source, pinned for attribution/provenance:

* Liu Baiying, `Improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis`,
  revision `46d612c2b63a163665ef560afca1965f7c8f434b`.
* The source replay document `README_on_lean.md` reports a strict Lean 4.34.1
  replay and exports `CombineV22.zeta_nonzero` for
  `Re(s) > 0.874957019420098946...`.
* The source explicitly does **not** claim RH or boundary nonvanishing.

This module does not copy or re-attribute that proof.  Instead it supplies an
exact conservative rational cap and least-privilege consumer compilers for the
live DASHI RH routes.  Any theorem asserting that an actual zeta zero satisfies
this cap remains an external/cross-prover attachment until the exact source
proof is imported or reconstructed on the DASHI proof graph.

The conservative cap is

```
beta <= 0.874958 = 437479/500000,
A = beta - 1/2 <= 187479/500000 = 0.374958 < 3/8.
```

The final strict inequality is useful wherever a live estimate is monotone in
the actual target/reflection displacement `A`.  It does **not** alter the
canonical local radius `eta0 = 1/(pi+1)` used by the A2 sixth/eighth leading
constant cut, so no A2 payment is booked merely from this donor.

The second part isolates the frontier question suggested by the external
optimality theorem.  Its optimality is scoped to its supplied positive/moment
estimate system.  A new same-object signed credit is therefore outside that
no-go.  Algebraically, every strictly positive signed credit moves a terminal
scalar strictly below the corresponding positive-system step.  The existence,
size and same-object validity of such a credit are still exactly the analytic
A1/A2/B obligations; this theorem does not manufacture them.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- Conservative rational upper cap, rounded *above* the externally reported
`0.874957019420098946...` bound. -/
def improvedZeroFreeSafeBeta : ℝ := (437479 : ℝ) / 500000

/-- Corresponding right-half target displacement cap `beta - 1/2`. -/
def improvedZeroFreeSafeHorizontalCap : ℝ :=
  improvedZeroFreeSafeBeta - (1 : ℝ) / 2

theorem improvedZeroFreeSafeHorizontalCap_eq :
    improvedZeroFreeSafeHorizontalCap = (187479 : ℝ) / 500000 := by
  norm_num [improvedZeroFreeSafeHorizontalCap, improvedZeroFreeSafeBeta]

theorem improvedZeroFreeSafeBeta_lt_sevenEighths :
    improvedZeroFreeSafeBeta < (7 : ℝ) / 8 := by
  norm_num [improvedZeroFreeSafeBeta]

theorem improvedZeroFreeSafeHorizontalCap_lt_threeEighths :
    improvedZeroFreeSafeHorizontalCap < (3 : ℝ) / 8 := by
  rw [improvedZeroFreeSafeHorizontalCap_eq]
  norm_num

/-- Scalar consumer for an exact external same-zeta attachment.  This is the
only logical content DASHI needs from the external zero-free theorem in order
to narrow a selected target displacement. -/
structure ImprovedZeroFreeTargetAttachment where
  beta : ℝ
  targetDisplacement : ℝ
  targetDisplacement_eq : targetDisplacement = beta - (1 : ℝ) / 2
  beta_le_safe : beta ≤ improvedZeroFreeSafeBeta
  sameZetaObject : Prop
  sameZetaObject_proof : sameZetaObject

/-- An attached target lies inside the conservative new horizontal cap. -/
theorem ImprovedZeroFreeTargetAttachment.targetDisplacement_le_safeHorizontalCap
    (D : ImprovedZeroFreeTargetAttachment) :
    D.targetDisplacement ≤ improvedZeroFreeSafeHorizontalCap := by
  rw [D.targetDisplacement_eq]
  unfold improvedZeroFreeSafeHorizontalCap
  linarith [D.beta_le_safe]

/-- Hence the old `3/8` target-radius endpoint is strictly improved. -/
theorem targetDisplacement_lt_threeEighths
    {A : ℝ}
    (hA : A ≤ improvedZeroFreeSafeHorizontalCap) :
    A < (3 : ℝ) / 8 := by
  exact lt_of_le_of_lt hA improvedZeroFreeSafeHorizontalCap_lt_threeEighths

/-- Generic monotone-consumer compiler.  Any live cost proved monotone in the
actual horizontal displacement may be evaluated at the smaller safe cap rather
than at `3/8`.  The required monotonicity theorem remains consumer-specific. -/
theorem monotoneTargetCost_le_safeCap
    (cost : ℝ → ℝ)
    (hmono : Monotone cost)
    {A : ℝ}
    (hA : A ≤ improvedZeroFreeSafeHorizontalCap) :
    cost A ≤ cost improvedZeroFreeSafeHorizontalCap :=
  hmono hA

/-- Same compiler all the way to the historical `3/8` envelope. -/
theorem monotoneTargetCost_lt_or_le_threeEighths
    (cost : ℝ → ℝ)
    (hmono : Monotone cost)
    {A : ℝ}
    (hA : A ≤ improvedZeroFreeSafeHorizontalCap) :
    cost A ≤ cost ((3 : ℝ) / 8) := by
  apply hmono
  exact le_of_lt (targetDisplacement_lt_threeEighths hA)

/-- Abstract external theorem attachment.  The foreign proof is intentionally
not represented by source metadata: a consumer must supply the actual theorem
term/transport giving `beta <= improvedZeroFreeSafeBeta` on the same zeta
object. -/
structure ImprovedZeroFreeExternalZetaDonor (Zero : Type*) where
  isNontrivialZero : Zero → Prop
  rightOfCriticalLine : Zero → Prop
  beta : Zero → ℝ
  sameZetaObject : Zero → Prop
  sameZetaObject_proof : ∀ rho, sameZetaObject rho
  beta_le_safe :
    ∀ rho, isNontrivialZero rho → rightOfCriticalLine rho →
      beta rho ≤ improvedZeroFreeSafeBeta

/-- Compile the external same-zeta theorem into the scalar target attachment
used by DASHI consumers. -/
def ImprovedZeroFreeExternalZetaDonor.targetAttachment
    {Zero : Type*}
    (D : ImprovedZeroFreeExternalZetaDonor Zero)
    (rho : Zero)
    (hzero : D.isNontrivialZero rho)
    (hright : D.rightOfCriticalLine rho) :
    ImprovedZeroFreeTargetAttachment where
  beta := D.beta rho
  targetDisplacement := D.beta rho - (1 : ℝ) / 2
  targetDisplacement_eq := rfl
  beta_le_safe := D.beta_le_safe rho hzero hright
  sameZetaObject := D.sameZetaObject rho
  sameZetaObject_proof := D.sameZetaObject_proof rho

/-- Hybrid terminal scalar retaining a new same-object signed credit rather than
forcing it through the external positive-envelope system. -/
def signedHybridStep (positiveSystemStep signedCredit : ℝ) : ℝ :=
  positiveSystemStep - signedCredit

/-- Any genuinely positive signed credit strictly improves the corresponding
positive-system scalar.  This is the exact algebraic test showing why an
optimality theorem *within the old positive estimate system* cannot by itself
rule out a new signed method. -/
theorem signedHybridStep_lt_positiveStep
    {positiveSystemStep signedCredit : ℝ}
    (hcredit : 0 < signedCredit) :
    signedHybridStep positiveSystemStep signedCredit < positiveSystemStep := by
  unfold signedHybridStep
  linarith

/-- If a positive-system bootstrap is at a fixed point `B`, any same-object
strictly positive signed credit moves the hybrid step below that fixed point.
This is deliberately only a one-step statement: no convergence to `1/2` is
inferred without a uniform analytic credit across the iteration. -/
theorem signedHybridBreaksPositiveFixedPoint
    {B signedCredit : ℝ}
    (hcredit : 0 < signedCredit) :
    signedHybridStep B signedCredit < B :=
  signedHybridStep_lt_positiveStep hcredit

/-- Source/provenance ledger.  Booleans here are documentary and do not create
proof authority. -/
structure ImprovedZeroFreeDonorAudit where
  sourceRepository : String
  sourceRevision : String
  sourceReplayDocument : String
  sourceExportedTheorem : String
  sourceReportedKernelReplay : Bool
  exactCrossProverTheoremImported : Bool
  safeRationalCapProvedHere : Bool
  g21DomainCanBeSharpenedConditionally : Bool
  canonicalA2Eta0Changed : Bool
  signedA1A2BProducerPaid : Bool
  signedHybridScalarCompilerPaid : Bool
  riemannHypothesisDerived : Bool

/-- Current fail-closed audit. -/
def improvedZeroFreeDonorAudit : ImprovedZeroFreeDonorAudit where
  sourceRepository :=
    "liubaiying101/Improved-zero-free-half-planes-for-the-quasi-Riemann-hypothesis"
  sourceRevision := "46d612c2b63a163665ef560afca1965f7c8f434b"
  sourceReplayDocument := "README_on_lean.md"
  sourceExportedTheorem := "CombineV22.zeta_nonzero"
  sourceReportedKernelReplay := true
  exactCrossProverTheoremImported := false
  safeRationalCapProvedHere := true
  g21DomainCanBeSharpenedConditionally := true
  canonicalA2Eta0Changed := false
  signedA1A2BProducerPaid := false
  signedHybridScalarCompilerPaid := true
  riemannHypothesisDerived := false

end Synthesis

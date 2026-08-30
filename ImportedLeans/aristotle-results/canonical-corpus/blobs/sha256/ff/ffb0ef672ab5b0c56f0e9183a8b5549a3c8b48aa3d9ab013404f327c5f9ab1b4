import Cuisine.ToneSeparation
import Cuisine.UmamiTransport

/-!
# Safety fields over the Monster base: the positive half of the tone bridge

`Cuisine.ToneSeparation` proves a negative: the fail-closed severity order of the
cuisine safety carrier admits no order-3 automorphism, so the *tone rotation* of
`Synthesis.ToneCore` does not transport to it.  That result is often over-read.
This file proves what *does* transport, which is a good deal.

* `severity_eq_zmod_val` — the fail-closed severity `verified < unknown <
  rejected` is exactly the canonical `ℤ/3` representative of the tone.  So the
  cuisine order is not an alien structure bolted onto a ternary carrier: it is
  the representative order of `ℤ/3` itself.
* `worst` — the fail-closed aggregation of verdicts is a commutative idempotent
  monoid with unit `verified` (`worst_comm`, `worst_assoc`, `worst_idem`,
  `worst_verified`), and it is exactly `max` of severities
  (`safetyLevel_worst`).
* `SafetyField := SSP → SafetyEvidence` — a verdict per supersingular prime, and
  `safetyFabric : SafetyField ≃ Fabric`: safety fields over the Monster base
  *are* hyperfabric sections.
* `doubtMask_eq_supportMask` — the "not verified" mask of a safety field is the
  support mask of its section, so safety fields land in the Monster mask fibre
  of `Synthesis.MonsterFibre`.
* `doubtMask_worstField` — **fail-closed aggregation is a semilattice
  homomorphism** onto the mask fibre (`OR` of masks).  Contrast
  `Synthesis.Hyperfabric.support_not_hom`: the ternary XOR does *not* descend to
  the mask layer, but the cuisine fail-closed join does.
* `dSafety`, `dSafety_eq_zero_iff`, `safety_projection_contractive` — the
  supplied Monster ultrametric and its contractive projection, pulled back to
  safety fields.  Honest caveat, proved: distance zero means *same doubt mask*,
  not equal field, because `unknown` and `rejected` share a mask
  (`dSafety_not_separating`).
* `safety_intensity_roundtrip` — composing with `Cuisine.UmamiTransport`: the
  doubt mask of a safety field is recovered from the cuisine intensity
  `maskIntensity (doubtMask s)`, i.e. safety data has an umami-arithmetic
  encoding whose hyperfabric shadow is the original doubt pattern.

Boundary: no empirical claim about food safety is made; `SafetyEvidence` is a
three-element set and everything below is a finite computation.
-/

namespace Cuisine.SafetyFabric

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.Base369 (TriTruth)
open AgdaMirror.MonsterOntos (SSP)
open Synthesis.ToneCore
open Synthesis.MonsterFibre
open Synthesis.Hyperfabric
open Cuisine.SensoryCore (SafetyEvidence)
open Cuisine.SensoryCore.SafetyEvidence
open Cuisine.ToneSeparation (safetyTritEquiv safetyLevel)
open Cuisine.UmamiTransport

/-! ## Severity is the `ℤ/3` representative -/

/-- **The fail-closed severity order is the representative order of `ℤ/3`.**
Transporting a verdict to the tone carrier and taking the canonical
representative returns exactly its severity. -/
theorem severity_eq_zmod_val (s : SafetyEvidence) :
    (toneZMod (safetyTritEquiv s)).val = safetyLevel s := by
  cases s <;> decide

theorem safetyLevel_le_iff (a b : SafetyEvidence) :
    safetyLevel a ≤ safetyLevel b ↔
      (toneZMod (safetyTritEquiv a)).val ≤ (toneZMod (safetyTritEquiv b)).val := by
  rw [severity_eq_zmod_val, severity_eq_zmod_val]

/-! ## Fail-closed aggregation -/

/-- The fail-closed aggregate of two verdicts: the worse one wins. -/
def worst : SafetyEvidence → SafetyEvidence → SafetyEvidence
  | safetyRejected, _ => safetyRejected
  | _, safetyRejected => safetyRejected
  | safetyUnknown, _ => safetyUnknown
  | _, safetyUnknown => safetyUnknown
  | safetyVerified, safetyVerified => safetyVerified

theorem worst_comm (a b : SafetyEvidence) : worst a b = worst b a := by
  cases a <;> cases b <;> rfl

theorem worst_assoc (a b c : SafetyEvidence) : worst (worst a b) c = worst a (worst b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem worst_idem (a : SafetyEvidence) : worst a a = a := by cases a <;> rfl

@[simp] theorem worst_verified (a : SafetyEvidence) : worst safetyVerified a = a := by
  cases a <;> rfl

/-- Fail-closed aggregation is the maximum of severities. -/
theorem safetyLevel_worst (a b : SafetyEvidence) :
    safetyLevel (worst a b) = max (safetyLevel a) (safetyLevel b) := by
  cases a <;> cases b <;> rfl

/-! ## Safety fields over the Monster prime base -/

/-- A safety field: one verdict per supersingular prime.  (The base is used here
purely as a fifteen-element index of lanes; see `Cuisine.NineSheet.sspToneTaste`
for its `3 · 5` shape.) -/
abbrev SafetyField := SSP → SafetyEvidence

/-- **Safety fields are hyperfabric sections.**  Pointwise transport along the
carrier bijection of `Cuisine.ToneSeparation`. -/
def safetyFabric : SafetyField ≃ Fabric :=
  Equiv.arrowCongr (Equiv.refl SSP) (safetyTritEquiv.trans tritToneEquiv.symm)

@[simp] theorem safetyFabric_apply (s : SafetyField) (p : SSP) :
    safetyFabric s p = tritToneEquiv.symm (safetyTritEquiv (s p)) := rfl

/-- The doubt mask of a safety field: the lanes whose verdict is not
`verified`. -/
def doubtMask (s : SafetyField) : MaskSSP := fun p => decide (s p ≠ safetyVerified)

/-- **The doubt mask is the support mask of the section.**  So safety fields
land in the Monster mask fibre, and inherit its geometry. -/
theorem doubtMask_eq_supportMask (s : SafetyField) :
    doubtMask s = supportMask (safetyFabric s) := by
  funext p
  cases h : s p <;> simp [doubtMask, supportMask, support, h] <;> decide

/-- Pointwise fail-closed aggregation of two safety fields. -/
def worstField (x y : SafetyField) : SafetyField := fun p => worst (x p) (y p)

/-- **Fail-closed aggregation is a semilattice homomorphism into the Monster
mask fibre.**  Compare `Synthesis.Hyperfabric.support_not_hom`: the ternary XOR
does not descend to masks, but this cuisine operation does. -/
theorem doubtMask_worstField (x y : SafetyField) :
    doubtMask (worstField x y) = fun p => (doubtMask x p || doubtMask y p) := by
  funext p
  cases hx : x p <;> cases hy : y p <;>
    simp [doubtMask, worstField, worst, hx, hy]

/-! ## The Monster ultrametric, pulled back to safety fields -/

/-- The Monster mask distance between the doubt patterns of two safety
fields. -/
def dSafety (x y : SafetyField) : ℕ := dSSP (doubtMask x) (doubtMask y)

/-- The supplied ultrametric, pulled back along the doubt mask. -/
def USafety : AgdaMirror.Ultrametric SafetyField :=
  Synthesis.MonsterFibre.Ultrametric.comap doubtMask USSP

@[simp] theorem USafety_d (x y : SafetyField) : USafety.d x y = dSafety x y := rfl

/-- Honest form of the identity of indiscernibles: distance zero means the same
doubt pattern. -/
theorem dSafety_eq_zero_iff (x y : SafetyField) :
    dSafety x y = 0 ↔ doubtMask x = doubtMask y :=
  dSSP_eq_zero_iff _ _

/-- ... and it is genuinely a pseudometric only: `unknown` and `rejected` are
distinct verdicts with the same doubt pattern. -/
theorem dSafety_not_separating :
    ∃ x y : SafetyField, x ≠ y ∧ dSafety x y = 0 := by
  refine ⟨fun _ => safetyUnknown, fun _ => safetyRejected, ?_, ?_⟩
  · intro h
    exact absurd (congrFun h SSP.p2) (by decide)
  · rw [dSafety_eq_zero_iff]
    funext p
    simp [doubtMask]

/-- **The supplied contractive projection, applied to cuisine safety data.**
For fields with distinct doubt patterns, the constant Monster projection
strictly decreases the distance. -/
theorem safety_projection_contractive (target : MaskSSP) {x y : SafetyField}
    (hxy : doubtMask x ≠ doubtMask y) :
    dSSP (projectSSP target (doubtMask x)) (projectSSP target (doubtMask y)) < dSafety x y :=
  projectSSP_contractive target hxy

/-! ## Composition with the umami transport -/

/-- **Safety data has an umami-arithmetic encoding.**  Encoding the doubt
pattern of a safety field as the cuisine intensity of its mask and transporting
that intensity back to the hyperfabric returns the original doubt pattern. -/
theorem safety_intensity_roundtrip (s : SafetyField) :
    supportMask (umamiFabric (maskIntensity (doubtMask s))) = doubtMask s :=
  supportMask_umamiFabric_maskIntensity _

/-- The arithmetic encoding is faithful on doubt patterns: different doubt
patterns get different intensities. -/
theorem safety_intensity_injective {x y : SafetyField}
    (h : maskIntensity (doubtMask x) = maskIntensity (doubtMask y)) :
    doubtMask x = doubtMask y :=
  maskIntensity_injective h

end Cuisine.SafetyFabric

import Cuisine.SafetyFabric
import Synthesis.DialecticTone

/-!
# The `369` carrier, cuisine severity, and why every fail-closed ladder has a
seam

The cuisine lane reaches `Base369` through
`SweetgrassCarrierSpine → SensibLawResidualLattice → Base369`, and
`SensibLawResidualLattice` is where the hexadic carrier `HexTruth` is actually
*used*: it is mapped onto a six-level residual chain and thence to a numeric
severity, with the rotation `rotateHex` compared against that severity.  This
file mirrors that content in Lean, proves the general fact behind it, and
connects it to the cuisine safety carrier.

* `SixResidualLevel`, `sixResidualSeverity`, `hexToSixResidual`, `hexSeverity`,
  `joinSixResidual` — faithful mirrors of the Agda declarations, with the
  distinctness (`sixResidualSeverity_injective`) and join law
  (`sixResidualSeverity_join`) the Agda module states for its four-level chain.
* `hexSeverity_rotate_le` — the five non-wrap steps of the Agda file
  (`rotateHex-nonwrap-severity-0 … -4`), as one statement.
* `hexSeverity_rotate_wrap` — the Agda `rotateHexWrapSeam`: the sixth step drops
  the severity back to `0`.
* `severity_const_of_monotone_perm` — **the general theorem**: for *any*
  permutation of a finite carrier and *any* `ℕ`-valued severity that never
  decreases along it, the severity is constant along the permutation.  Hence
  `exists_severity_seam`: a rotation of a carrier whose severity is not
  rotation-invariant must have a seam where severity drops.
  This is a single explanation for two facts the corpus records separately: the
  wrap seam of `hexSeverity`, and the cuisine result
  `Cuisine.ToneSeparation.no_order_three_monotone_selfmap`.
* `hexToSafety`, `hexToSafety_rotate` — the **positive** transport: the hexadic
  `Base369` carrier maps onto the cuisine safety verdicts, two-to-one and
  *rotation-equivariantly*, via the mod-3 descent of
  `Synthesis.DialecticTone.hexToTri`.  So the cuisine safety carrier really is a
  quotient of the `369` carrier as a rotational object; what fails, and provably
  must fail, is only compatibility with the fail-closed order.

Boundary: `Severity` here is a natural number and `HexTruth` a six-element set.
Nothing about law, evidence, or safety in the world is claimed.
-/

namespace Cuisine.SeveritySeam

open AgdaMirror.Base369 (HexTruth rotateHex TriTruth rotateTri)
open Synthesis.ToneCore
open Synthesis.DialecticTone (hexToTri hexToTri_rotate)
open Cuisine.SensoryCore (SafetyEvidence)
open Cuisine.SensoryCore.SafetyEvidence
open Cuisine.ToneSeparation (safetyTritEquiv safetyLevel safetyRotate)

instance : Fintype HexTruth :=
  ⟨{.h0, .h1, .h2, .h3, .h4, .h5}, fun x => by cases x <;> decide⟩

/-! ## Mirror of the SensibLaw six-level residual carrier -/

/-- Mirror of `DASHI.Interop.SensibLawResidualLattice.SixResidualLevel`. -/
inductive SixResidualLevel
  | exact6 | partial6 | underdetermined6 | noTypedMeet6 | scopeExceeded6 | contradiction6
  deriving DecidableEq, Fintype, Repr

open SixResidualLevel

/-- Mirror of `sixResidualSeverity`.  The severities are `0,1,2,3,4,9`. -/
def sixResidualSeverity : SixResidualLevel → ℕ
  | exact6 => 0
  | partial6 => 1
  | underdetermined6 => 2
  | noTypedMeet6 => 3
  | scopeExceeded6 => 4
  | contradiction6 => 9

/-- The six levels are distinct, as the Agda module proves for its four-level
chain. -/
theorem sixResidualSeverity_injective : Function.Injective sixResidualSeverity := by decide

/-- Mirror of `joinSixResidual`: the worse level wins. -/
def joinSixResidual (a b : SixResidualLevel) : SixResidualLevel :=
  if sixResidualSeverity a ≤ sixResidualSeverity b then b else a

/-- The join law the Agda module states for its chains. -/
theorem sixResidualSeverity_join (a b : SixResidualLevel) :
    sixResidualSeverity (joinSixResidual a b) =
      max (sixResidualSeverity a) (sixResidualSeverity b) := by
  cases a <;> cases b <;> decide

/-- Mirror of `hexToSixResidual`. -/
def hexToSixResidual : HexTruth → SixResidualLevel
  | .h0 => exact6 | .h1 => partial6 | .h2 => underdetermined6
  | .h3 => noTypedMeet6 | .h4 => scopeExceeded6 | .h5 => contradiction6

/-- Mirror of `hexSeverity`. -/
def hexSeverity (h : HexTruth) : ℕ := sixResidualSeverity (hexToSixResidual h)

/-- The hexadic carrier is faithfully graded: distinct positions, distinct
severities. -/
theorem hexSeverity_injective : Function.Injective hexSeverity := by decide

/-- The five non-wrap steps of the Agda file, in one statement. -/
theorem hexSeverity_rotate_le (h : HexTruth) (hne : h ≠ .h5) :
    hexSeverity h ≤ hexSeverity (rotateHex h) := by
  cases h <;> simp_all [hexSeverity, hexToSixResidual, sixResidualSeverity, rotateHex]

/-- The Agda `rotateHexWrapSeam`: the sixth step returns to severity `0`. -/
theorem hexSeverity_rotate_wrap : hexSeverity (rotateHex .h5) = 0 := rfl

/-- ... and it is a genuine drop. -/
theorem hexSeverity_seam : hexSeverity (rotateHex .h5) < hexSeverity .h5 := by decide

/-! ## Why the seam is unavoidable -/

/-- **General theorem.**  If a natural-number severity never decreases along a
permutation of a finite carrier, then it is constant along that permutation.
(Proof: the two sums agree by reindexing, and a pointwise-`≤` family with equal
sums is pointwise equal.) -/
theorem severity_const_of_monotone_perm {C : Type} [Fintype C] [DecidableEq C]
    (σ : C ≃ C) (sev : C → ℕ) (h : ∀ c, sev c ≤ sev (σ c)) (c : C) :
    sev (σ c) = sev c := by
  have hsum : ∑ x : C, sev (σ x) = ∑ x : C, sev x := Equiv.sum_comp σ sev
  have hle : ∀ x ∈ (Finset.univ : Finset C), sev x ≤ sev (σ x) := fun x _ => h x
  have := (Finset.sum_eq_sum_iff_of_le hle).mp hsum.symm
  exact (this c (Finset.mem_univ c)).symm

/-- **Corollary: fail-closed ladders have seams.**  If a severity on a finite
carrier is not invariant under a rotation, then the rotation must somewhere
decrease it.  The `hexSeverity` wrap seam and the cuisine impossibility result
are the two instances of this in the corpus. -/
theorem exists_severity_seam {C : Type} [Fintype C] [DecidableEq C]
    (σ : C ≃ C) (sev : C → ℕ) (hne : ∃ c, sev (σ c) ≠ sev c) :
    ∃ c, sev (σ c) < sev c := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc⟩ := hne
  exact hc (severity_const_of_monotone_perm σ sev (fun x => hcon x) c)

/-- `rotateHex` as a permutation of the hexadic carrier. -/
def rotateHexEquiv : HexTruth ≃ HexTruth where
  toFun := rotateHex
  invFun h := rotateHex (rotateHex (rotateHex (rotateHex (rotateHex h))))
  left_inv h := by cases h <;> rfl
  right_inv h := by cases h <;> rfl

/-- The hexadic instance: `rotateHex` is a permutation and `hexSeverity` is not
constant along it, so a seam must exist — and the Agda file's
`rotateHexWrapSeam` exhibits it. -/
theorem hex_seam_from_general :
    ∃ h : HexTruth, hexSeverity (rotateHex h) < hexSeverity h :=
  exists_severity_seam rotateHexEquiv hexSeverity ⟨.h0, by decide⟩

/-- The transported tone rotation as a permutation of the safety carrier. -/
def safetyRotateEquiv : SafetyEvidence ≃ SafetyEvidence where
  toFun := safetyRotate
  invFun s := safetyRotate (safetyRotate s)
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl

/-- The cuisine instance of the same argument, for the transported tone
rotation of `Cuisine.ToneSeparation`. -/
theorem safety_seam_from_general :
    ∃ s : SafetyEvidence, safetyLevel (safetyRotate s) < safetyLevel s :=
  exists_severity_seam safetyRotateEquiv safetyLevel ⟨safetyVerified, by decide⟩

/-! ## The positive transport: `369` onto the cuisine safety carrier -/

/-- The hexadic `Base369` carrier mapped onto cuisine safety verdicts, through
the mod-3 descent `Synthesis.DialecticTone.hexToTri`. -/
def hexToSafety (h : HexTruth) : SafetyEvidence := safetyTritEquiv.symm (hexToTri h)

/-- **Rotation equivariance.**  One `rotateHex` step of the `369` carrier is one
tone step of the cuisine safety carrier.  So the safety carrier *is* a quotient
of the hexadic carrier as a rotational object — the positive counterpart of
`Cuisine.ToneSeparation.no_order_three_monotone_selfmap`, which says only that
this rotation cannot also respect the fail-closed order. -/
theorem hexToSafety_rotate (h : HexTruth) :
    hexToSafety (rotateHex h) = safetyRotate (hexToSafety h) := by
  cases h <;> rfl

/-- The transport is onto, and exactly two-to-one. -/
theorem hexToSafety_surjective : Function.Surjective hexToSafety := by
  intro s; cases s
  · exact ⟨.h0, rfl⟩
  · exact ⟨.h1, rfl⟩
  · exact ⟨.h2, rfl⟩

theorem hexToSafety_fibre_card (s : SafetyEvidence) :
    (Finset.univ.filter (fun h : HexTruth => hexToSafety h = s)).card = 2 := by
  cases s <;> decide

/-- The two gradings agree modulo three at every hexadic position except the
last: the cuisine severity of a position is its SensibLaw residual severity
reduced mod 3. -/
theorem safetyLevel_hexToSafety (h : HexTruth) (hne : h ≠ .h5) :
    safetyLevel (hexToSafety h) = hexSeverity h % 3 := by
  cases h <;> simp_all [safetyLevel, hexToSafety, hexSeverity, hexToSixResidual,
    sixResidualSeverity, safetyTritEquiv, hexToTri]

/-- ... and it fails exactly at the wrap position, because the residual ladder
jumps from `4` to `9` there rather than to `5`.  The seam of
`hexSeverity_seam` is the same defect seen through the mod-3 descent. -/
theorem safetyLevel_hexToSafety_wrap :
    safetyLevel (hexToSafety .h5) ≠ hexSeverity .h5 % 3 := by decide

end Cuisine.SeveritySeam

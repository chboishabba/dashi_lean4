import Synthesis.MonsterVacuumHomEquivalence

/-!
# Signed same-object Hom and finite-copy composition

Consumes the original weight frame and Weyl Hom equivalence. A normalizer
arrow can change the marked phase; its two E-actions need not be equal.
Derive the transported Hom, vacuum arrow and its factorization on every
basis weight, rather than requiring an independent multiplicity action.
Source-written; actual Conway/ATLAS/character inhabitants and kernel
acceptance are separate.
-/

namespace Synthesis.MonsterSignedHomComposition

noncomputable section
open Synthesis.MonsterWeightFrame
open Synthesis.MonsterVacuumHomEquivalence
open Synthesis.MonsterNormalizerHomAction

universe u
variable {k E S T W U ι : Type u}
variable [Field k] [Group E] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
variable [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable (F : Frame (k := k) (S := S) (W := W) (ι := ι))
variable (G : Frame (k := k) (S := T) (W := U) (ι := ι))
variable (A : EActionPair (k := k) (E := E) (H := Schr k ι) (W := W))
variable (B : EActionPair (k := k) (E := E) (H := Schr k ι) (W := U))

/-- Actual cross-phase analogue of NormalizerLift. -/
structure SignedArrow where
  conjugate : E → E
  surjective : Function.Surjective conjugate
  onH : Schr k ι ≃ₗ[k] Schr k ι
  onW : W ≃ₗ[k] U
  covH : ∀ e x, onH (A.actH e x) = B.actH (conjugate e) (onH x)
  covW : ∀ e w, onW (A.actW e w) = B.actW (conjugate e) (onW w)

variable (R : SignedArrow A B)

def homArrow (f : homSubmodule A) : homSubmodule B := by
  refine ⟨R.onW.toLinearMap.comp (f.1.comp R.onH.symm.toLinearMap), ?_⟩
  intro e x
  obtain ⟨e₀, rfl⟩ := R.surjective e
  have h : R.onH.symm (B.actH (R.conjugate e₀) x) =
      A.actH e₀ (R.onH.symm x) := by
    apply R.onH.injective
    simpa using (R.covH e₀ (R.onH.symm x)).symm
  change B.actW (R.conjugate e₀) (R.onW (f.1 (R.onH.symm x))) =
    R.onW (f.1 (R.onH.symm (B.actH (R.conjugate e₀) x)))
  rw [h, ← f.2 e₀]
  exact (R.covW e₀ _).symm

theorem homArrow_apply (f : homSubmodule A) (x : Schr k ι) :
    (homArrow A B R f).1 x = R.onW (f.1 (R.onH.symm x)) := rfl

variable (L : WeylVacuumLaws F A) (M : WeylVacuumLaws G B)

def vacuumArrow (u : S) : T :=
  homToVacuum G B M (homArrow A B R (vacuumToHom F A L u))

/-- No independent Hom gauge is needed for a phase-changing arrow. -/
theorem eval_covariance (u : S) (x : Schr k ι) :
    vacuumEval G (vacuumArrow F G A B R L M u) (R.onH x) =
      R.onW (vacuumEval F u x) := by
  have h := vacuum_hom_inverse G B M (homArrow A B R (vacuumToHom F A L u))
  have he := congrArg (fun f : homSubmodule B => f.1 (R.onH x)) h
  change vacuumEval G (vacuumArrow F G A B R L M u) (R.onH x) =
    R.onW (vacuumEval F u (R.onH.symm (R.onH x))) at he
  simpa only [LinearEquiv.symm_apply_apply] using he

/-- Linear conjugation on the actual Hom submodules. -/
def homLinearArrow : homSubmodule A →ₗ[k] homSubmodule B where
  toFun := homArrow A B R
  map_add' := by
    intro f g
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change R.onW (f.1 (R.onH.symm x) + g.1 (R.onH.symm x)) =
      R.onW (f.1 (R.onH.symm x)) + R.onW (g.1 (R.onH.symm x))
    exact R.onW.map_add _ _
  map_smul' := by
    intro c f
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change R.onW (c • f.1 (R.onH.symm x)) =
      c • R.onW (f.1 (R.onH.symm x))
    exact R.onW.map_smul _ _

/-- The signed multiplicity arrow is the composite of actual linear Hom
identification, conjugation, and actual vacuum recovery. -/
def vacuumLinearArrow : S →ₗ[k] T :=
  (vacuumHomLinearEquiv G B M).symm.toLinearMap.comp
    ((homLinearArrow A B R).comp (vacuumHomLinearEquiv F A L).toLinearMap)

theorem vacuumLinearArrow_apply (u : S) :
    vacuumLinearArrow F G A B R L M u = vacuumArrow F G A B R L M u := rfl

/-- Derive the literal kernel entry law from the existing Hom equivalence. -/
theorem basis_entry (i j : ι) (u : S) :
    G.recoverWeight j (R.onW (F.includeWeight i u)) =
      (R.onH (delta i) j) • vacuumArrow F G A B R L M u := by
  rw [← vacuumEval_delta F u i, ← eval_covariance F G A B R L M]
  change recover G (evaluate G (fun x =>
    R.onH (delta i) x • vacuumArrow F G A B R L M u)) j = _
  rw [recover_evaluate]

/-- Full vectors, not just pure tensors. The coordinate action is the
Weil kernel times the derived vacuum arrow, summed over all weights. -/
theorem full_entry (u : ι → S) (j : ι) :
    transport F G R.onW.toLinearMap u j =
      ∑ i, (R.onH (delta i) j) • vacuumArrow F G A B R L M (u i) := by
  rw [transport_entry]
  apply Finset.sum_congr rfl
  intro i _
  exact basis_entry F G A B R L M i j (u i)

end
end Synthesis.MonsterSignedHomComposition

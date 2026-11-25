import Synthesis.MonsterSignedHomComposition
import Mathlib.LinearAlgebra.Trace

/-!
# Honest multiplicity representation and its actual trace

This closes the generic law/trace seam on the same frame and derived Hom.
The character is defined by the trace of that representation, not a separately
supplied function called trace. Only the external original character
identification remains a source premise. The actual H0/Conway instance and
field descent of the character-isomorphism theorem are not claimed here.
-/
namespace Synthesis.MonsterActualMultiplicityCharacter
noncomputable section
open Synthesis.MonsterWeightFrame
open Synthesis.MonsterVacuumHomEquivalence
open Synthesis.MonsterNormalizerHomAction
open Synthesis.MonsterSignedHomComposition

universe u
variable {k E S W ι N : Type u}
variable [Field k] [Group E] [Group N] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup S] [Module k S] [AddCommGroup W] [Module k W]
variable (F : Frame (k := k) (S := S) (W := W) (ι := ι))
variable (A : EActionPair (k := k) (E := E) (H := Schr k ι) (W := W))
variable (L : WeylVacuumLaws F A)

theorem vacuumEval_injective (u v : S)
    (h : ∀ x, vacuumEval F u x = vacuumEval F v x) : u = v := by
  have h0 := congrArg (F.recoverWeight L.origin) (h (delta L.origin))
  simpa only [vacuumEval_delta, F.orthogonal, if_pos rfl] using h0

/-- Supply honest inner arrows of the original H0 action. Their covariance
is the signed Weil/Conway source law; do not require separate Hom action laws. -/
structure HonestInnerArrows where
  arrow : N → SignedArrow A A
  oneH : ∀ x, (arrow 1).onH x = x
  oneW : ∀ w, (arrow 1).onW w = w
  mulH : ∀ a b x, (arrow (a*b)).onH x = (arrow a).onH ((arrow b).onH x)
  mulW : ∀ a b w, (arrow (a*b)).onW w = (arrow a).onW ((arrow b).onW w)

variable (D : HonestInnerArrows (N := N) A)

theorem vacuum_one (u : S) :
    vacuumArrow F F A A (D.arrow 1) L L u = u := by
  apply vacuumEval_injective F A L
  intro x
  have h := eval_covariance F F A A (D.arrow 1) L L u x
  rw [D.oneH, D.oneW] at h
  exact h

theorem vacuum_mul (a b : N) (u : S) :
    vacuumArrow F F A A (D.arrow (a*b)) L L u =
      vacuumArrow F F A A (D.arrow a) L L
        (vacuumArrow F F A A (D.arrow b) L L u) := by
  apply vacuumEval_injective F A L
  intro x
  obtain ⟨y, rfl⟩ := (D.arrow (a*b)).onH.surjective x
  calc
    _ = (D.arrow (a*b)).onW (vacuumEval F u y) :=
      eval_covariance F F A A (D.arrow (a*b)) L L u y
    _ = (D.arrow a).onW ((D.arrow b).onW (vacuumEval F u y)) :=
      D.mulW a b _
    _ = (D.arrow a).onW (vacuumEval F
          (vacuumArrow F F A A (D.arrow b) L L u) ((D.arrow b).onH y)) :=
      congrArg (D.arrow a).onW
        (eval_covariance F F A A (D.arrow b) L L u y).symm
    _ = vacuumEval F
          (vacuumArrow F F A A (D.arrow a) L L
            (vacuumArrow F F A A (D.arrow b) L L u))
          ((D.arrow a).onH ((D.arrow b).onH y)) :=
      (eval_covariance F F A A (D.arrow a) L L
        (vacuumArrow F F A A (D.arrow b) L L u) ((D.arrow b).onH y)).symm
    _ = _ := by rw [D.mulH]

/-- The multiplicity representation is derived from actual original arrows. -/
def actualMultiplicity : N →* Module.End k S where
  toFun g := vacuumLinearArrow F F A A (D.arrow g) L L
  map_one' := by
    apply LinearMap.ext
    intro u
    change vacuumArrow F F A A (D.arrow 1) L L u = u
    exact vacuum_one F A L D u
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    change vacuumArrow F F A A (D.arrow (a*b)) L L u =
      vacuumArrow F F A A (D.arrow a) L L
        (vacuumArrow F F A A (D.arrow b) L L u)
    exact vacuum_mul F A L D a b u

variable [FiniteDimensional k S]

/-- Unlike a bare `Set` or named function, this is the actual operator trace. -/
def actualCharacter (g : N) : k :=
  LinearMap.trace k S (actualMultiplicity F A L D g)

/-- The precisely typed residual source obligation for the 12+78 theorem.
The two source characters must be attached to this marked H0 and phase. -/
def SameSourceCharacter (c12 c78 : N → k) : Prop :=
  ∀ g, actualCharacter F A L D g = c12 g + c78 g

end
end Synthesis.MonsterActualMultiplicityCharacter

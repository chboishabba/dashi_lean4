import Synthesis.MonsterTensorEvaluationFiniteCopies
import Synthesis.MonsterNormalizerHomAction
import Mathlib

/-!
# Actual weight-resolution to linear finite copies

The original Weyl projectors supply inclusion T_x and recovery T_x^-1 Pi_x
on the SAME actual vacuum S and sector W. No basis permutation or pure tensor
pair inverse is used. Orthogonality and completeness are explicit source
inputs; both linear inverses and the transported operator law are outputs.
The source-bound Monster instance is not produced merely by this compiler.
-/

namespace Synthesis.MonsterWeightFrame
noncomputable section

universe u v
variable {k S W : Type u} {ι : Type v}
variable [Field k] [AddCommGroup S] [Module k S]
variable [AddCommGroup W] [Module k W] [Fintype ι] [DecidableEq ι]

structure Frame where
  includeWeight : ι → S →ₗ[k] W
  recoverWeight : ι → W →ₗ[k] S
  orthogonal : ∀ i j x, recoverWeight i (includeWeight j x) =
    if i = j then x else 0
  complete : ∀ w, (∑ i, includeWeight i (recoverWeight i w)) = w

def evaluate (F : Frame (k := k) (S := S) (W := W) (ι := ι)) :
    (ι → S) →ₗ[k] W where
  toFun x := ∑ i, F.includeWeight i (x i)
  map_add' := by
    intro x y
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [Finset.smul_sum]

def recover (F : Frame (k := k) (S := S) (W := W) (ι := ι)) :
    W →ₗ[k] (ι → S) where
  toFun w i := F.recoverWeight i w
  map_add' := by
    intro x y
    funext i
    exact (F.recoverWeight i).map_add x y
  map_smul' := by
    intro c x
    funext i
    exact (F.recoverWeight i).map_smul c x

theorem recover_evaluate (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (x : ι → S) : recover F (evaluate F x) = x := by
  funext i
  change F.recoverWeight i (∑ j, F.includeWeight j (x j)) = x i
  rw [map_sum]
  simp [F.orthogonal]

theorem evaluate_recover (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (w : W) : evaluate F (recover F w) = w :=
  F.complete w

def linearEquiv (F : Frame (k := k) (S := S) (W := W) (ι := ι)) :
    (ι → S) ≃ₗ[k] W :=
  { evaluate F with
    invFun := recover F
    left_inv := recover_evaluate F
    right_inv := evaluate_recover F }

variable {S' W' : Type u} {κ : Type v}
variable [AddCommGroup S'] [Module k S']
variable [AddCommGroup W'] [Module k W'] [Fintype κ] [DecidableEq κ]

/-- An operator between marked sectors, not necessarily an endomorphism. -/
def transport (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (G : Frame (k := k) (S := S') (W := W') (ι := κ))
    (g : W →ₗ[k] W') : (ι → S) →ₗ[k] (κ → S') :=
  (recover G).comp (g.comp (evaluate F))

theorem transport_intertwines
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (G : Frame (k := k) (S := S') (W := W') (ι := κ))
    (g : W →ₗ[k] W') (x : ι → S) :
    evaluate G (transport F G g x) = g (evaluate F x) :=
  evaluate_recover G (g (evaluate F x))

theorem transport_entry
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (G : Frame (k := k) (S := S') (W := W') (ι := κ))
    (g : W →ₗ[k] W') (x : ι → S) (j : κ) :
    transport F G g x j =
      ∑ i, G.recoverWeight j (g (F.includeWeight i (x i))) := by
  change G.recoverWeight j (g (∑ i, F.includeWeight i (x i))) = _
  rw [map_sum, map_sum]

theorem transport_roundtrip
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (G : Frame (k := k) (S := S') (W := W') (ι := κ))
    (g : W ≃ₗ[k] W') (x : ι → S) :
    transport G F g.symm.toLinearMap (transport F G g.toLinearMap x) = x := by
  change recover F (g.symm (evaluate G (transport F G g.toLinearMap x))) = x
  rw [transport_intertwines]
  simp only [LinearEquiv.toLinearMap_apply, LinearEquiv.symm_apply_apply]
  exact recover_evaluate F x

end
end Synthesis.MonsterWeightFrame

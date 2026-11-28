import Mathlib
import Welds.PNPF3SyndromeBoundaryExact

namespace PNPF3CollectiveNormal

open PNPF3SyndromeBoundary

-- Two restrictions can be glued only when they agree on the ENTIRE
-- collective intersection, not on individual factor pairs.
theorem glueValue {r : Nat} (U V : Submodule (ZMod 3) (Syndrome r))
    (f g : Syndrome r →ₗ[ZMod 3] ZMod 3)
    (agree : ∀ x, x ∈ U → x ∈ V → f x = g x)
    (a a' b b' : Syndrome r) (ha : a ∈ U) (ha' : a' ∈ U)
    (hb : b ∈ V) (hb' : b' ∈ V) (eq : a+b = a'+b') :
    f a+g b = f a'+g b' := by
  have e : a-a' = b'-b := by
    calc
      a-a' = (a+b)-(a'+b) := by abel
      _ = (a'+b')-(a'+b) := by rw [eq]
      _ = b'-b := by abel
  have he := agree (a-a') (U.sub_mem ha ha') (by rw [e]; exact V.sub_mem hb' hb)
  have he' : f (a-a') = g (b'-b) := he.trans (congrArg g e)
  simp only [map_sub] at he'
  calc
    f a+g b = (f a-f a')+(f a'+g b) := by abel
    _ = (g b'-g b)+(f a'+g b) := by rw [he']
    _ = f a'+g b' := by abel

-- Local agreement on pairwise intersections is not sufficient:
-- e1,e2,e1+e2 have pairwise zero intersections, yet the three
-- local values are constrained by one collective linear dependence.
theorem collective_relation (f : Syndrome 2 →ₗ[ZMod 3] ZMod 3)
    (a b : Syndrome 2) : f (a+b) = f a+f b := map_add f a b

-- Correct sufficient stopping rule: the retained direction itself
-- must pay the full directional error, including the factor of two.
theorem stop_direction (head actual radius eps : ℚ)
    (error : head-radius ≤ actual) (ready : -eps ≤ head-radius) :
    -eps ≤ actual := ready.trans error

theorem zero_sum_small_tail (a b c radius eps : ℚ)
    (h : a+b+c=0) (hr : radius ≤ eps) :
    -eps ≤ a-radius ∨ -eps ≤ b-radius ∨ -eps ≤ c-radius := by
  by_cases ha : 0 ≤ a
  · exact Or.inl (by linarith)
  by_cases hb : 0 ≤ b
  · exact Or.inr (Or.inl (by linarith))
  exact Or.inr (Or.inr (by linarith))

-- Explicit countercontrol to the weaker amplitude-only test:
-- H=(0,4,4), |character|=4, E=3, w=1, eps=1/8.
theorem amplitude_threshold_insufficient :
    (4:ℚ) > 3+1/8 ∧
    (-8:ℚ)-2*3 < -1/8 ∧ (4:ℚ)-2*3 < -1/8 := by norm_num

end PNPF3CollectiveNormal

namespace PNPCutRankFirewall

-- Full communication rank over F2 is compatible with a linear
-- equality circuit. Equality's matrix is literally the identity.
def equalityMatrix (n : Nat) : Matrix (Fin n → Bool) (Fin n → Bool) (ZMod 2) :=
  fun x y => if x=y then 1 else 0

theorem equalityMatrix_one (n : Nat) : equalityMatrix n = 1 := by
  classical
  ext x y
  simp [equalityMatrix, Matrix.one_apply]

theorem equalityMatrix_det (n : Nat) : (equalityMatrix n).det = 1 := by
  rw [equalityMatrix_one, Matrix.det_one]

end PNPCutRankFirewall

namespace PNPGuardedTranslation

-- Compose two already discovered, selected blocks. The requirement
-- transport pays the original first block's displacement.
theorem displacement_append (a b : List Rule) :
    displacement (a++b) = displacement a+displacement b := by
  induction a with
  | nil => simp [displacement]
  | cons x xs ih =>
    rcases x with ⟨g,d⟩
    simp only [List.cons_append,displacement,ih]
    ring

theorem need_append (a b : List Rule) :
    need (a++b) = max (need a) (need b-displacement a) := by
  induction a with
  | nil => simp [need,displacement]
    have h : 0 ≤ need b := by
      cases b with
      | nil => simp [need]
      | cons x xs => rcases x with ⟨g,d⟩; simp only [need]; exact le_max_left _ _
    omega
  | cons x xs ih =>
    rcases x with ⟨g,d⟩
    simp only [List.cons_append,need,displacement,ih]
    omega

-- A higher-priority guard dominated by another forbidden guard is
-- redundant. This applies to each integer repetition independently.
theorem dominated_guard {ι : Type*} (v a b : ι → ℤ)
    (h : ∀ i, a i ≤ b i) :
    (∀ i, b i ≤ v i) → (∀ i, a i ≤ v i) :=
  fun hb i => (h i).trans (hb i)

end PNPGuardedTranslation

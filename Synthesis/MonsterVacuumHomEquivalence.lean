import Synthesis.MonsterWeightFrame
import Synthesis.MonsterNormalizerHomAction

/-!
The actual Heisenberg multiplicity Hom is the vacuum, not an arbitrary set
called Hom. This compiler consumes the existing linear weight frame and the
Weyl translation/modulation laws on the SAME E-action. It derives the Hom
submodule and its linear inverse. Actual Monster source inhabitants remain
separate. No finite basis-label identification of arbitrary vectors.
-/
namespace Synthesis.MonsterVacuumHomEquivalence

noncomputable section
open Synthesis.MonsterWeightFrame
open Synthesis.MonsterNormalizerHomAction
universe u
variable {k E S W ι : Type u}
variable [Field k] [Group E] [AddCommGroup S] [Module k S]
variable [AddCommGroup W] [Module k W] [Fintype ι] [DecidableEq ι]

abbrev Schr (k ι : Type u) := ι → k

def delta (i : ι) : Schr k ι := fun j => if j = i then 1 else 0

theorem delta_expansion (h : Schr k ι) :
    (∑ i, h i • delta (k := k) i) = h := by
  funext j
  change (∑ i, h i * (if j = i then 1 else 0)) = h j
  calc
    _ = h j * (if j = j then 1 else 0) :=
      Finset.sum_eq_single j
        (by intro i _ hij; simp [Ne.symm hij])
        (by simp)
    _ = h j := by simp

theorem linear_ext_delta (f g : Schr k ι →ₗ[k] W)
    (h : ∀ i, f (delta i) = g (delta i)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [← delta_expansion x, map_sum, map_sum]
  simp only [map_smul, h]

variable (F : Frame (k := k) (S := S) (W := W) (ι := ι))

def vacuumEval (u : S) : Schr k ι →ₗ[k] W where
  toFun h := evaluate F (fun i => h i • u)
  map_add' := by
    intro x y
    rw [← map_add]
    congr 1
    funext i
    exact add_smul (x i) (y i) u
  map_smul' := by
    intro c x
    rw [← map_smul]
    congr 1
    funext i
    exact mul_smul c (x i) u

theorem vacuumEval_delta (u : S) (i : ι) :
    vacuumEval F u (delta i) = F.includeWeight i u := by
  change (∑ j, F.includeWeight j ((if j = i then 1 else 0) • u)) = _
  calc
    _ = F.includeWeight i ((if i = i then 1 else 0) • u) :=
      Finset.sum_eq_single i
        (by intro j _ hji; simp [hji])
        (by simp)
    _ = _ := by simp

variable (A : EActionPair (k := k) (E := E) (H := Schr k ι) (W := W))

/-- Exact geometry-facing source obligations. Translation sends the marked
basis vector to each weight, and separating modulations fix that basis vector
while acting by a nonunit character on any other weight. The basis action
formula is the literal Weyl covariance on the existing actual frame. -/
structure WeylVacuumLaws where
  origin : ι
  translate : ι → E
  translates_basis : ∀ i, A.actH (translate i) (delta origin) = delta i
  translates_vacuum : ∀ i u,
    A.actW (translate i) (F.includeWeight origin u) = F.includeWeight i u
  separate : ∀ i, i ≠ origin → ∃ (e : E) (a : k),
    a ≠ 1 ∧ A.actH e (delta origin) = delta origin ∧
      ∀ w, F.recoverWeight i (A.actW e w) = a • F.recoverWeight i w
  basis_covariance : ∀ e i u,
    A.actW e (F.includeWeight i u) = vacuumEval F u (A.actH e (delta i))

/-- The actual equivariant Hom carrier as a linear submodule. -/
def homSubmodule : Submodule k (Schr k ι →ₗ[k] W) where
  carrier := { f | ∀ e x, A.actW e (f x) = f (A.actH e x) }
  zero_mem' := by
    intro e x
    simp
  add_mem' := by
    intro f g hf hg e x
    change A.actW e (f x + g x) = f (A.actH e x) + g (A.actH e x)
    rw [map_add, hf e x, hg e x]
  smul_mem' := by
    intro c f hf e x
    change A.actW e (c • f x) = c • f (A.actH e x)
    rw [map_smul, hf e x]

variable (L : WeylVacuumLaws F A)

def vacuumToHom (u : S) : homSubmodule A := by
  refine ⟨vacuumEval F u, ?_⟩
  intro e x
  have h : (A.actW e).comp (vacuumEval F u) =
      (vacuumEval F u).comp (A.actH e) := by
    apply linear_ext_delta
    intro i
    simp only [LinearMap.comp_apply, vacuumEval_delta]
    exact L.basis_covariance e i u
  exact DFunLike.congr_fun h x

def homToVacuum (f : homSubmodule A) : S :=
  F.recoverWeight L.origin (f.1 (delta L.origin))

theorem hom_origin_supported (f : homSubmodule A) (i : ι)
    (hi : i ≠ L.origin) :
    F.recoverWeight i (f.1 (delta L.origin)) = 0 := by
  obtain ⟨e, a, ha, hb, hw⟩ := L.separate i hi
  have hf := f.2 e (delta L.origin)
  rw [hb] at hf
  have hs : a • F.recoverWeight i (f.1 (delta L.origin)) =
      F.recoverWeight i (f.1 (delta L.origin)) := by
    rw [← hw, hf]
  have hz : (a - 1) • F.recoverWeight i (f.1 (delta L.origin)) = 0 := by
    rw [sub_smul, one_smul, hs, sub_self]
  exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)

theorem hom_origin (f : homSubmodule A) :
    f.1 (delta L.origin) = F.includeWeight L.origin (homToVacuum F A L f) := by
  calc
    _ = ∑ i, F.includeWeight i (F.recoverWeight i (f.1 (delta L.origin))) :=
      (F.complete _).symm
    _ = _ := Finset.sum_eq_single L.origin
      (by intro i _ hi; rw [hom_origin_supported F A L f i hi, map_zero])
      (by simp)

theorem hom_vacuum_inverse (u : S) :
    homToVacuum F A L (vacuumToHom F A L u) = u := by
  change F.recoverWeight L.origin (vacuumEval F u (delta L.origin)) = u
  rw [vacuumEval_delta, F.orthogonal]
  simp

theorem vacuum_hom_inverse (f : homSubmodule A) :
    vacuumToHom F A L (homToVacuum F A L f) = f := by
  apply Subtype.ext
  apply linear_ext_delta
  intro i
  change vacuumEval F (homToVacuum F A L f) (delta i) = f.1 (delta i)
  rw [vacuumEval_delta, ← L.translates_vacuum i, ← hom_origin F A L f]
  rw [f.2, L.translates_basis]

/-- Actual linear Hom identification, under the exact Weyl source laws. -/
def vacuumHomLinearEquiv : S ≃ₗ[k] homSubmodule A where
  toFun := vacuumToHom F A L
  invFun := homToVacuum F A L
  left_inv := hom_vacuum_inverse F A L
  right_inv := vacuum_hom_inverse F A L
  map_add' := by
    intro u v
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change evaluate F (fun i => x i • (u + v)) =
      evaluate F (fun i => x i • u) + evaluate F (fun i => x i • v)
    rw [← map_add]
    congr 1
    funext i
    exact smul_add (x i) u v
  map_smul' := by
    intro c u
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change evaluate F (fun i => x i • (c • u)) =
      c • evaluate F (fun i => x i • u)
    rw [← map_smul]
    congr 1
    funext i
    change x i • (c • u) = c • (x i • u)
    simp only [smul_smul, mul_comm]

end
end Synthesis.MonsterVacuumHomEquivalence

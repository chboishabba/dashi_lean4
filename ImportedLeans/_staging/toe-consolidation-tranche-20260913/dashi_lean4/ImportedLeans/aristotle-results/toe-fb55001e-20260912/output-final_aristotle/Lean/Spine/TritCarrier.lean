/-
# The corpus's own trit carrier, wired into the spine

The corpus already carries a balanced-ternary digit type
`AgdaMirror.DASHIAlgebra.Trit` with two distinguished self-maps:

* the digit negation `Trit.inv` (`neg ↔ pos`, fixing `zer`), an involution;
* the cyclic rotation `AgdaMirror.TritBridge.rotTrit`
  (`neg → zer → pos → neg`), of order three.

That is a `C₃` carrier together with an inversion involution, so it should be an
*instance* of the ternary phase core rather than a parallel hand-rolled
encoding.  This module establishes the link **by explicit equivariance
theorems**, not by shared vocabulary:

* `embed` sends a real weighting of the digits to a vector of `ℝ[C₃]`;
* `embed_rot` intertwines `rotTrit` with the cyclic shift `σ`;
* `embed_inv` intertwines `Trit.inv` with an explicit linear reflection `ρ`;
* `reflect_shift` proves the dihedral relation `ρ σ = σ² ρ` — the involution
  acts on the transverse plane by conjugation, exactly as `ζ ↦ ζ²` does.

The payoff is the *linear* form of the corpus's own
`AgdaMirror.TritBridge.inv_not_rotation_at_neg` ("negation is not rotation"):
on the transverse plane the reflection has a real eigenvector
(`reflect_eigenvector_transverse`) while the rotation has none
(`RealC3.no_real_eigenvector_transverse`).  So the two are not merely unequal at
one digit — they are of different linear types.  That is the ternary distinction
that binary intuition cannot see, since in `C₂` reflection and the nontrivial
character coincide.

Finally `trit_weighting_plane_pos` produces a genuine `MeanObserver` instance
from trit data, with both nondegeneracy witnesses discharged from elementary
conditions on the weightings.
-/
import Mathlib
import Spine.Observer
import Spine.TernaryPhase
import AgdaMirror.TritBridge

open RealInnerProductSpace

namespace Spine
namespace TritCarrier

open AgdaMirror.DASHIAlgebra (Trit)
open AgdaMirror.TritBridge (rotTrit)

/-! ## The index dictionary -/

/-- Digits in cyclic order, indexed by `Fin 3`. -/
def tritOf : Fin 3 → Trit
  | 0 => .neg
  | 1 => .zer
  | 2 => .pos

/-- The inverse dictionary. -/
def idxOf : Trit → Fin 3
  | .neg => 0
  | .zer => 1
  | .pos => 2

@[simp] theorem idxOf_tritOf (i : Fin 3) : idxOf (tritOf i) = i := by fin_cases i <;> rfl
@[simp] theorem tritOf_idxOf (t : Trit) : tritOf (idxOf t) = t := by cases t <;> rfl

/-- The dictionary carries the successor of `Fin 3` to the corpus's rotation:
this is what makes `Trit` a `C₃`-carrier rather than merely a three-element
type. -/
theorem tritOf_succ (i : Fin 3) : tritOf (i + 1) = rotTrit (tritOf i) := by
  fin_cases i <;> rfl

/-! ## The embedding into `ℝ[C₃]` -/

/-- A real weighting of the three digits, read as a vector of `ℝ[C₃]`. -/
noncomputable def embed (f : Trit → ℝ) : RealC3.V := WithLp.toLp 2 (fun i => f (tritOf i))

@[simp] theorem embed_apply (f : Trit → ℝ) (i : Fin 3) : embed f i = f (tritOf i) := rfl

/-- **Equivariance for the rotation.**  The corpus's `rotTrit` is intertwined
with the cyclic shift of `ℝ[C₃]`. -/
theorem embed_rot (f : Trit → ℝ) : RealC3.shift (embed f) = embed (f ∘ rotTrit) := by
  ext i
  simp [RealC3.shift_apply, tritOf_succ]

/-- The linear reflection induced by digit negation. -/
noncomputable def reflect : RealC3.V →ₗ[ℝ] RealC3.V where
  toFun x := WithLp.toLp 2 (fun i => x (idxOf (Trit.inv (tritOf i))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem reflect_apply (x : RealC3.V) (i : Fin 3) :
    reflect x i = x (idxOf (Trit.inv (tritOf i))) := rfl

/-- **Equivariance for the involution.**  Digit negation is intertwined with the
linear reflection. -/
theorem embed_inv (f : Trit → ℝ) : reflect (embed f) = embed (f ∘ Trit.inv) := by
  ext i
  simp

theorem reflect_involutive (x : RealC3.V) : reflect (reflect x) = x := by
  ext i
  have h : ∀ j : Fin 3, idxOf (Trit.inv (Trit.inv (tritOf j))) = j := by decide
  simp only [reflect_apply, tritOf_idxOf]
  rw [h i]

/-- **The dihedral relation `ρ σ = σ² ρ`.**  The involution acts on the carrier
by conjugating the rotation, exactly as complex conjugation sends `ζ` to `ζ²`. -/
theorem reflect_shift (x : RealC3.V) :
    reflect (RealC3.shift x) = RealC3.shift (RealC3.shift (reflect x)) := by
  ext i
  have h : ∀ j : Fin 3,
      idxOf (Trit.inv (tritOf j)) + 1 = idxOf (Trit.inv (tritOf (j + 1 + 1))) := by decide
  simp only [reflect_apply, RealC3.shift_apply]
  rw [h i]

/-! ## The fixed line and the transverse plane -/

/-- The reflection fixes the constant vectors pointwise. -/
theorem reflect_on_fixedSub {x : RealC3.V} (hx : x ∈ RealC3.fixedSub) : reflect x = x := by
  have hc := (RealC3.mem_fixedSub_iff x).mp hx
  ext i
  simpa using hc (idxOf (Trit.inv (tritOf i))) i

/-- The reflection preserves the transverse sector. -/
theorem reflect_mem_transverse {x : RealC3.V} (hx : x ∈ RealC3.transverse) :
    reflect x ∈ RealC3.transverse := by
  rw [RealC3.mem_transverse_iff] at hx ⊢
  have e0 : reflect x 0 = x 2 := rfl
  have e1 : reflect x 1 = x 1 := rfl
  have e2 : reflect x 2 = x 0 := rfl
  rw [e0, e1, e2]; linarith

/-- The alternating weighting `neg ↦ 1`, `zer ↦ 0`, `pos ↦ -1`. -/
noncomputable def altVec : RealC3.V := embed (fun t => match t with
  | .neg => 1
  | .zer => 0
  | .pos => -1)

theorem altVec_mem_transverse : altVec ∈ RealC3.transverse := by
  rw [RealC3.mem_transverse_iff]
  norm_num [altVec, embed, tritOf]

theorem altVec_ne_zero : altVec ≠ 0 := by
  intro h
  have : altVec 0 = (0 : RealC3.V) 0 := by rw [h]
  norm_num [altVec, embed, tritOf] at this

/-- **The reflection has a real eigenvector inside the transverse plane.** -/
theorem reflect_eigenvector_transverse : reflect altVec = -altVec := by
  ext i
  fin_cases i <;> norm_num [altVec, embed, tritOf, idxOf, Trit.inv]

/-- **Negation is not rotation, in linear form.**  The corpus records the
digit-level obstruction `AgdaMirror.TritBridge.inv_not_rotation_at_neg`; here is
its structural cause.  The reflection acts on the transverse plane with a real
eigenvalue, and the rotation provably cannot
(`RealC3.no_real_eigenvector_transverse`), so the two maps are of different
linear types on the very plane that carries the ternary phase. -/
theorem reflect_ne_shift : reflect ≠ RealC3.shift := by
  intro h
  refine RealC3.no_real_eigenvector_transverse altVec_mem_transverse altVec_ne_zero (-1) ?_
  rw [← h, reflect_eigenvector_transverse]
  simp

/-! ## The trit carrier as an observer instance -/

theorem avg_embed (f : Trit → ℝ) :
    MeanSplit.avg (embed f) = (f .neg + f .zer + f .pos) / 3 := by
  simp [MeanSplit.avg, Fin.sum_univ_three, tritOf]

/-- **A genuine plane from trit data.**  A weighting whose digit values do not
sum to zero, paired with a channel whose digit values are not all equal, spans a
strictly positive transverse area: the ternary pair is two independent
directions, not two names for one line. -/
theorem trit_weighting_plane_pos (f g : Trit → ℝ)
    (hf : f .neg + f .zer + f .pos ≠ 0)
    (hg : ¬ (g .neg = g .zer ∧ g .zer = g .pos)) :
    0 < area2 (embed f) (MeanSplit.fluct (embed g)) := by
  refine MeanObserver.transverse_area_pos
    (D := Unit) ⟨fun _ => embed f, fun _ => embed g, fun _ => ?_, fun _ => ?_⟩ ()
  · rw [avg_embed]
    intro h
    exact hf (by field_simp at h; linarith)
  · intro h
    have hconst := (MeanSplit.fluct_eq_zero_iff (embed g)).mp h
    exact hg ⟨by simpa [tritOf] using hconst 0 1, by simpa [tritOf] using hconst 1 2⟩

/-- **The degeneracy control, stated for trit data.**  A constant weighting has
no transverse content, so the inherited theorem says nothing about it. -/
theorem constant_trit_weighting_degenerate (f g : Trit → ℝ)
    (hg : ∀ s t : Trit, g s = g t) :
    area2 (embed f) (MeanSplit.fluct (embed g)) = 0 :=
  degenerate_observer_area_zero _ _ (fun i j => by
    simpa using hg (tritOf i) (tritOf j))

end TritCarrier
end Spine

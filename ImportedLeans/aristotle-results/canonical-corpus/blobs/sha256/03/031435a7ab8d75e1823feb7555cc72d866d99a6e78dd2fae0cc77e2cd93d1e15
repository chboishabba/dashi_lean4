import Mathlib
import Integration.Experiment.JacobianSensitivity
import Integration.Experiment.LocalIdentifiability

/-!
# Stage 7, lane 3 — the information matrix and experiment design

`TOE_STAGE6_INFERENCE.md` frontier item 7 records the gap opened here:

> **Only scalar dynamics.**  … vector states, several parameters, control inputs
> `u`, and Fisher information are all absent.

Stage 5's measurement selector ranked candidate readings by *the largest
sensitivity*.  With several parameters that is the wrong question: a very
sensitive reading can still leave a whole direction of parameter space
invisible.  The right object is

```
F  =  Jᵀ W J,        W  =  the measurement weighting (e.g. Σ⁻¹)
```

and the right question is *which design leaves no invisible direction*, and then
*which design makes the worst-case direction as informative as possible*.

## A deliberate naming decision

`F` is called an **information matrix**, never "Fisher information".  Nothing in
this corpus declares a likelihood family for which `JᵀΣ⁻¹J` is the Fisher
information of a parameter; `information_sees_only_the_jacobian_and_weight`
records exactly what `F` does and does not depend on.

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `infoMatrix`, `infoMatrix_quadratic` | definition/theorem | `F = JᵀWJ` as an `RCov` (so symmetry and positive semidefiniteness come for free), and `vᵀFv = (Jv)ᵀW(Jv)` |
| `zero_information_iff_invisible` | theorem | under a positive-definite weight, `vᵀFv = 0 ↔ Jv = 0`: zero information *is* invisibility |
| **`singular_iff_invisible_direction`** | theorem | `det F = 0 ↔ the design has an invisible parameter direction` |
| `infoOf`, `infoOf_union`, `infoOf_insert` | definition/theorem | the information of a *set* of measurements, and its additivity |
| **`more_measurements_never_lose_information`** | theorem | enlarging the design makes `F` grow in the positive-semidefinite order |
| `EigLower`, `eigLower_gives_derivative_lower_bound` | definition/theorem | a certified `λ_min` bound is exactly the lower bound the identifiability-radius theorem consumes |
| **`best_design_by_det_is_identifiable_if_any_is`** | theorem | maximising `det F` over a candidate list finds an identifiable design whenever one exists |
| `dCrit`, `aCrit`, `EigLower` | definition | the three design criteria of the roadmap: `det F`, `tr(F⁻¹)`, and a certified `λ_min` lower bound |
| `aCrit_of_singular`, `aCrit_ranks_a_singular_design_best` | negative | `tr(F⁻¹)` reports `0` for a *singular* design, so minimising it without a nonsingularity check selects the unidentifiable experiment |
| `criteria_disagree`, `all_three_criteria_disagree` | negative | `det F`, `tr(F⁻¹)` and `λ_min(F)` rank two designs in opposite orders — "optimal design" is meaningless without naming the criterion |
| `information_sees_only_the_jacobian_and_weight` | negative | `F` cannot see model discrepancy, higher-order terms, or the data |

## Claim boundary

No probability distribution appears.  `W` is a declared weighting matrix, `J` a
declared (elsewhere certified) Jacobian.  A large `det F` is a statement about
those two declared objects and nothing else.
-/

namespace Integration.Experiment.InformationMatrix

open Matrix
open Integration.Experiment.JacobianSensitivity

variable {p m : ℕ}

/-! ## §1 The information matrix -/

/-- **The information matrix** `F = Jᵀ W J` of a design with Jacobian `J` and
measurement weighting `W`.  Packaged as an `RCov`, so that its symmetry and
positive semidefiniteness are proved, not assumed. -/
def infoMatrix (J : Matrix (Fin m) (Fin p) ℝ) (W : RCov m) : RCov p :=
  RCov.push J.transpose W

@[simp] theorem infoMatrix_toMatrix (J : Matrix (Fin m) (Fin p) ℝ) (W : RCov m) :
    (infoMatrix J W).toMatrix = J.transpose * W.toMatrix * J := by
  simp [infoMatrix]

/-- **The quadratic form**: the information in direction `v` is the weighted size
of the measurement change `J v` that `v` produces. -/
theorem infoMatrix_quadratic (J : Matrix (Fin m) (Fin p) ℝ) (W : RCov m) (v : Fin p → ℝ) :
    v ⬝ᵥ ((infoMatrix J W).toMatrix *ᵥ v) = (J *ᵥ v) ⬝ᵥ (W.toMatrix *ᵥ (J *ᵥ v)) := by
  rw [infoMatrix_toMatrix]
  have h : (J.transpose * W.toMatrix * J) *ᵥ v
      = J.transpose *ᵥ (W.toMatrix *ᵥ (J *ᵥ v)) := by
    simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_transpose]

/-- A **positive-definite weighting**: every nonzero measurement discrepancy
carries strictly positive weight. -/
def PosDefWeight (W : RCov m) : Prop :=
  ∀ y : Fin m → ℝ, y ≠ 0 → 0 < y ⬝ᵥ (W.toMatrix *ᵥ y)

/-- **Zero information is exactly invisibility.**  Under a positive-definite
weighting, a direction carries no information precisely when the design cannot
see it to first order. -/
theorem zero_information_iff_invisible {J : Matrix (Fin m) (Fin p) ℝ} {W : RCov m}
    (hW : PosDefWeight W) (v : Fin p → ℝ) :
    v ⬝ᵥ ((infoMatrix J W).toMatrix *ᵥ v) = 0 ↔ J *ᵥ v = 0 := by
  rw [infoMatrix_quadratic]
  constructor
  · intro h
    by_contra hne
    exact absurd h (ne_of_gt (hW _ hne))
  · intro h
    rw [h]
    simp

/-! ## §2 Singularity is an invisible direction -/

/-- **The rank criterion, exactly.**  A singular information matrix and an
invisible parameter direction are the same thing.  This is what makes `det F` a
meaningful design criterion rather than a heuristic. -/
theorem singular_iff_invisible_direction {J : Matrix (Fin m) (Fin p) ℝ} {W : RCov m}
    (hW : PosDefWeight W) :
    (infoMatrix J W).toMatrix.det = 0 ↔ ∃ v ≠ 0, J *ᵥ v = 0 := by
  constructor
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    refine ⟨v, hv0, ?_⟩
    rw [← zero_information_iff_invisible hW v, hv]
    simp
  · rintro ⟨v, hv0, hv⟩
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, ?_⟩
    rw [infoMatrix_toMatrix]
    have h : (J.transpose * W.toMatrix * J) *ᵥ v
        = J.transpose *ᵥ (W.toMatrix *ᵥ (J *ᵥ v)) := by
      simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [h, hv]
    simp

/-- The contrapositive an experimenter uses: a nonsingular information matrix
means every parameter direction moves the data. -/
theorem nonsingular_has_no_invisible_direction {J : Matrix (Fin m) (Fin p) ℝ} {W : RCov m}
    (hW : PosDefWeight W) (hdet : (infoMatrix J W).toMatrix.det ≠ 0) (v : Fin p → ℝ)
    (hv : J *ᵥ v = 0) : v = 0 := by
  by_contra hv0
  exact hdet ((singular_iff_invisible_direction hW).2 ⟨v, hv0, hv⟩)

/-! ## §3 Information of a set of measurements -/

/-- **The information of a design**, as a sum over the chosen measurements: each
measurement `i` contributes the rank-one term `wᵢ · rowᵢ rowᵢᵀ`. -/
def infoOf {ι : Type*} [DecidableEq ι] (rows : ι → (Fin p → ℝ)) (w : ι → ℝ)
    (S : Finset ι) : Matrix (Fin p) (Fin p) ℝ :=
  ∑ i ∈ S, w i • Matrix.vecMulVec (rows i) (rows i)

/-- The information of a design is additive over disjoint groups of
measurements. -/
theorem infoOf_union {ι : Type*} [DecidableEq ι] (rows : ι → (Fin p → ℝ)) (w : ι → ℝ)
    {S T : Finset ι} (h : Disjoint S T) :
    infoOf rows w (S ∪ T) = infoOf rows w S + infoOf rows w T := by
  simp [infoOf, Finset.sum_union h]

/-- Adding one measurement adds exactly its rank-one contribution. -/
theorem infoOf_insert {ι : Type*} [DecidableEq ι] (rows : ι → (Fin p → ℝ)) (w : ι → ℝ)
    {S : Finset ι} {i : ι} (hi : i ∉ S) :
    infoOf rows w (insert i S)
      = w i • Matrix.vecMulVec (rows i) (rows i) + infoOf rows w S := by
  simp [infoOf, Finset.sum_insert hi]

/-- The quadratic form of a rank-one contribution is a square. -/
theorem rankOne_quadratic (r v : Fin p → ℝ) (c : ℝ) :
    v ⬝ᵥ ((c • Matrix.vecMulVec r r) *ᵥ v) = c * (r ⬝ᵥ v) ^ 2 := by
  have hL : v ⬝ᵥ ((c • Matrix.vecMulVec r r) *ᵥ v)
      = ∑ i, ∑ j, c * (r i * v i) * (r j * v j) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, Matrix.vecMulVec_apply,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hR : c * (r ⬝ᵥ v) ^ 2 = ∑ i, ∑ j, c * (r i * v i) * (r j * v j) := by
    rw [sq, dotProduct, Finset.sum_mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  rw [hL, hR]

/-- **More measurements never lose information.**  Enlarging the design
increases the information matrix in the positive-semidefinite order, provided
the weights are nonnegative. -/
theorem more_measurements_never_lose_information {ι : Type*} [DecidableEq ι]
    (rows : ι → (Fin p → ℝ)) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {S T : Finset ι} (hST : S ⊆ T) (v : Fin p → ℝ) :
    v ⬝ᵥ (infoOf rows w S *ᵥ v) ≤ v ⬝ᵥ (infoOf rows w T *ᵥ v) := by
  have hquad : ∀ U : Finset ι, v ⬝ᵥ (infoOf rows w U *ᵥ v)
      = ∑ i ∈ U, w i * (rows i ⬝ᵥ v) ^ 2 := by
    intro U
    refine Finset.induction_on U (by simp [infoOf]) ?_
    intro i S hi ih
    rw [infoOf_insert rows w hi, Finset.sum_insert hi, ← ih, Matrix.add_mulVec,
      dotProduct_add, rankOne_quadratic]
  rw [hquad, hquad]
  refine Finset.sum_le_sum_of_subset_of_nonneg hST (fun i _ _ => ?_)
  exact mul_nonneg (hw i) (sq_nonneg _)

/-! ## §4 The design criteria -/

/-- The **D-criterion**: the determinant of the information matrix.  Zero exactly
when a parameter direction is invisible. -/
def dCrit (F : RCov p) : ℝ := F.toMatrix.det

/-- The **E-criterion**, as a *certificate* rather than a number: `EigLower F c`
says every direction carries at least `c‖v‖²` of information.  This is the
worst-case identifiability guarantee. -/
def EigLower (F : RCov p) (c : ℝ) : Prop :=
  ∀ v : Fin p → ℝ, c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (F.toMatrix *ᵥ v)

/-- A certified `λ_min` bound with the identity weighting is exactly a lower
bound on the Jacobian — the hypothesis
`IdentifiabilityRadius.certifiably_identifiable_within_radius` consumes.  So
E-optimal design and certified identifiability radius are the same quantity. -/
theorem eigLower_gives_derivative_lower_bound {J : Matrix (Fin m) (Fin p) ℝ} {W : RCov m}
    {c : ℝ} (h : EigLower (infoMatrix J W) c) (v : Fin p → ℝ) :
    c * (v ⬝ᵥ v) ≤ (J *ᵥ v) ⬝ᵥ (W.toMatrix *ᵥ (J *ᵥ v)) := by
  have := h v
  rwa [infoMatrix_quadratic] at this

/-- A positive `λ_min` certificate rules out invisible directions. -/
theorem eigLower_pos_no_invisible {J : Matrix (Fin m) (Fin p) ℝ} {W : RCov m}
    {c : ℝ} (hc : 0 < c) (h : EigLower (infoMatrix J W) c) (v : Fin p → ℝ)
    (hv : J *ᵥ v = 0) : v = 0 := by
  have h1 := eigLower_gives_derivative_lower_bound h v
  rw [hv] at h1
  simp only [Matrix.mulVec_zero, dotProduct_zero] at h1
  have h2 : v ⬝ᵥ v ≤ 0 := by nlinarith
  have h3 : (0 : ℝ) ≤ v ⬝ᵥ v := by
    rw [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h4 : v ⬝ᵥ v = 0 := le_antisymm h2 h3
  funext i
  have : ∀ j ∈ (Finset.univ : Finset (Fin p)), v j * v j = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg _)).1 ?_
    rw [← dotProduct]; exact h4
  have := this i (Finset.mem_univ i)
  simpa using mul_self_eq_zero.1 this

/-! ## §5 Choosing a design -/

/-- **Maximising the determinant finds an identifiable design if one exists.**
This is the sense in which measurement selection has moved from "take the
largest sensitivity" to "eliminate the invisible parameter volume": the ranking
is by a quantity whose vanishing *is* unidentifiability. -/
theorem best_design_by_det_is_identifiable_if_any_is {ι : Type*} (cands : List ι)
    (Fs : ι → RCov p) (best : ι)
    (hmax : ∀ d ∈ cands, |dCrit (Fs d)| ≤ |dCrit (Fs best)|)
    (good : ι) (hgood : good ∈ cands) (hne : dCrit (Fs good) ≠ 0) :
    dCrit (Fs best) ≠ 0 := by
  intro h
  have := hmax good hgood
  rw [h, abs_zero] at this
  exact hne (abs_eq_zero.1 (le_antisymm this (abs_nonneg _)))

/-- A diagonal information matrix, used to compare criteria. -/
def diagInfo (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : RCov 2 :=
  RCov.diag ![a, b] (by intro i; fin_cases i <;> simpa)

@[simp] theorem dCrit_diagInfo (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dCrit (diagInfo a b ha hb) = a * b := by
  simp [dCrit, diagInfo, RCov.diag]

/-- The **A-criterion**: `tr(F⁻¹)`.  Read as "the total variance of the
parameter estimates", but see `aCrit_of_singular` immediately below — the
reading is only available once `F` is known to be nonsingular, and the bare
number is actively misleading otherwise. -/
noncomputable def aCrit (F : RCov p) : ℝ := (F.toMatrix⁻¹).trace

@[simp] theorem aCrit_diagInfo {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    aCrit (diagInfo a b ha.le hb.le) = 1 / a + 1 / b := by
  have hd : (diagInfo a b ha.le hb.le).toMatrix = Matrix.diagonal ![a, b] := by
    simp [diagInfo, RCov.diag]
  have hprod : (fun i => (![a, b] : Fin 2 → ℝ) i * (![a⁻¹, b⁻¹] : Fin 2 → ℝ) i) = 1 := by
    funext i; fin_cases i <;> simp [ha.ne', hb.ne']
  have hinv : (Matrix.diagonal ![a, b])⁻¹ = Matrix.diagonal ![a⁻¹, b⁻¹] := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, hprod]
    exact Matrix.diagonal_one
  rw [aCrit, hd, hinv, Matrix.trace_diagonal, Fin.sum_univ_two]
  simp [one_div]

/-- **The A-criterion ranks a singular design as perfect.**  Lean's matrix
inverse of a singular matrix is `0`, so `tr(F⁻¹) = 0` exactly when the design is
*worst* — it has an invisible parameter direction.  Minimising `tr(F⁻¹)` without
a nonsingularity side condition therefore selects the unidentifiable design.
This is why `dCrit` and `EigLower`, not `aCrit`, are used in the selection
theorem above. -/
theorem aCrit_of_singular {F : RCov p} (h : dCrit F = 0) : aCrit F = 0 := by
  have : F.toMatrix⁻¹ = 0 := by
    refine Matrix.nonsing_inv_apply_not_isUnit _ ?_
    rw [show F.toMatrix.det = dCrit F from rfl, h]
    simp
  rw [aCrit, this, Matrix.trace_zero]

/-- The trap, as a statement: a singular design and a genuinely good design can
have `aCrit` in the wrong order. -/
theorem aCrit_ranks_a_singular_design_best :
    ∃ A B : RCov 2, dCrit A = 0 ∧ dCrit B ≠ 0 ∧ aCrit A < aCrit B := by
  refine ⟨diagInfo 0 1 le_rfl (by norm_num), diagInfo 2 2 (by norm_num) (by norm_num),
    by simp, by simp, ?_⟩
  rw [aCrit_of_singular (by simp), aCrit_diagInfo (by norm_num : (0:ℝ) < 2)
    (by norm_num : (0:ℝ) < 2)]
  norm_num

/-- **The criteria disagree.**  Design `A` has information `diag(9,1)` and design
`B` has `diag(2,2)`.  `A` wins on the determinant (`9 > 4`) while `B` wins on the
worst direction (`B` certifies `λ_min ≥ 2`, `A` does not).  "Optimal design" is
therefore not a property of the information matrix alone: the identifiability
goal must be declared. -/
theorem criteria_disagree :
    ∃ (A B : RCov 2),
      dCrit B < dCrit A ∧ EigLower B 2 ∧ ¬ EigLower A 2 := by
  refine ⟨diagInfo 9 1 (by norm_num) (by norm_num),
    diagInfo 2 2 (by norm_num) (by norm_num), by norm_num, ?_, ?_⟩
  · intro v
    simp only [diagInfo, RCov.diag, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    norm_num
    ring_nf
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · intro h
    have := h ![0, 1]
    simp only [diagInfo, RCov.diag, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.diagonal_apply] at this
    norm_num at this

/-- **All three criteria of the roadmap now exist, and all three disagree.**
Design `A` has information `diag(9,1)`, design `B` has `diag(2,2)`.  `A` wins on
the determinant (`9 > 4`); `B` wins on the A-criterion (`1 < 10/9`) and on the
worst direction (`B` certifies `λ_min ≥ 2`, `A` does not).  So `det F`,
`tr(F⁻¹)` and `λ_min(F)` are three different questions, and a design is only
"optimal" relative to a declared identifiability goal. -/
theorem all_three_criteria_disagree :
    ∃ A B : RCov 2,
      dCrit B < dCrit A ∧ aCrit B < aCrit A ∧ EigLower B 2 ∧ ¬ EigLower A 2 := by
  refine ⟨diagInfo 9 1 (by norm_num) (by norm_num),
    diagInfo 2 2 (by norm_num) (by norm_num), by norm_num, ?_, ?_, ?_⟩
  · rw [aCrit_diagInfo (by norm_num : (0:ℝ) < 2) (by norm_num : (0:ℝ) < 2),
      aCrit_diagInfo (by norm_num : (0:ℝ) < 9) (by norm_num : (0:ℝ) < 1)]
    norm_num
  · intro v
    simp only [diagInfo, RCov.diag, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    norm_num
    ring_nf
    nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  · intro h
    have := h ![0, 1]
    simp only [diagInfo, RCov.diag, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Matrix.diagonal_apply] at this
    norm_num at this

/-! ## §6 What the information matrix cannot see -/

/-- **The information matrix depends only on the Jacobian and the weighting.**
Two experiments with the same certified Jacobian and the same declared weighting
have the same information — however differently they misdescribe the system, and
whatever data they returned.  So a design optimised by `det F` or `λ_min(F)` is
optimised against the *declared model*, and carries no protection against model
discrepancy (`ModelDiscrepancy`) or against the second-order terms the Jacobian
omits. -/
theorem information_sees_only_the_jacobian_and_weight
    (J J' : Matrix (Fin m) (Fin p) ℝ) (W : RCov m) (h : J = J') :
    (infoMatrix J W).toMatrix = (infoMatrix J' W).toMatrix := by
  rw [h]

end Integration.Experiment.InformationMatrix

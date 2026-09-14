import Integration.Variation.SymmetricFibre

/-!
# QFT/GR frontier, lane 8 — the symmetric perturbation *field* fibre

Lane 6 (`Integration.Variation.SymmetricFibre`) settles the symmetry objection
for a single symmetric matrix: symmetric perturbations separate symmetric
tensors and nothing more.  The frontier report then records the next objection
against the weld, which lane 6 does *not* answer: a physical metric perturbation
is not one symmetric matrix, it is a symmetric 2-tensor **field** — one
symmetric matrix per point of the base — and the variation pairs it against the
stress field through an integral carrying a positive density factor.

This lane takes that step in the honest finite model: the base is a finite index
type `ι` (the sample points of the integral), a field is a function
`ι → Matrix n n ℝ`, and the pairing is the density-weighted trace sum

```
⟪T, H⟫_w  =  ∑ x, w x * tr (T x * H x).
```

The results say exactly which extra hypotheses the field-level weld needs beyond
lane 6:

* it needs **no** extra fibre size: perturbations supported at a single base
  point already separate (`eq_of_localised_pairing_on_symmetric`), so the
  physically admissible "compactly supported" fibre is enough;
* it needs the density to be **nonvanishing**: at a point where `w x = 0` the
  stress field is completely invisible
  (`vanishing_density_hides_a_point`), so `√(-g) > 0` is load-bearing, not
  bookkeeping;
* it still needs **symmetry of the stress field**, exactly as in lane 6
  (`symmetric_field_perturbations_do_not_separate_general_fields`).

## What is proved

* `fieldPair_add_right`, `fieldPair_smul_right`, `fieldPair_add_left` — the
  field pairing is bilinear;
* `localise`, `fieldPair_localise` — the point-supported probe and its pairing;
* `eq_of_localised_pairing_on_symmetric` — separation of symmetric stress fields
  by point-supported symmetric perturbations under a nonvanishing density;
* `eq_of_fieldPair_eq_on_symmetric` — the same with the full symmetric fibre;
* `vanishing_density_hides_a_point` — the negative for a vanishing density;
* `symmetric_field_perturbations_do_not_separate_general_fields` — the negative
  without symmetry of the stress field;
* `field_weld_hypotheses_are_load_bearing` — the three put together.

## What is *not* proved

The base is a finite index type with a weight, not a manifold with a measure:
there is no chart, no coordinate change, no Lorentzian signature and no
integration by parts.  A genuinely infinite base — where the admitted fibre of
compactly supported fields is dense rather than everything — is covered by lane
1's `Pairing.separates_iff_dense`, not here.
-/

namespace Integration.Variation.SymmetricField

open Matrix Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A tensor field on the finite base `ι`: one matrix per base point. -/
abbrev TensorField (ι n : Type*) := ι → Matrix n n ℝ

/-- A field is symmetric when it is symmetric at every base point. -/
def IsSymmField (T : TensorField ι n) : Prop := ∀ x, (T x).IsSymm

/-- The density-weighted trace pairing of two tensor fields,
`∑ x, w x * tr (T x * H x)`.  The weight `w` plays the role of the volume
density `√(-g)` at each sample point. -/
def fieldPair (w : ι → ℝ) (T H : TensorField ι n) : ℝ :=
  ∑ x, w x * (T x * H x).trace

omit [DecidableEq ι] [DecidableEq n] in
theorem fieldPair_add_right (w : ι → ℝ) (T H K : TensorField ι n) :
    fieldPair w T (H + K) = fieldPair w T H + fieldPair w T K := by
  simp only [fieldPair, Pi.add_apply, Matrix.trace_add, mul_add]
  rw [Finset.sum_add_distrib]

omit [DecidableEq ι] [DecidableEq n] in
theorem fieldPair_add_left (w : ι → ℝ) (T S H : TensorField ι n) :
    fieldPair w (T + S) H = fieldPair w T H + fieldPair w S H := by
  simp only [fieldPair, Pi.add_apply, Matrix.add_mul, Matrix.trace_add, mul_add]
  rw [Finset.sum_add_distrib]

omit [DecidableEq ι] [DecidableEq n] in
theorem fieldPair_smul_right (w : ι → ℝ) (c : ℝ) (T H : TensorField ι n) :
    fieldPair w T (c • H) = c * fieldPair w T H := by
  simp only [fieldPair, Pi.smul_apply, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The point-supported ("compactly supported") probe: the perturbation `M` at
the base point `x₀` and zero everywhere else. -/
def localise (x₀ : ι) (M : Matrix n n ℝ) : TensorField ι n :=
  fun x => if x = x₀ then M else 0

omit [Fintype ι] [Fintype n] [DecidableEq n] in
theorem isSymmField_localise {x₀ : ι} {M : Matrix n n ℝ} (hM : M.IsSymm) :
    IsSymmField (localise (n := n) x₀ M) := by
  intro x
  by_cases hx : x = x₀
  · simpa [localise, hx] using hM
  · simp [localise, hx, Matrix.IsSymm]

omit [DecidableEq n] in
/-- Pairing against a point-supported probe reads off the stress at that
point, weighted by the density there. -/
theorem fieldPair_localise (w : ι → ℝ) (T : TensorField ι n) (x₀ : ι) (M : Matrix n n ℝ) :
    fieldPair w T (localise x₀ M) = w x₀ * (T x₀ * M).trace := by
  rw [fieldPair, Finset.sum_eq_single x₀]
  · simp [localise]
  · intro x _ hx
    simp [localise, hx]
  · intro hx
    exact absurd (Finset.mem_univ x₀) hx

/-- **Point-supported symmetric perturbations separate symmetric stress
fields.**  Under a nowhere-vanishing density, two symmetric stress fields with
the same pairings against every *point-supported* symmetric perturbation are
equal.  The admitted physical fibre therefore does not have to be all of field
space. -/
theorem eq_of_localised_pairing_on_symmetric (w : ι → ℝ) (hw : ∀ x, w x ≠ 0)
    (A B : TensorField ι n) (hA : IsSymmField A) (hB : IsSymmField B)
    (hab : ∀ (x₀ : ι) (M : Matrix n n ℝ), M.IsSymm →
      fieldPair w A (localise x₀ M) = fieldPair w B (localise x₀ M)) :
    A = B := by
  funext x₀
  refine SymmetricFibre.eq_of_trace_eq_on_symmetric (A x₀) (B x₀) (hA x₀) (hB x₀) ?_
  intro M hM
  have h := hab x₀ M hM
  rw [fieldPair_localise, fieldPair_localise] at h
  exact mul_left_cancel₀ (hw x₀) h

/-- The same separation statement with the hypothesis taken over the whole
symmetric fibre. -/
theorem eq_of_fieldPair_eq_on_symmetric (w : ι → ℝ) (hw : ∀ x, w x ≠ 0)
    (A B : TensorField ι n) (hA : IsSymmField A) (hB : IsSymmField B)
    (hab : ∀ H : TensorField ι n, IsSymmField H → fieldPair w A H = fieldPair w B H) :
    A = B :=
  eq_of_localised_pairing_on_symmetric w hw A B hA hB
    (fun _ _ hM => hab _ (isSymmField_localise hM))

/-- **A vanishing density hides a base point.**  If the weight vanishes at some
point then no perturbation whatsoever sees the stress there: two distinct
symmetric stress fields have identical pairings against the entire fibre.  So
`√(-g) ≠ 0` is a load-bearing hypothesis of the field-level weld. -/
theorem vanishing_density_hides_a_point [Nonempty n] (w : ι → ℝ) {x₀ : ι} (hw : w x₀ = 0) :
    ∃ A B : TensorField ι n, A ≠ B ∧ IsSymmField A ∧ IsSymmField B ∧
      ∀ H : TensorField ι n, fieldPair w A H = fieldPair w B H := by
  classical
  refine ⟨0, localise x₀ 1, ?_, fun x => by simp [Matrix.IsSymm], ?_, ?_⟩
  · intro hc
    have h1 : (localise (n := n) x₀ (1 : Matrix n n ℝ)) x₀ = 0 := by
      rw [← hc]; rfl
    simp only [localise] at h1
    obtain ⟨i⟩ := ‹Nonempty n›
    have := congrFun (congrFun h1 i) i
    simp at this
  · intro x
    by_cases hx : x = x₀ <;> simp [localise, hx, Matrix.IsSymm]
  · intro H
    rw [fieldPair, fieldPair]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x = x₀
    · subst hx
      simp [hw]
    · simp [localise, hx]

omit [DecidableEq ι] in
/-- **Symmetric field perturbations do not separate general stress fields.**
The pointwise antisymmetric part remains invisible at field level, exactly as in
lane 6. -/
theorem symmetric_field_perturbations_do_not_separate_general_fields
    [Nonempty ι] [Nontrivial n] (w : ι → ℝ) :
    ∃ A B : TensorField ι n, A ≠ B ∧
      ∀ H : TensorField ι n, IsSymmField H → fieldPair w A H = fieldPair w B H := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty ι›
  obtain ⟨C, D, hCD, hagree⟩ :=
    SymmetricFibre.symmetric_perturbations_do_not_separate_general_tensors (n := n)
  refine ⟨fun _ => C, fun _ => D, ?_, ?_⟩
  · intro hc
    exact hCD (congrFun hc x₀)
  · intro H hH
    exact Finset.sum_congr rfl fun x _ => by rw [hagree (H x) (hH x)]

/-- **The three field-level hypotheses are load-bearing.**  With a nowhere
vanishing density and symmetric stress fields the weld holds on the physical
(symmetric, point-supported) fibre; dropping either the density condition or the
symmetry of the stress breaks it. -/
theorem field_weld_hypotheses_are_load_bearing [Nonempty ι] [Nontrivial n] (w : ι → ℝ)
    (hw : ∀ x, w x ≠ 0) :
    (∀ A B : TensorField ι n, IsSymmField A → IsSymmField B →
        (∀ H : TensorField ι n, IsSymmField H → fieldPair w A H = fieldPair w B H) → A = B)
      ∧ ¬ (∀ A B : TensorField ι n,
        (∀ H : TensorField ι n, IsSymmField H → fieldPair w A H = fieldPair w B H) → A = B)
      ∧ ∀ w' : ι → ℝ, (∃ x, w' x = 0) →
        ¬ (∀ A B : TensorField ι n, IsSymmField A → IsSymmField B →
            (∀ H : TensorField ι n, IsSymmField H → fieldPair w' A H = fieldPair w' B H) →
            A = B) := by
  have hne : Nonempty n := ⟨(exists_pair_ne n).choose⟩
  refine ⟨fun A B hA hB h => eq_of_fieldPair_eq_on_symmetric w hw A B hA hB h, ?_, ?_⟩
  · intro hall
    obtain ⟨A, B, hne', hagree⟩ :=
      symmetric_field_perturbations_do_not_separate_general_fields (ι := ι) (n := n) w
    exact hne' (hall A B hagree)
  · rintro w' ⟨x₀, hx₀⟩ hall
    obtain ⟨A, B, hAB, hA, hB, hagree⟩ :=
      vanishing_density_hides_a_point (ι := ι) (n := n) w' hx₀
    exact hAB (hall A B hA hB (fun H _ => hagree H))

end Integration.Variation.SymmetricField

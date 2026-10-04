import Mathlib

/-!
# OS pre-gap reflection Gram null space

The Osterwalder--Schrader Hilbert-space construction first quotients the
positive-time cylinder vector space by the radical of the reflected
positive semidefinite form.  These theorems prove the algebraic quotient
invariance *from positivity*, not from an independent null-space axiom.

The unproved CMP119 task is producing this actual bilinear form and
positivity on its genuine positive-time cylinder class.  Completing the
quotient and proving the translation semigroup descends are subsequent
functional-analytic tasks.
-/

namespace RequestProject.YangMills

/--
For a positive semidefinite symmetric OS Gram form, a null-norm
positive-time test is orthogonal to EVERY positive-time test.  This is
the precise result justifying the OS null quotient.
-/
theorem os_gram_null_iff_orthogonal
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (v : V) :
    B v v = 0 ↔ ∀ w : V, B v w = 0 := by
  rw [B.apply_apply_same_eq_zero_iff hPositive hSymmetric]
  constructor
  · intro hv w
    have hzero : B v = 0 := LinearMap.mem_ker.mp hv
    exact congrArg (fun f : V →ₗ[ℝ] ℝ => f w) hzero
  · intro hv
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro w
    exact hv w

/--
The reflected pairing does not depend on which representative of an
OS zero-norm class is chosen in the LEFT slot.
-/
theorem os_gram_pair_eq_of_null_left_difference
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    {left left' : V}
    (hNull : B (left - left') (left - left') = 0)
    (right : V) :
    B left right = B left' right := by
  have hOrth := (os_gram_null_iff_orthogonal
    B hPositive hSymmetric (left - left')).mp hNull right
  have hDifference : B (left - left') right =
      B left right - B left' right := by
    simp
  rw [hDifference] at hOrth
  exact sub_eq_zero.mp hOrth

/--
The bilinear form is well-defined on TWO independently chosen
representatives modulo OS null directions.  This is the algebraic
precondition for the pre-Hilbert quotient, not the completion theorem.
-/
theorem os_gram_pair_eq_of_null_differences
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    {left left' right right' : V}
    (hNullLeft : B (left - left') (left - left') = 0)
    (hNullRight : B (right - right') (right - right') = 0) :
    B left right = B left' right' := by
  have hLeft :=
    os_gram_pair_eq_of_null_left_difference
      B hPositive hSymmetric hNullLeft right
  have hRight :=
    os_gram_pair_eq_of_null_left_difference
      B hPositive hSymmetric hNullRight left'
  calc
    B left right = B left' right := hLeft
    _ = B right left' := hSymmetric.eq _ _
    _ = B right' left' := hRight
    _ = B left' right' := hSymmetric.eq _ _

/--
Any reflected-Gram contraction preserves null vectors, so the positive-time
translation operator is meaningful on the OS quotient.  This is the
algebraic descent condition; a strongly continuous contraction semigroup
on the completion still needs a separate analytic reconstruction theorem.
-/
theorem os_gram_contraction_preserves_null
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v)
    {v : V}
    (hNull : B v v = 0) :
    B (T v) (T v) = 0 := by
  have hnonneg := hPositive (T v)
  have hupper := hContract v
  rw [hNull] at hupper
  exact le_antisymm hupper hnonneg

/--
OS reflection-positive quotient classes remain identified under
positive-time translation, provided the physical translation is
nonexpansive in the ACTUAL reflected Gram form.
-/
theorem os_gram_contraction_respects_null_equivalence
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (T : V →ₗ[ℝ] V)
    (hContract : ∀ v : V, B (T v) (T v) ≤ B v v)
    {left right : V}
    (hNull : B (left - right) (left - right) = 0) :
    B (T left - T right) (T left - T right) = 0 := by
  simpa only [map_sub] using
    os_gram_contraction_preserves_null
      B hPositive T hContract hNull

/--
The ACTUAL pairing on the OS null quotient, constructed with Lean's
`Submodule` quotient.  Positivity plus symmetry proves representative
independence by `os_gram_pair_eq_of_null_differences`.

No independent axiom asserting "OS pairing descends" is taken here.
-/
def osGramQuotientPairing
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm) :
    (V ⧸ B.ker) → (V ⧸ B.ker) → ℝ :=
  fun left right =>
    Quotient.liftOn₂ left right
      (fun x y : V => B x y)
      (by
        intro left₁ left₂ right₁ right₂ hleft hright
        have hleftMem :
            left₁ - left₂ ∈ B.ker :=
          (Submodule.quotientRel_def B.ker).mp hleft
        have hrightMem :
            right₁ - right₂ ∈ B.ker :=
          (Submodule.quotientRel_def B.ker).mp hright
        exact os_gram_pair_eq_of_null_differences
          B hPositive hSymmetric
          ((B.apply_apply_same_eq_zero_iff hPositive hSymmetric).mpr hleftMem)
          ((B.apply_apply_same_eq_zero_iff hPositive hSymmetric).mpr hrightMem))

/--
The reconstructed pre-Hilbert pairing of two OS equivalence classes is
definitionally the original positive-time reflection Gram value.
-/
theorem osGramQuotientPairing_mk
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (left right : V) :
    osGramQuotientPairing B hPositive hSymmetric
      (Quotient.mk left : V ⧸ B.ker)
      (Quotient.mk right : V ⧸ B.ker) =
    B left right := rfl

/--
Positivity is inherited by the genuine OS quotient.  On the quotient,
zero reflected Gram length is exactly the ZERO equivalence class, so
the positive semidefinite form becomes positive definite.
-/
theorem osGramQuotientPairing_nonnegative
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (q : V ⧸ B.ker) :
    0 ≤ osGramQuotientPairing B hPositive hSymmetric q q := by
  refine Quotient.inductionOn q ?_
  intro v
  exact hPositive v

theorem osGramQuotientPairing_self_eq_zero_iff
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V)
    (hPositive : ∀ v : V, 0 ≤ B v v)
    (hSymmetric : B.IsSymm)
    (q : V ⧸ B.ker) :
    osGramQuotientPairing B hPositive hSymmetric q q = 0
      ↔ q = 0 := by
  refine Quotient.inductionOn q ?_
  intro v
  change B v v = 0 ↔
    (Submodule.Quotient.mk v : V ⧸ B.ker) = 0
  rw [B.apply_apply_same_eq_zero_iff hPositive hSymmetric]
  exact (Submodule.Quotient.mk_eq_zero B.ker).symm

end RequestProject.YangMills

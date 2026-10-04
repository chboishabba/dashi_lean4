import Mathlib
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product-pair second-coordinate swap

For independent copies of a product law `μ × ν`, swapping only the two `ν`
coordinates between the copies preserves the four-fold product measure.  This
is the exact Fubini symmetry needed by the upper/lower boundary-plane Wilson
calculation.
-/

open MeasureTheory

namespace RequestProject.YangMills

/-- `((a,b),(c,d)) ↦ ((a,d),(c,b))`. -/
def productPairSecondSwap
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] :
    ((A × B) × (A × B)) ≃ᵐ ((A × B) × (A × B)) where
  toFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  invFun z := ((z.1.1, z.2.2), (z.2.1, z.1.2))
  left_inv := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  right_inv := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    rfl
  measurable_toFun := by fun_prop
  measurable_invFun := by fun_prop

@[simp] theorem product_pair_second_swap_apply
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (a c : A) (b d : B) :
    productPairSecondSwap ((a, b), (c, d)) = ((a, d), (c, b)) := rfl

/-- The second-coordinate swap preserves two independent copies of `μ × ν`. -/
theorem product_pair_second_swap_measurePreserving
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν] :
    MeasurePreserving (productPairSecondSwap (A := A) (B := B))
      ((μ.prod ν).prod (μ.prod ν))
      ((μ.prod ν).prod (μ.prod ν)) := by
  let regroup : ((A × B) × (A × B)) ≃ᵐ ((A × A) × (B × B)) :=
    { toFun := fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))
      invFun := fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))
      left_inv := by rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
      right_inv := by rintro ⟨⟨a,c⟩,⟨b,d⟩⟩; rfl
      measurable_toFun := by fun_prop
      measurable_invFun := by fun_prop }
  have hregroup : MeasurePreserving regroup
      ((μ.prod ν).prod (μ.prod ν))
      ((μ.prod μ).prod (ν.prod ν)) := by
    have h1 : MeasurePreserving
        (MeasurableEquiv.prodAssoc : ((A × B) × (A × B)) ≃ᵐ A × (B × (A × B)))
        ((μ.prod ν).prod (μ.prod ν))
        (μ.prod (ν.prod (μ.prod ν))) :=
      MeasureTheory.measurePreserving_prodAssoc μ ν (μ.prod ν)
    have h2inner : MeasurePreserving
        (Prod.map Prod.swap id)
        (ν.prod (μ.prod ν))
        (μ.prod (ν.prod ν)) := by
      have hs := MeasureTheory.measurePreserving_swap (μ := ν) (ν := μ)
      exact MeasurePreserving.prod hs (MeasurePreserving.id ν)
    have h2 : MeasurePreserving (Prod.map id (Prod.map Prod.swap id))
        (μ.prod (ν.prod (μ.prod ν)))
        (μ.prod (μ.prod (ν.prod ν))) :=
      MeasurePreserving.prod (MeasurePreserving.id μ) h2inner
    have h3 : MeasurePreserving
        (MeasurableEquiv.prodAssoc.symm : (A × (A × (B × B))) ≃ᵐ ((A × A) × (B × B)))
        (μ.prod (μ.prod (ν.prod ν)))
        ((μ.prod μ).prod (ν.prod ν)) :=
      (MeasureTheory.measurePreserving_prodAssoc μ μ (ν.prod ν)).symm
        MeasurableEquiv.prodAssoc
    have h := h3.comp (h2.comp h1)
    simpa [regroup, Function.comp_def] using h
  have hmiddle : MeasurePreserving (Prod.map id Prod.swap)
      ((μ.prod μ).prod (ν.prod ν))
      ((μ.prod μ).prod (ν.prod ν)) :=
    MeasurePreserving.prod (MeasurePreserving.id (μ.prod μ))
      (MeasureTheory.measurePreserving_swap (μ := ν) (ν := ν))
  have hback : MeasurePreserving regroup.symm
      ((μ.prod μ).prod (ν.prod ν))
      ((μ.prod ν).prod (μ.prod ν)) :=
    hregroup.symm regroup
  have h := hback.comp (hmiddle.comp hregroup)
  simpa [regroup, productPairSecondSwap, Function.comp_def] using h

/-- Integral invariance under exchanging the second coordinates of two product-law copies. -/
theorem integral_product_pair_second_swap
    {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure A) (ν : Measure B) [SFinite μ] [SFinite ν]
    (F : (A × B) × (A × B) → E) :
    (∫ z, F (productPairSecondSwap z) ∂((μ.prod ν).prod (μ.prod ν))) =
      ∫ z, F z ∂((μ.prod ν).prod (μ.prod ν)) := by
  exact (product_pair_second_swap_measurePreserving μ ν).integral_comp'
    (f := productPairSecondSwap (A := A) (B := B)) F

end RequestProject.YangMills

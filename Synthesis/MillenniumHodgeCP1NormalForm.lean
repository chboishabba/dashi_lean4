import Synthesis.MillenniumHodgeCP1Quotient
import Mathlib.Tactic

/-!
# Canonical normal form for the literal complex projective line

The quotient itself already exists as mathlib's `Projectivization`.  This file
proves that every quotient point has exactly one of the normal forms

* `[1 : z]` for a unique `z : ℂ`;
* the point at infinity `[0 : 1]`.

Thus the actual quotient carrier is equivalent, as a type, to `Option ℂ`.
This is a set-level normal form/elimination theorem; no topology/cohomology is
claimed here.
-/

namespace Synthesis.Millennium.Hodge

open scoped LinearAlgebra.Projectivization
open Projectivization

def infinityClass : CP1 :=
  secondChartClass 0

def normalFormToCP1 : Option ℂ → CP1
  | none => infinityClass
  | some z => firstChartClass z

theorem firstChartClass_injective : Function.Injective firstChartClass := by
  intro z w h
  rw [firstChartClass, firstChartClass,
    Projectivization.mk_eq_mk_iff' ℂ] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have ha : a = 1 := by
    simpa [firstVec] using h0
  simpa [firstVec, ha] using h1

theorem infinity_ne_firstChartClass (z : ℂ) :
    infinityClass ≠ firstChartClass z := by
  intro h
  rw [infinityClass, secondChartClass, firstChartClass,
    Projectivization.mk_eq_mk_iff' ℂ] at h
  obtain ⟨a, ha⟩ := h
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have ha0 : a = 0 := by
    simpa [firstVec, secondVec] using h0
  simpa [firstVec, secondVec, ha0] using h1

theorem normalFormToCP1_injective :
    Function.Injective normalFormToCP1 := by
  intro x y h
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y =>
          exfalso
          exact infinity_ne_firstChartClass y h
  | some x =>
      cases y with
      | none =>
          exfalso
          exact infinity_ne_firstChartClass x h.symm
      | some y =>
          exact congrArg some (firstChartClass_injective h)

theorem normalFormToCP1_surjective :
    Function.Surjective normalFormToCP1 := by
  intro p
  rcases chart_cover p with ⟨z, hz⟩ | ⟨w, hw⟩
  · exact ⟨some z, by simpa [normalFormToCP1] using hz⟩
  · by_cases hzero : w = 0
    · subst w
      exact ⟨none, by simpa [normalFormToCP1, infinityClass] using hw⟩
    · refine ⟨some (w⁻¹), ?_⟩
      have hmul : w⁻¹ * w = 1 := by
        simp [hzero]
      have hglue :
          firstChartClass (w⁻¹) = secondChartClass w :=
        chart_classes_eq_of_mul_eq_one' (w⁻¹) w hmul
      simpa [normalFormToCP1] using hglue.trans hw

noncomputable def optionEquivCP1 : Option ℂ ≃ CP1 :=
  Equiv.ofBijective normalFormToCP1
    ⟨normalFormToCP1_injective, normalFormToCP1_surjective⟩

noncomputable def cp1EquivOption : CP1 ≃ Option ℂ :=
  optionEquivCP1.symm

theorem normalForm_exists_unique (p : CP1) :
    ∃! form : Option ℂ, normalFormToCP1 form = p := by
  obtain ⟨form, hform⟩ := normalFormToCP1_surjective p
  refine ⟨form, hform, ?_⟩
  intro other hother
  exact normalFormToCP1_injective (hother.trans hform.symm)

theorem firstChart_not_infinity (z : ℂ) :
    firstChartClass z ≠ infinityClass :=
  (infinity_ne_firstChartClass z).symm

end Synthesis.Millennium.Hodge

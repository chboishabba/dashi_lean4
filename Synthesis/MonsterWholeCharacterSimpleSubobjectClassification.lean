import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Whole-character classification of simple subobjects

A small generic donor for the Monster 3B whole-character route.

If `V` has character equal to a nonzero scalar multiple of the character of a
simple representation `H`, then every simple representation `U` admitting a
nonzero equivariant map into `V` is isomorphic to `H`.

This is deliberately weaker than a full isotypic decomposition theorem.  It
classifies only simple types that actually occur through a nonzero morphism.
Semisimplicity/isotypic assembly and all Monster-specific same-object payments
remain separate.
-/

namespace Synthesis

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [CharZero k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

/-- A nonzero simple source of a representation whose whole character is a
nonzero scalar multiple of one simple character must have that simple type. -/
theorem simple_source_iso_of_nonzero_hom_and_character_eq_smul
    (V H U : FDRep k G) [Simple H] [Simple U]
    (a : k) (_ha : a ≠ 0)
    (hchar : V.character = a • H.character)
    (f : U ⟶ V) (hf : f ≠ 0) :
    Nonempty (U ≅ H) := by
  classical
  by_contra hno
  have hHU : ¬ Nonempty (H ≅ U) := by
    intro h
    exact hno ⟨h.some.symm⟩
  have horth := FDRep.char_orthonormal H U
  rw [if_neg hHU] at horth
  have horth0 :
      ⅟(Fintype.card G : k) •
          ∑ g : G, H.character g * U.character g⁻¹ = 0 := by
    simpa using horth
  have hfinCast : (Module.finrank k (U ⟶ V) : k) = 0 := by
    rw [← FDRep.scalar_product_char_eq_finrank_equivariant U V]
    rw [hchar]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    calc
      ⅟(Fintype.card G : k) *
          (a * ∑ g : G, H.character g * U.character g⁻¹) =
          a *
            (⅟(Fintype.card G : k) *
              ∑ g : G, H.character g * U.character g⁻¹) := by
              ring
      _ = a * 0 := by
        simpa [smul_eq_mul] using congrArg (fun z : k => a * z) horth0
      _ = 0 := by simp
  have hfin : Module.finrank k (U ⟶ V) = 0 := by
    exact Nat.cast_eq_zero.mp hfinCast
  have hsub : Subsingleton (U ⟶ V) :=
    (Module.finrank_eq_zero_iff_of_free k (U ⟶ V)).mp hfin
  exact hf (hsub.elim f 0)

end
end Synthesis

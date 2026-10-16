import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Whole-character classifier for simple sources

Promoted onto the live Monster post-recognition tail from the earlier DASHI
`agent/monster3b-fdrep-groupalgebra-adapter` branch.  The mathematical input is
one SAME-object whole-character identity

  character(V) = a • character(H),   a ≠ 0,

with `H` simple.  Then every simple `U` admitting a nonzero equivariant map into
`V` is forced to have the same representation type as `H`.

This eliminates an arbitrary per-subobject Monster classifier as an independent
research input.  It does not create the actual whole-character identity, the
FDRep/group-algebra adapter used by module-level isotypic assembly, or the
literal Monster same-object attachment.
-/

namespace Synthesis.MonsterWholeCharacterSimpleSource

open CategoryTheory

noncomputable section

universe u

variable {k G : Type u}
variable [Field k] [CharZero k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [IsAlgClosed k]

/-- A nonzero simple source of a representation whose whole character is a
nonzero scalar multiple of one simple character has that same simple type. -/
theorem simpleSourceIsoOfWholeCharacter
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
              ac_rfl
      _ = a * 0 := by
        simpa [smul_eq_mul] using congrArg (fun z : k => a * z) horth0
      _ = 0 := by simp
  have hfin : Module.finrank k (U ⟶ V) = 0 := by
    exact Nat.cast_eq_zero.mp hfinCast
  have hsub : Subsingleton (U ⟶ V) :=
    (Module.finrank_eq_zero_iff_of_free k (U ⟶ V)).mp hfin
  exact hf (hsub.elim f 0)

structure Boundary where
  simpleSourceClassifierSourceWritten : Bool
  wholeCharacterIdentityIsActualInput : Bool
  fdrepToModuleAdapterStillNeededForModuleIsotypicTail : Bool
  arbitrarySimpleTypeClassifierStillIndependentInput : Bool
  actualMonsterWholeCharacterIdentityPaidHere : Bool
  actualMonsterSameObjectAttachmentPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  simpleSourceClassifierSourceWritten := true
  wholeCharacterIdentityIsActualInput := true
  fdrepToModuleAdapterStillNeededForModuleIsotypicTail := true
  arbitrarySimpleTypeClassifierStillIndependentInput := false
  actualMonsterWholeCharacterIdentityPaidHere := false
  actualMonsterSameObjectAttachmentPaidHere := false

end

end Synthesis.MonsterWholeCharacterSimpleSource

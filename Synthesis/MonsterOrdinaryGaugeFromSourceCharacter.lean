import Synthesis.MonsterProjectedOriginalCharacter
import Synthesis.MonsterSignedEndpointComposition

/-!
# Compose recognized character blocks into the actual ordinary gauge

Consumes actual parity split, source row signs and norms, and the original
character identity (derived by MonsterProjectedOriginalCharacter).
No independent numerical intertwiner is an input. Both ordinary block
gauges are retained; their direct sum is then composed with the signed
weight-frame endpoint. Source-written, kernel not run.
-/
namespace Synthesis.MonsterOrdinaryGaugeFromSourceCharacter
noncomputable section
open CategoryTheory
open Synthesis.MonsterCyclotomicCharacterRecognition
open Synthesis.MonsterActualParityCharacter

universe u
variable {k G V M P : Type u}
variable [Field k] [CharZero k] [Group G] [Fintype G]
variable [Invertible (Fintype.card G : k)] [Invertible (Nat.card G : k)]
variable [NeZero (Nat.card G : k)]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup M] [Module k M] [FiniteDimensional k M]
variable [AddCommGroup P] [Module k P] [FiniteDimensional k P]

/-- Reuse the pinned mathlib same-action isomorphism adapter. -/
theorem isoIntertwines {T U : FDRep k G} (i : T ≅ U) (g : G) (x : T) :
    U.ρ g (FDRep.isoToLinearEquiv i x) =
      FDRep.isoToLinearEquiv i (T.ρ g x) := by
  have h := DFunLike.congr_fun (FDRep.Iso.conj_ρ i g) (FDRep.isoToLinearEquiv i x)
  change U.ρ g (FDRep.isoToLinearEquiv i x) =
    FDRep.isoToLinearEquiv i (T.ρ g
      ((FDRep.isoToLinearEquiv i).symm (FDRep.isoToLinearEquiv i x))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

variable (rho : Representation k G V)
variable (minus : Representation k G M) (plus : Representation k G P)
variable (D : ParitySplit rho minus plus)

/-- Combine two independently selected actual Hom isos. This is the
source-to-actual direction consumed by the signed negative gauge theorem. -/
def gauge (T12 T78 : FDRep k G)
    (i12 : T12 ≅ FDRep.of minus) (i78 : T78 ≅ FDRep.of plus) :
    (T12 × T78) ≃ₗ[k] V :=
  LinearEquiv.prodCongr (FDRep.isoToLinearEquiv i12)
    (FDRep.isoToLinearEquiv i78) ≪≫ₗ D.split.symm

theorem gaugeIntertwines (T12 T78 : FDRep k G)
    (i12 : T12 ≅ FDRep.of minus) (i78 : T78 ≅ FDRep.of plus)
    (g : G) (x : T12 × T78) :
    rho g (gauge rho minus plus D T12 T78 i12 i78 x) =
      gauge rho minus plus D T12 T78 i12 i78 (T12.ρ g x.1, T78.ρ g x.2) := by
  apply D.split.injective
  let e := LinearEquiv.prodCongr (FDRep.isoToLinearEquiv i12)
    (FDRep.isoToLinearEquiv i78)
  change D.split (rho g (D.split.symm (e x))) =
    D.split (D.split.symm (e (T12.ρ g x.1, T78.ρ g x.2)))
  rw [LinearEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (D.action g) (e x)
  change D.split (rho g (D.split.symm (e x))) =
    LinearMap.prodMap (minus g) (plus g) (e x) at h
  rw [h]
  apply Prod.ext
  · exact isoIntertwines i12 g x.1
  · exact isoIntertwines i78 g x.2

/-- End-to-end existence of the actual source-to-vacuum gauge over K.
The hypotheses are source character data on the same marked action,
not separate 12 and 78 matrices of the actual vacuum. -/
theorem ordinaryGaugeExists (T12 T78 : FDRep k G)
    (n12 : pairing T12.character T12.character = 1)
    (n78 : pairing T78.character T78.character = 1)
    (h : ∀ g, LinearMap.trace k V (rho g) = T12.character g + T78.character g)
    (ha : ∀ g, T12.character (g * D.j) = -T12.character g)
    (hb : ∀ g, T78.character (g * D.j) = T78.character g) :
    ∃ e : (T12 × T78) ≃ₗ[k] V, ∀ g x,
      rho g (e x) = e (T12.ρ g x.1, T78.ρ g x.2) := by
  obtain ⟨⟨i12⟩,⟨i78⟩⟩ :=
    ordinaryBlocks rho minus plus D T12 T78 n12 n78 h ha hb
  exact ⟨gauge rho minus plus D T12 T78 i12 i78,
    gaugeIntertwines rho minus plus D T12 T78 i12 i78⟩

end
end Synthesis.MonsterOrdinaryGaugeFromSourceCharacter

import Mathlib

/-!
# Canonical normalizer action on an equivariant Hom space

Let `E` act linearly on `H` and `W`.  Let a normalizer carrier `N` act by linear
automorphisms on both H and W and conjugate the E-action compatibly.  Then the
usual formula

  (n . f) = rho_W(n) ∘ f ∘ rho_H(n)^(-1)

preserves E-equivariant maps.  Thus the normalizer action on the multiplicity
Hom carrier is not independent data once the actual normalizer lifts on H and W
and their same conjugation action on E are paid.

This theorem does not construct those actual Monster lifts, prove their
projective cocycle laws, orient zeta, or identify the resulting character with
the source-paid 12+78 character.
-/

namespace Synthesis.MonsterNormalizerHomAction

noncomputable section

universe u

variable {k E N H W : Type u}
variable [Field k]
variable [Group E]
variable [AddCommGroup H] [Module k H]
variable [AddCommGroup W] [Module k W]

/-- Linear E-actions on H and W. -/
structure EActionPair where
  actH : E → H →ₗ[k] H
  actW : E → W →ₗ[k] W

/-- E-equivariant maps H -> W. -/
structure EquivariantHom (A : EActionPair (k := k) (E := E) (H := H) (W := W)) where
  toLinearMap : H →ₗ[k] W
  intertwines : ∀ e x, A.actW e (toLinearMap x) = toLinearMap (A.actH e x)

@[ext]
theorem EquivariantHom.ext
    {A : EActionPair (k := k) (E := E) (H := H) (W := W)}
    {f g : EquivariantHom A}
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Same conjugation action on E, realized compatibly on H and W. -/
structure NormalizerLift
    (A : EActionPair (k := k) (E := E) (H := H) (W := W)) where
  conjugate : N → E → E
  onH : N → H ≃ₗ[k] H
  onW : N → W ≃ₗ[k] W
  onH_conjugates : ∀ n e x,
    onH n (A.actH e x) = A.actH (conjugate n e) (onH n x)
  onW_conjugates : ∀ n e x,
    onW n (A.actW e x) = A.actW (conjugate n e) (onW n x)
  conjugate_surjective : ∀ n, Function.Surjective (conjugate n)

/-- The canonical conjugation action on Hom. -/
def actHom
    (A : EActionPair (k := k) (E := E) (H := H) (W := W))
    (L : NormalizerLift (N := N) A)
    (n : N) (f : EquivariantHom A) : EquivariantHom A where
  toLinearMap := (L.onW n).toLinearMap.comp
    (f.toLinearMap.comp (L.onH n).symm.toLinearMap)
  intertwines := by
    intro e x
    obtain ⟨e0, rfl⟩ := L.conjugate_surjective n e
    have hH := L.onH_conjugates n e0 ((L.onH n).symm x)
    have hW := L.onW_conjugates n e0 (f.toLinearMap ((L.onH n).symm x))
    have hH' :
        (L.onH n).symm (A.actH (L.conjugate n e0) x) =
          A.actH e0 ((L.onH n).symm x) := by
      apply (L.onH n).injective
      simpa using hH.symm
    simp only [LinearMap.comp_apply]
    rw [hH', f.intertwines e0]
    exact hW.symm

/-- Pointwise formula for the induced action. -/
theorem actHom_apply
    (A : EActionPair (k := k) (E := E) (H := H) (W := W))
    (L : NormalizerLift (N := N) A)
    (n : N) (f : EquivariantHom A) (x : H) :
    (actHom A L n f).toLinearMap x =
      L.onW n (f.toLinearMap ((L.onH n).symm x)) := by
  rfl

structure Boundary where
  normalizerLiftInterfaceTyped : Bool
  inducedHomNormalizerActionSourceWritten : Bool
  homPreservationFromConjugationSourceWritten : Bool
  independentMultiplicityActionStillRequired : Bool
  actualMonsterNormalizerLiftsPaidHere : Bool
  actualProjectiveCocycleLawsPaidHere : Bool
  absoluteZetaOrientationPaidHere : Bool
  actualTwelveSeventyEightCharacterTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  normalizerLiftInterfaceTyped := true
  inducedHomNormalizerActionSourceWritten := true
  homPreservationFromConjugationSourceWritten := true
  independentMultiplicityActionStillRequired := false
  actualMonsterNormalizerLiftsPaidHere := false
  actualProjectiveCocycleLawsPaidHere := false
  absoluteZetaOrientationPaidHere := false
  actualTwelveSeventyEightCharacterTransportPaidHere := false

end

end Synthesis.MonsterNormalizerHomAction

import Mathlib

/-!
# Canonical 276 carrier: unordered pairs of 24 coordinates

The off-diagonal part of Sym^2 of a 24-dimensional coordinate space is
canonically indexed by unordered 2-subsets of a 24-element set.

This file constructs that carrier directly:
  Pair24 = {s : Finset (Fin 24) // s.card = 2}

and proves:
  |Pair24| = 276.

Every permutation of the 24 coordinates acts canonically on Pair24.  This is
the natural finite carrier underlying the usual degree-276 action of M24 once a
source embedding M24 -> S24 is supplied.

Semantic boundary:
* this does not identify Pair24 with the Carnahan--Urano 2B Tate multiplicity;
* it does not identify the ATLAS M24 degree-276 action with the 2B Tate action;
* it supplies the missing typed off-diagonal carrier so those same-object
  questions can be asked without flattening everything to the numeral 276.
-/

namespace Integration.OggSSP2BPair24Carrier

abbrev Pair24 := {s : Finset (Fin 24) // s.card = 2}

instance : Fintype Pair24 := inferInstance
instance : DecidableEq Pair24 := inferInstance

theorem pair24_card :
    Fintype.card Pair24 = 276 := by
  native_decide

/-- Coordinate permutations act on unordered pairs by image. -/
def permutePair (σ : Equiv.Perm (Fin 24)) : Pair24 ≃ Pair24 where
  toFun p :=
    ⟨p.1.image σ, by
      simpa using Finset.card_image_iff.mpr σ.injective p.1⟩
  invFun p :=
    ⟨p.1.image σ.symm, by
      simpa using Finset.card_image_iff.mpr σ.symm.injective p.1⟩
  left_inv p := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simp

theorem permutePair_id (p : Pair24) :
    permutePair (Equiv.refl (Fin 24)) p = p := by
  apply Subtype.ext
  simp [permutePair]

theorem permutePair_comp
    (σ τ : Equiv.Perm (Fin 24)) (p : Pair24) :
    permutePair (σ.trans τ) p =
      permutePair τ (permutePair σ p) := by
  apply Subtype.ext
  simp [permutePair, Finset.image_image]

/-- Distinct coordinate transpositions act nontrivially on Pair24. -/
theorem transposition_nontrivial
    (i j k : Fin 24)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    permutePair (Equiv.swap i j)
      ⟨{i,k}, by simp [hij, hik]⟩
      ≠
      ⟨{i,k}, by simp [hij, hik]⟩ := by
  intro h
  have hs := congrArg (fun p : Pair24 => (j ∈ p.1)) h
  simp [permutePair, hij, hik, hjk] at hs

/-- The ordinary permutation module on the canonical 276-point carrier. -/
abbrev Pair24PermutationModule := Pair24 → ZMod 2

def pullbackAction
    (σ : Equiv.Perm (Fin 24)) :
    Pair24PermutationModule →ₗ[ZMod 2] Pair24PermutationModule where
  toFun f := fun p => f ((permutePair σ.symm) p)
  map_add' f g := by
    funext p
    rfl
  map_smul' c f := by
    funext p
    rfl

theorem pullbackAction_id :
    pullbackAction (Equiv.refl (Fin 24)) = LinearMap.id := by
  ext f p
  rfl

theorem pullbackAction_comp
    (σ τ : Equiv.Perm (Fin 24)) :
    pullbackAction (σ.trans τ) =
      (pullbackAction σ).comp (pullbackAction τ) := by
  ext f p
  simp [pullbackAction, permutePair_comp]

/-- Shared cardinality alone does not establish the same-object identification
with the source-derived 2B Tate module. -/
inductive Pair24IsActualTwoBTate276 : Prop

theorem pair24_cardinality_does_not_identify_twoB_tate :
    ¬ Pair24IsActualTwoBTate276 := by
  intro h
  cases h

end Integration.OggSSP2BPair24Carrier

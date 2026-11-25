import Synthesis.MonsterSignedHomComposition
import Synthesis.MonsterLinearEigenspaceRestriction

/-!
# Signed endpoint composition and group descent

Coordinate gauges on the two nontrivial phases are separate. Derive the
negative gauge from the positive one and the two actual outer arrows.
Then compose the actual weight frame with ordinary multiplicity coordinates.
Finally the original E/H product law propagates equivariance to N.
No new character search and no fabricated actual source inhabitant.
-/

namespace Synthesis.MonsterSignedEndpointComposition
noncomputable section
open Synthesis.MonsterWeightFrame

universe u
variable {k S T W U V P M ι : Type u}
variable [Field k] [Fintype ι] [DecidableEq ι]
variable [AddCommGroup S] [Module k S] [AddCommGroup T] [Module k T]
variable [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
variable [AddCommGroup V] [Module k V] [AddCommGroup P] [Module k P]
variable [AddCommGroup M] [Module k M]

/-- The negative source-to-actual gauge is a derived arrow, not an independent
search. Csource : P -> M and Cactual : S -> T keep their types. -/
def negativeGauge (f : P ≃ₗ[k] S) (Csource : P ≃ₗ[k] M)
    (Cactual : S ≃ₗ[k] T) : M ≃ₗ[k] T :=
  Csource.symm ≪≫ₗ f ≪≫ₗ Cactual

theorem positiveOuterSquare (f : P ≃ₗ[k] S) (Csource : P ≃ₗ[k] M)
    (Cactual : S ≃ₗ[k] T) (x : P) :
    negativeGauge f Csource Cactual (Csource x) = Cactual (f x) := by
  change Cactual (f (Csource.symm (Csource x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The reverse outer square follows from the retained C² residual.
This does not assume C²=+I on both constituents. -/
theorem negativeOuterSquare (f : P ≃ₗ[k] S) (Csource : P ≃ₗ[k] M)
    (Cactual : S ≃ₗ[k] T) (Dsource : M ≃ₗ[k] P)
    (Dactual : T ≃ₗ[k] S)
    (square : ∀ x, Dactual (Cactual (f x)) = f (Dsource (Csource x)))
    (y : M) :
    Dactual (negativeGauge f Csource Cactual y) = f (Dsource y) := by
  obtain ⟨x, rfl⟩ := Csource.surjective y
  rw [positiveOuterSquare]
  exact square x

/-- Same positive inner equation at the conjugate source word induces the
negative equation; both source and actual conjugation squares are required. -/
theorem negativeInner (f : P ≃ₗ[k] S) (Csource : P ≃ₗ[k] M)
    (Cactual : S ≃ₗ[k] T)
    (p : P →ₗ[k] P) (m : M →ₗ[k] M)
    (s : S →ₗ[k] S) (t : T →ₗ[k] T)
    (hc₁ : ∀ x, m (Csource x) = Csource (p x))
    (hc₂ : ∀ x, t (Cactual x) = Cactual (s x))
    (hf : ∀ x, s (f x) = f (p x)) (y : M) :
    t (negativeGauge f Csource Cactual y) =
      negativeGauge f Csource Cactual (m y) := by
  obtain ⟨x, rfl⟩ := Csource.surjective y
  rw [positiveOuterSquare, hc₂, hf, hc₁, positiveOuterSquare]

/-- Componentwise linear equivalence, preserving all weight slots. -/
def weightwise (e : S ≃ₗ[k] P) : (ι → S) ≃ₗ[k] (ι → P) where
  toFun x i := e (x i)
  invFun x i := e.symm (x i)
  left_inv x := by funext i; exact e.symm_apply_apply (x i)
  right_inv x := by funext i; exact e.apply_symm_apply (x i)
  map_add' x y := by funext i; exact e.map_add (x i) (y i)
  map_smul' c x := by funext i; exact e.map_smul c (x i)

/-- The actual sector to ordinary finite-copy tensor presentation.
Use P = V12 × Sym²(V12 dual), after proof-bearing character recognition.
The old actual frame supplies the inverse, not a finite basis-label map. -/
def ordinaryCoordinates (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (e : S ≃ₗ[k] P) : W ≃ₗ[k] (ι → P) :=
  (linearEquiv F).symm ≪≫ₗ weightwise e

theorem ordinaryCoordinates_apply
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (e : S ≃ₗ[k] P) (w : W) (i : ι) :
    ordinaryCoordinates F e w i = e (F.recoverWeight i w) := rfl

theorem ordinaryCoordinates_inverse
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (e : S ≃ₗ[k] P) (x : ι → P) :
    (ordinaryCoordinates F e).symm x =
      evaluate F (fun i => e.symm (x i)) := rfl

/-- Genuine tensor product, in the required H ⊗ ordinary orientation.
This is the existing mathlib finite-copy equivalence, not a Cartesian inverse. -/
def ordinaryTensor
    (F : Frame (k := k) (S := S) (W := W) (ι := ι))
    (e : S ≃ₗ[k] P) :
    (ι → k) ⊗[k] P ≃ₗ[k] W :=
  TensorProduct.comm k (ι → k) P ≪≫ₗ
    TensorProduct.piScalarRight k k P ι ≪≫ₗ (ordinaryCoordinates F e).symm

section SignedEntry
open Synthesis.MonsterSignedHomComposition
open Synthesis.MonsterVacuumHomEquivalence
open Synthesis.MonsterNormalizerHomAction
variable {E : Type u} [Group E]
variable (F : Frame (k := k) (S := S) (W := W) (ι := ι))
variable (G : Frame (k := k) (S := T) (W := U) (ι := ι))
variable (A : EActionPair (k := k) (E := E) (H := Schr k ι) (W := W))
variable (B : EActionPair (k := k) (E := E) (H := Schr k ι) (W := U))
variable (R : SignedArrow A B)
variable (L : WeylVacuumLaws F A) (K : WeylVacuumLaws G B)

/-- The FULL transported source operator follows from the genuine
multiplicity intertwiner and the already derived Weyl/Hom action.
In particular zero entries of the Weil kernel are not dropped. -/
theorem ordinaryEntry (e : S ≃ₗ[k] P) (f : T ≃ₗ[k] M)
    (a : P →ₗ[k] M)
    (ha : ∀ u, f (vacuumArrow F G A B R L K u) = a (e u))
    (w : W) (j : ι) :
    ordinaryCoordinates G f (R.onW w) j =
      ∑ i, (R.onH (delta i) j) • a (ordinaryCoordinates F e w i) := by
  have h := full_entry F G A B R L K (recover F w) j
  change G.recoverWeight j (R.onW (evaluate F (recover F w))) = _ at h
  rw [evaluate_recover] at h
  change f (G.recoverWeight j (R.onW w)) =
    ∑ i, (R.onH (delta i) j) • a (e (F.recoverWeight i w))
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change f ((R.onH (delta i) j) • vacuumArrow F G A B R L K
    (F.recoverWeight i w)) = _
  rw [map_smul, ha]

end SignedEntry

/-- Reuse the original zero-sector carrier unchanged. The input splitting
must come from the actual central projections; the two signed coordinates
may have distinct source types. -/
def wholeCoordinates
    (split : V ≃ₗ[k] (U × (W × T)))
    (plus : W ≃ₗ[k] (ι → P)) (minus : T ≃ₗ[k] (ι → M)) :
    V ≃ₗ[k] (U × ((ι → P) × (ι → M))) :=
  split ≪≫ₗ LinearEquiv.prodCongr (LinearEquiv.refl k U)
    (LinearEquiv.prodCongr plus minus)

section Descent
variable {G N : Type u} [Group G] [Group N]

/-- A proof on the literal E and H factors suffices for every normalizer
word, since N=EH. Both actions are honest monoid homs on the same N. -/
theorem equivarianceOfProductCoverage
    (rho : N →* Module.End k W) (sigma : N →* Module.End k V)
    (e : W ≃ₗ[k] V) (E H : Subgroup N)
    (cover : ∀ n : N, ∃ a : E, ∃ b : H, (a : N) * (b : N) = n)
    (hE : ∀ (a : E) w, e (rho a w) = sigma a (e w))
    (hH : ∀ (b : H) w, e (rho b w) = sigma b (e w))
    (n : N) (w : W) :
    e (rho n w) = sigma n (e w) := by
  obtain ⟨a, b, rfl⟩ := cover n
  rw [map_mul, map_mul]
  change e (rho a (rho b w)) = sigma a (sigma b (e w))
  rw [hE, hH]

/-- Kernel triviality proves fibre constancy of the split action. This is
the actual central descent seam: diagonal kernel triviality, not individual
triviality of either of its two marked central factors. -/
theorem actionConstantOnFibre (q : G →* N)
    (a : G →* Module.End k W)
    (hk : ∀ g, q g = 1 → a g = 1)
    {x y : G} (h : q x = q y) : a x = a y := by
  have hz : q (x * y⁻¹) = 1 := by simp [h]
  have ha : a (x * y⁻¹) = 1 := hk _ hz
  calc
    a x = a ((x * y⁻¹) * y) := by simp
    _ = a (x * y⁻¹) * a y := map_mul a _ _
    _ = a y := by rw [ha, one_mul]

/-- Construct the descended representation through a surjective original
quotient map, rather than require a second independent action. -/
def descendAction (q : G →* N) (hq : Function.Surjective q)
    (a : G →* Module.End k W) (hk : ∀ g, q g = 1 → a g = 1) :
    N →* Module.End k W where
  toFun n := a (Classical.choose (hq n))
  map_one' := by
    exact (actionConstantOnFibre q a hk
      ((Classical.choose_spec (hq 1)).trans (map_one q).symm)).trans (map_one a)
  map_mul' x y := by
    have h : q (Classical.choose (hq (x*y))) =
        q (Classical.choose (hq x) * Classical.choose (hq y)) := by
      rw [Classical.choose_spec (hq (x*y)), map_mul,
        Classical.choose_spec (hq x), Classical.choose_spec (hq y)]
    exact (actionConstantOnFibre q a hk h).trans (map_mul a _ _)

theorem descendAction_apply (q : G →* N) (hq : Function.Surjective q)
    (a : G →* Module.End k W) (hk : ∀ g, q g = 1 → a g = 1)
    (g : G) : descendAction q hq a hk (q g) = a g :=
  actionConstantOnFibre q a hk (Classical.choose_spec (hq (q g)))

end Descent
end
end Synthesis.MonsterSignedEndpointComposition

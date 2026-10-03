import Synthesis.MillenniumHodgeRelativeProductSwapExact

/-!
# Hodge max-cut: genuine relative ruling embeddings and factor-swap exchange

For any scheme morphism `f : X ⟶ S` equipped with a section `p : S ⟶ X`,
the relative self-product `X ×[S] X` has two canonical ruling embeddings

  x ↦ (x, p(f x))
  x ↦ (p(f x), x).

This file constructs those maps as literal pullback lifts and proves that the
actual pullback symmetry exchanges them.  No projective-space or synthetic
cycle model is involved.

The eventual `P¹_ℚ` regression only has to instantiate `X`, `S`, `f`, and a
rational section `p`, then push the fundamental cycle along these maps.
-/

namespace Synthesis.Millennium.Hodge

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

section RelativeRulings

variable {X S : Scheme.{u}}
variable (f : X ⟶ S) (p : S ⟶ X)
variable (hp : p ≫ f = 𝟙 S)

/-- First genuine ruling embedding `x ↦ (x, p(f x))`. -/
noncomputable def relativeRulingOne : X ⟶ pullback f f :=
  pullback.lift (𝟙 X) (f ≫ p) (by
    simp [Category.assoc, hp])

/-- Second genuine ruling embedding `x ↦ (p(f x), x)`. -/
noncomputable def relativeRulingTwo : X ⟶ pullback f f :=
  pullback.lift (f ≫ p) (𝟙 X) (by
    simp [Category.assoc, hp])

@[reassoc (attr := simp)]
theorem relativeRulingOne_fst :
    relativeRulingOne f p hp ≫ pullback.fst f f = 𝟙 X := by
  simp [relativeRulingOne]

@[reassoc (attr := simp)]
theorem relativeRulingOne_snd :
    relativeRulingOne f p hp ≫ pullback.snd f f = f ≫ p := by
  simp [relativeRulingOne]

@[reassoc (attr := simp)]
theorem relativeRulingTwo_fst :
    relativeRulingTwo f p hp ≫ pullback.fst f f = f ≫ p := by
  simp [relativeRulingTwo]

@[reassoc (attr := simp)]
theorem relativeRulingTwo_snd :
    relativeRulingTwo f p hp ≫ pullback.snd f f = 𝟙 X := by
  simp [relativeRulingTwo]

/-- The actual relative factor swap sends the first ruling embedding to the
second ruling embedding. -/
theorem relativeRulingOne_swap :
    relativeRulingOne f p hp ≫ (relativeSelfProductSwap f).hom =
      relativeRulingTwo f p hp := by
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

/-- The actual relative factor swap sends the second ruling embedding to the
first ruling embedding. -/
theorem relativeRulingTwo_swap :
    relativeRulingTwo f p hp ≫ (relativeSelfProductSwap f).hom =
      relativeRulingOne f p hp := by
  apply pullback.hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

/-!
MAX-CUT STATUS

PAID HERE:
* the two ruling embeddings are actual Scheme morphisms into the same relative
  pullback used by the factor-swap owner;
* both projection equations are literal pullback equations;
* factor swap exchanges the two rulings at the morphism level.

NEXT:
* instantiate the section with an actual rational point of `P¹_ℚ`;
* define `D₁` and `D₂` as genuine algebraic-cycle pushforwards;
* prove pushforward functoriality in the exact weight convention and derive
  `σ_* D₁ = D₂`, `σ_* D₂ = D₁`, then the `(-1)` difference identity.
-/

end RelativeRulings

end Synthesis.Millennium.Hodge

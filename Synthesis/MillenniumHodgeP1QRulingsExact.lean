import Synthesis.MillenniumHodgeP1QPoint10Exact

/-!
# Hodge max-cut: actual P¹_Q rulings in the genuine relative product

With the selected Proj displayed over `Spec Q` and the literal section
`[1:0]`, the generic relative-ruling construction now specializes without any
synthetic geometry.  This file fixes the actual product over `Spec Q`, the two
ruling embeddings, and the genuine factor-swap equations.
-/

namespace Synthesis.Millennium.Hodge

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

/-- The genuine relative self-product P¹_Q ×_{Spec Q} P¹_Q. -/
abbrev P1QSelfProductOverQ : Scheme :=
  pullback p1QToSpecQ p1QToSpecQ

/-- Genuine factor swap on the selected product over Q. -/
def p1QFactorSwapOverQ :
    P1QSelfProductOverQ ≅ P1QSelfProductOverQ :=
  relativeProductSwap p1QToSpecQ

/-- First actual ruling x ↦ (x,[1:0]). -/
def p1QRulingOne : P1QScheme ⟶ P1QSelfProductOverQ :=
  relativeRulingOne p1QToSpecQ p1QPoint10 p1QPoint10_isSection

/-- Second actual ruling x ↦ ([1:0],x). -/
def p1QRulingTwo : P1QScheme ⟶ P1QSelfProductOverQ :=
  relativeRulingTwo p1QToSpecQ p1QPoint10 p1QPoint10_isSection

@[simp, reassoc] theorem p1QRulingOne_fst :
    p1QRulingOne ≫ pullback.fst p1QToSpecQ p1QToSpecQ = 𝟙 P1QScheme :=
  relativeRulingOne_fst p1QToSpecQ p1QPoint10 p1QPoint10_isSection

@[simp, reassoc] theorem p1QRulingOne_snd :
    p1QRulingOne ≫ pullback.snd p1QToSpecQ p1QToSpecQ =
      p1QToSpecQ ≫ p1QPoint10 :=
  relativeRulingOne_snd p1QToSpecQ p1QPoint10 p1QPoint10_isSection

@[simp, reassoc] theorem p1QRulingTwo_fst :
    p1QRulingTwo ≫ pullback.fst p1QToSpecQ p1QToSpecQ =
      p1QToSpecQ ≫ p1QPoint10 :=
  relativeRulingTwo_fst p1QToSpecQ p1QPoint10 p1QPoint10_isSection

@[simp, reassoc] theorem p1QRulingTwo_snd :
    p1QRulingTwo ≫ pullback.snd p1QToSpecQ p1QToSpecQ = 𝟙 P1QScheme :=
  relativeRulingTwo_snd p1QToSpecQ p1QPoint10 p1QPoint10_isSection

/-- The actual factor swap exchanges the literal first and second rulings. -/
theorem p1QRulingOne_swap :
    p1QRulingOne ≫ p1QFactorSwapOverQ.hom = p1QRulingTwo :=
  relativeRulingOne_swap p1QToSpecQ p1QPoint10 p1QPoint10_isSection

/-- And conversely. -/
theorem p1QRulingTwo_swap :
    p1QRulingTwo ≫ p1QFactorSwapOverQ.hom = p1QRulingOne :=
  relativeRulingTwo_swap p1QToSpecQ p1QPoint10 p1QPoint10_isSection

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* actual P¹_Q ×_{Spec Q} P¹_Q;
* actual [1:0]-defined ruling embeddings;
* literal factor-swap exchange equations on those morphisms.

NEXT:
* push an actual fundamental P¹ cycle along these embeddings;
* prove iso-postcomposition compatibility for `AlgebraicCycle.map` and derive
  swap exchange of the two cycle pushforwards;
* subtract to obtain the genuine (-1)-eigencycle;
* pay cycle-class naturality, then leave the P¹ regression.
-/

end

end Synthesis.Millennium.Hodge

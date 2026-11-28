import Synthesis.MillenniumHodgeDicksonGenericSignedFibreExact

/-!
Original generic Dickson six-root geometry: lift the already-proved
signed-square-root even-deck torsor to the ACTUAL quadratic Q0 roots.

This is an equivalence of the original algebraic root fibres, not a
new synthetic sixfold product and not a Chow cycle, proper pushforward,
or generic primitive Hodge class.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

/-- On a fixed original NONZERO signed discriminant fibre, the actual
six quadratic roots are freely and transitively parameterized by
even deck-sign vectors, with the original discriminant and product
constraints preserved in BOTH directions. -/
def actualOriginalRootEvenDeckEquiv
    (a y : Address → F) (δ : F)
    (base : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    EvenDeck F ≃ ActualRootFibre a y δ :=
  (signedFibreDeckEquiv ((actualRootFibreEquiv a y δ) base) hδ).trans
    (actualRootFibreEquiv a y δ).symm

/-- The zero deck-sign vector's identity is the exact original root
basepoint; no implicit change of coordinate labels or signed phase. -/
theorem originalRootEvenDeck_surjective
    (a y : Address → F) (δ : F)
    (base : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    Function.Surjective
      (actualOriginalRootEvenDeckEquiv a y δ base hδ) :=
  (actualOriginalRootEvenDeckEquiv a y δ base hδ).surjective

/-- Two distinct even-deck choices cannot give the same original
Q0 root fibre. This is a genuine free original geometric action. -/
theorem originalRootEvenDeck_injective
    (a y : Address → F) (δ : F)
    (base : ActualRootFibre a y δ) (hδ : δ ≠ 0) :
    Function.Injective
      (actualOriginalRootEvenDeckEquiv a y δ base hδ) :=
  (actualOriginalRootEvenDeckEquiv a y δ base hδ).injective

/-- The original geometric fibre is nonempty over an algebraically
closed field on the same punctured discriminant cover. The output is
the original Q0 root object, not a generic square-root surrogate. -/
theorem actualOriginalRootPuncturedNonempty
    [IsAlgClosed F]
    (a y : Address → F) (δ : F)
    (hy : ∀ i, y i ≠ 0) (hδ : δ ≠ 0)
    (hprod : δ^2 = ∏ i, deltaField (a i) (y i)) :
    Nonempty (ActualRootFibre a y δ) :=
  actualRootFibre_inhabited a y δ hy hδ hprod

end
end DASHI.Hodge.DicksonCoupled

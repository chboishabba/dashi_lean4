import Synthesis.MillenniumHodgeDicksonOriginalQ0FiveDeckBidiExact
import Synthesis.MillenniumHodgeDicksonGenericProjectionDegreeExact

/-!
Original coupled Dickson geometry, one actual y/eta/delta source:
five independent seventh-power deck coordinates (rotation) paired
with five independent square-sign coordinates (quadratic Q0 roots).
The two sixth coordinates are forced by their ORIGINAL product
constraints, not independent degrees of freedom.

This solves the generic FINITE FIBRE and its injective projected
image when y² != a⁷, not the global proper cycle or the primitive
Hodge class. Neither projection multiplicity nor primitive class is
promoted without its original owner.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

def originalCoupledTenDeckEquiv
    (a y : Address → F) (η δ : F)
    (v : RotationFibre y η) (s : ActualRootFibre a y δ)
    (hη : η ≠ 0) (hδ : δ ≠ 0) :
    ((Fin 5 → {z : F // z^7=1}) ×
     (Fin 5 → {z : F // z^2=1})) ≃
      (RotationFibre y η × ActualRootFibre a y δ) :=
  Equiv.prodCongr
    ((fiveDeckEquiv (F := F) 7 (by decide)).trans
      (rotationDeckEquiv v hη))
    (actualOriginalQ0FiveDeckEquiv a y δ s hδ)

/-- With only the ORIGINAL punctured equations, both original
quadratic and rotation root product fibres are simultaneously
inhabited and controlled by ONE 5+5 deck equivalence. -/
theorem original_coupled_generic_ten_deck_realized
    [IsAlgClosed F]
    (a y : Address → F) (η δ : F)
    (hy : ∀ i,y i ≠ 0)
    (hη : η ≠ 0) (hδ : δ ≠ 0)
    (hrot : η^7 = ∏ i, y i)
    (hsign : δ^2 = ∏ i, deltaField (a i) (y i)) :
    Nonempty
      (((Fin 5 → {z : F // z^7=1}) ×
        (Fin 5 → {z : F // z^2=1})) ≃
          (RotationFibre y η × ActualRootFibre a y δ)) := by
  obtain ⟨v⟩ := rotationFibre_inhabited y η hη hrot
  obtain ⟨s⟩ := actualOriginalRootPuncturedNonempty a y δ hy hδ hsign
  exact ⟨originalCoupledTenDeckEquiv a y η δ v s hη hδ⟩

/-- The original generic projection is itself represented by the
same 5+5 original deck coordinates on its actual IMAGE. The branch
condition y² != a⁷ is precisely the original fold-collision
obstruction; without it no injective claim is made. -/
def original_coupled_ten_deck_projected_image_equiv
    (a y : Address → F) (η δ : F)
    (v : RotationFibre y η) (s : ActualRootFibre a y δ)
    (hη : η ≠ 0) (hδ : δ ≠ 0)
    (hy : ∀ i, y i ≠ 0)
    (hbranch : ∀ i, (y i)^2 ≠ (a i)^7) :
    ((Fin 5 → {z : F // z^7=1}) ×
     (Fin 5 → {z : F // z^2=1})) ≃
      Set.range (coupledProjection a y η δ) :=
  (originalCoupledTenDeckEquiv a y η δ v s hη hδ).trans
    (coupledSurfaceFibreEquiv a y η δ hy hbranch)

end
end DASHI.Hodge.DicksonCoupled

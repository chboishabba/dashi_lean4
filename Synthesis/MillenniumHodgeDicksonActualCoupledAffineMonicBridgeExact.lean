import Synthesis.MillenniumHodgeDicksonOriginalCoupledTenDeckGeometryExact
import Synthesis.MillenniumHodgeDicksonAffineFiniteProperExact

/-!
Original Hodge Dickson coupled chart: the SAME six y_i sources in the
rotation-product fibre satisfy their exact MONIC quadratic over the
ORIGINAL Q0 surface values, coordinate by coordinate.

This weld consumes existing actual_surface_address_quadratic and the
original coupled finite fibre; it does not assume six unrelated base
quadratics or delete the fold locus. It ties the generic 5+5 deck
geometry to the existing finite/proper affine chart construction.

Caution: finite/proper AFFINE chart is already an existing donor
Synthesis.MillenniumHodgeDicksonAffineFiniteProperExact. The true
global projective cycle, branch gluing and primitive cohomological
pairing remain unproved, and are not inferred here.
-/
namespace DASHI.Hodge.DicksonCoupled
noncomputable section
variable {F : Type*} [Field F] [CharZero F]

/-- Every original coupled source root gives the same monic quadratic
y_i² - Q0(a_i,s_i)y_i + a_i⁷=0 on the actual source surface.
This is an algebraic relation, not a point-counting proxy. -/
theorem original_coupled_actual_y_surface_monic
    (a y : Address → F) (η δ : F)
    (hη : η ≠ 0)
    (p : RotationFibre y η × ActualRootFibre a y δ)
    (i : Address) :
    (y i)^2 - Q0Field (a i) (p.2.1 i) * (y i)
      + (a i)^7 = 0 := by
  have hv : p.1.1 i ≠ 0 := rotationFibre_nonzero p.1 hη i
  have hsurface :
      dickson7Field (p.1.1 i + a i / p.1.1 i) (a i) =
        Q0Field (a i) (p.2.1 i) := by
    rw [dickson7Field_laurent _ _ hv, div_pow, p.1.2.1 i]
    exact (p.2.2.1 i).symm
  have hmonic :=
    actual_surface_address_quadratic (a i) (p.1.1 i)
      (p.2.1 i) hv hsurface
  simpa only [p.1.2.1 i] using hmonic

/-- The original geometric existence constructor produces a real
rotation/Q0 surface pair satisfying *all six* monic relations on one
and the same original address/fibre, not separate pointwise choices. -/
theorem original_coupled_actual_six_surface_monic_realization
    [IsAlgClosed F]
    (a y : Address → F) (η δ : F)
    (hy : ∀ i, y i ≠ 0) (hη : η ≠ 0) (hδ : δ ≠ 0)
    (hrot : η^7 = ∏ i, y i)
    (hsign : δ^2 = ∏ i, deltaField (a i) (y i)) :
    ∃ p : RotationFibre y η × ActualRootFibre a y δ,
      ∀ i, (y i)^2 - Q0Field (a i) (p.2.1 i) * (y i)
          + (a i)^7 = 0 := by
  obtain ⟨v,s,_⟩ := coupled_chart_inhabited
    a y η δ hy hη hδ hrot hsign
  exact ⟨(v,s), original_coupled_actual_y_surface_monic a y η δ hη (v,s)⟩

end
end DASHI.Hodge.DicksonCoupled

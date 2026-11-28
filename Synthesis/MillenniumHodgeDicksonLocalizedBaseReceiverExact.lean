import Synthesis.MillenniumHodgeDicksonBasePunctureExact

namespace DASHI.Hodge.DicksonCoupled
noncomputable section

abbrev pulledBaseDenominator : ActualCoupledFoldAlgebra :=
  algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra baseChartDenominator

abbrev ActualSourceOpen := Localization.Away chartDenominator
abbrev PulledBaseOpen := Localization.Away pulledBaseDenominator
abbrev ActualBaseOpen := Localization.Away baseChartDenominator

/-- The literal map from the base ring to any receiver where the source
chart denominator is invertible also admits the base principal open. -/
def actualBaseOpenLift {R : Type*} [CommRing R]
    (p : ActualCoupledFoldAlgebra →+* R) (hp : IsUnit (p chartDenominator)) :
    ActualBaseOpen →+* R :=
  IsLocalization.Away.lift baseChartDenominator
    (g:=p.comp (algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra))
    ((actualChartDenominator_unit_iff p).mp hp)

/-- Both principal localizations have the same actual ring receivers.
No cancellation, reducedness or field hypothesis is used. -/
def actualSourceOpenLift {R : Type*} [CommRing R]
    (p : ActualCoupledFoldAlgebra →+* R)
    (hp : IsUnit (p pulledBaseDenominator)) : ActualSourceOpen →+* R :=
  IsLocalization.Away.lift chartDenominator
    (g:=p) ((actualChartDenominator_unit_iff p).mpr hp)

def pulledBaseOpenLift {R : Type*} [CommRing R]
    (p : ActualCoupledFoldAlgebra →+* R)
    (hp : IsUnit (p chartDenominator)) : PulledBaseOpen →+* R :=
  IsLocalization.Away.lift pulledBaseDenominator
    (g:=p) ((actualChartDenominator_unit_iff p).mp hp)

theorem actual_localized_receivers {R : Type*} [CommRing R]
    (p : ActualCoupledFoldAlgebra →+* R) :
    IsUnit (p chartDenominator) →
      Nonempty (ActualBaseOpen →+* R) ∧
      Nonempty (ActualSourceOpen →+* R) ∧
      Nonempty (PulledBaseOpen →+* R) := by
  intro hp
  exact ⟨⟨actualBaseOpenLift p hp⟩,
    ⟨actualSourceOpenLift p ((actualChartDenominator_unit_iff p).mp hp)⟩,
    ⟨pulledBaseOpenLift p hp⟩⟩

/-- Use the original inhabited sample, not an abstract ring point. -/
theorem actual_sample_all_opens {F : Type*} [Field F] [CharZero F]
    [IsAlgClosed F] :
    Nonempty (ActualBaseOpen →+* F) ∧
    Nonempty (ActualSourceOpen →+* F) ∧
    Nonempty (PulledBaseOpen →+* F) := by
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (-16113/16:F) (by decide : 0<2)
  exact actual_localized_receivers (actualFoldSample d hd)
    (isUnit_iff_ne_zero.mpr (actualFoldSample_denominator d hd))

end
end DASHI.Hodge.DicksonCoupled

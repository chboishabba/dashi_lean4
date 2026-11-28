import Synthesis.MillenniumHodgeDicksonBasePunctureExact
import Mathlib.RingTheory.RingHom.Finite

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

/-- The two actual source localizations are canonically inverse,
over the original coupled ring, not merely inhabited. -/
def sourceToPulled : ActualSourceOpen →+* PulledBaseOpen :=
  actualSourceOpenLift (algebraMap ActualCoupledFoldAlgebra PulledBaseOpen)
    (IsLocalization.Away.algebraMap_isUnit pulledBaseDenominator)

def pulledToSource : PulledBaseOpen →+* ActualSourceOpen :=
  pulledBaseOpenLift (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen)
    (IsLocalization.Away.algebraMap_isUnit chartDenominator)

theorem sourceToPulled_on_original (a : ActualCoupledFoldAlgebra) :
    sourceToPulled (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen a)=
      algebraMap ActualCoupledFoldAlgebra PulledBaseOpen a := by
  simp [sourceToPulled,actualSourceOpenLift]

theorem pulledToSource_on_original (a : ActualCoupledFoldAlgebra) :
    pulledToSource (algebraMap ActualCoupledFoldAlgebra PulledBaseOpen a)=
      algebraMap ActualCoupledFoldAlgebra ActualSourceOpen a := by
  simp [pulledToSource,pulledBaseOpenLift]

theorem source_pulled_roundTrip :
    pulledToSource.comp sourceToPulled=RingHom.id ActualSourceOpen := by
  apply IsLocalization.ringHom_ext (Submonoid.powers chartDenominator)
  ext a
  simp only [RingHom.comp_apply,RingHom.id_apply,sourceToPulled_on_original,
    pulledToSource_on_original]

theorem pulled_source_roundTrip :
    sourceToPulled.comp pulledToSource=RingHom.id PulledBaseOpen := by
  apply IsLocalization.ringHom_ext (Submonoid.powers pulledBaseDenominator)
  ext a
  simp only [RingHom.comp_apply,RingHom.id_apply,pulledToSource_on_original,
    sourceToPulled_on_original]

def actualSourcePulledEquiv : ActualSourceOpen ≃+* PulledBaseOpen where
  toFun := sourceToPulled
  invFun := pulledToSource
  left_inv a := congrArg (fun f : ActualSourceOpen →+* ActualSourceOpen=>f a)
    source_pulled_roundTrip
  right_inv a := congrArg (fun f : PulledBaseOpen →+* PulledBaseOpen=>f a)
    pulled_source_roundTrip
  map_mul' := sourceToPulled.map_mul
  map_add' := sourceToPulled.map_add

/-- The actual localized map out of the base commutes on every
original base coordinate, not only on a chosen geometric point. -/
def actualLocalizedProjectionRingHom : ActualBaseOpen →+* ActualSourceOpen :=
  actualBaseOpenLift (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen)
    (IsLocalization.Away.algebraMap_isUnit chartDenominator)

theorem actualLocalizedProjectionRingHom_commutes :
    actualLocalizedProjectionRingHom.comp (algebraMap CoupledSurfaceBase ActualBaseOpen)=
      (algebraMap ActualCoupledFoldAlgebra ActualSourceOpen).comp
        (algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra) := by
  exact IsLocalization.Away.lift_comp baseChartDenominator _

/-- The original source ring is itself a localization at the pulled
back base element. The squared denominator identity supplies the exact
instance, so the standard finite-localization theorem applies to
the actual chart without choosing a different source. -/
theorem actualSourceOpen_isPulledLocalization :
    IsLocalization.Away pulledBaseDenominator ActualSourceOpen := by
  have h := IsLocalization.Away.mul_of_isUnit
    (S:=ActualSourceOpen) chartDenominator chartDenominator
    (IsLocalization.Away.algebraMap_isUnit chartDenominator)
  simpa only [← pow_two,actualChartDenominator_square,pulledBaseDenominator] using h

theorem actualLocalizedProjectionRingHom_finite :
    actualLocalizedProjectionRingHom.Finite := by
  let f := algebraMap CoupledSurfaceBase ActualCoupledFoldAlgebra
  letI : IsLocalization.Away (f baseChartDenominator) ActualSourceOpen :=
    actualSourceOpen_isPulledLocalization
  letI : Module.Finite CoupledSurfaceBase ActualCoupledFoldAlgebra :=
    coupledFold_finite baseA baseX baseEta
  have hf : f.Finite := RingHom.finite_algebraMap.mpr inferInstance
  have hfin := RingHom.localization_away_map_finite
    CoupledSurfaceBase ActualCoupledFoldAlgebra ActualBaseOpen ActualSourceOpen
    f baseChartDenominator hf
  have he : actualLocalizedProjectionRingHom =
      IsLocalization.Away.map ActualBaseOpen ActualSourceOpen f baseChartDenominator := by
    apply IsLocalization.ringHom_ext (Submonoid.powers baseChartDenominator)
    rw [actualLocalizedProjectionRingHom_commutes]
    unfold IsLocalization.Away.map
    rw [IsLocalization.map_comp]
  rw [he]
  exact hfin

open AlgebraicGeometry in
def actualLocalizedProjection :=
  Spec.map (CommRingCat.ofHom actualLocalizedProjectionRingHom)

open AlgebraicGeometry in
theorem actualLocalizedProjection_proper : IsProper actualLocalizedProjection := by
  letI : IsFinite actualLocalizedProjection :=
    (IsFinite.SpecMap_iff _).mpr actualLocalizedProjectionRingHom_finite
  infer_instance

end
end DASHI.Hodge.DicksonCoupled

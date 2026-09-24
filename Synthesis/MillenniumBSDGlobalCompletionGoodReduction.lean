import Synthesis.MillenniumBSDGlobalPrimePlaceWeld
import Synthesis.MillenniumBSDOddPrimeGoodReduction
import Mathlib.Tactic

/-!
# Good reduction directly on the actual global height-one completion

For a rational odd prime p, work on the exact completion/integer-ring pair
used by mathlib's global WeierstrassCurve.LFunction.  The displayed global
model still has discriminant 64.  The canonical integer-ring equivalence to
Z_p transports the fact that 64 is a unit, hence the displayed model is
already minimal with good reduction on the global completion itself.

This removes the first half of the localPolynomial globalization seam without
postulating invariance under an abstract DVR equivalence.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open NumberField
open IsDedekindDomain
open IsDiscreteValuationRing

abbrev RationalPrimeCompletion
    (p : ℕ) [Fact p.Prime] : Type :=
  (rationalPrimePlace p).adicCompletion ℚ

abbrev RationalPrimeIntegers
    (p : ℕ) [Fact p.Prime] : Type :=
  (rationalPrimePlace p).adicCompletionIntegers ℚ

noncomputable def cmGlobalPrimeCurve
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve (RationalPrimeCompletion p) :=
  cmWeierstrass.baseChange (RationalPrimeCompletion p)

theorem cmGlobalPrimeCurve_discriminant
    (p : ℕ) [Fact p.Prime] :
    (cmGlobalPrimeCurve p).Δ = 64 := by
  simp [cmGlobalPrimeCurve, cmWeierstrass_discriminant]

instance cmGlobalPrimeCurve_isIntegral
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsIntegral (RationalPrimeIntegers p)
      (cmGlobalPrimeCurve p) := by
  refine WeierstrassCurve.isIntegral_of_exists_lift
    (R := RationalPrimeIntegers p)
    (K := RationalPrimeCompletion p) ?_ ?_ ?_ ?_ ?_
  · exact ⟨0, by simp [cmGlobalPrimeCurve, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmGlobalPrimeCurve, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmGlobalPrimeCurve, cmWeierstrass]⟩
  · exact ⟨-1, by simp [cmGlobalPrimeCurve, cmWeierstrass]⟩
  · exact ⟨0, by simp [cmGlobalPrimeCurve, cmWeierstrass]⟩

theorem sixtyFour_isUnit_rationalPrimeIntegers
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    IsUnit (64 : RationalPrimeIntegers p) := by
  have hzp : IsUnit (64 : ℤ_[p]) :=
    sixtyFour_isUnit_padicInt hp2
  have hback := hzp.map
    (rationalPrimeIntegerEquiv p).symm.toRingEquiv.toRingHom
  simpa using hback

theorem cmGlobalPrimeCurve_discriminant_valuation_eq_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p))
      (cmGlobalPrimeCurve p).Δ = 1 := by
  rw [cmGlobalPrimeCurve_discriminant]
  change valuation (RationalPrimeCompletion p)
    (maximalIdeal (RationalPrimeIntegers p))
    (algebraMap (RationalPrimeIntegers p)
      (RationalPrimeCompletion p)
      (64 : RationalPrimeIntegers p)) = 1
  rw [valuation_eq_one_iff_notMem]
  simpa [IsDiscreteValuationRing.maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    using sixtyFour_isUnit_rationalPrimeIntegers hp2

instance cmGlobalPrimeCurve_isMinimal
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.IsMinimal (RationalPrimeIntegers p)
      (cmGlobalPrimeCurve p) where
  val_Δ_maximal := by
    constructor
    · infer_instance
    · intro C hC hle
      have hcurCoe :
          ((WeierstrassCurve.valuation_Δ_aux
            (RationalPrimeIntegers p)
            ((1 : WeierstrassCurve.VariableChange
              (RationalPrimeCompletion p)) • cmGlobalPrimeCurve p) :
            {v : ℤᵐ⁰ // v ≤ 1}) : ℤᵐ⁰) = 1 := by
        simp only [one_smul]
        rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
        exact cmGlobalPrimeCurve_discriminant_valuation_eq_one hp2
      have hcur :
          WeierstrassCurve.valuation_Δ_aux
            (RationalPrimeIntegers p)
            ((1 : WeierstrassCurve.VariableChange
              (RationalPrimeCompletion p)) • cmGlobalPrimeCurve p)
            = (⟨1, le_rfl⟩ : {v : ℤᵐ⁰ // v ≤ 1}) := by
        apply Subtype.ext
        exact hcurCoe
      rw [hcur]
      exact (WeierstrassCurve.valuation_Δ_aux
        (RationalPrimeIntegers p) (C • cmGlobalPrimeCurve p)).property

instance cmGlobalPrimeCurve_hasGoodReduction
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.HasGoodReduction (RationalPrimeIntegers p)
      (cmGlobalPrimeCurve p) where
  toIsMinimal := cmGlobalPrimeCurve_isMinimal hp2
  goodReduction :=
    cmGlobalPrimeCurve_discriminant_valuation_eq_one hp2

noncomputable def cmGlobalChosenMinimal
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve (RationalPrimeCompletion p) :=
  (cmGlobalPrimeCurve p).minimal (RationalPrimeIntegers p)

instance cmGlobalChosenMinimal_isMinimal
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsMinimal (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p) := by
  dsimp [cmGlobalChosenMinimal]
  infer_instance

instance cmGlobalChosenMinimal_isIntegral
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.IsIntegral (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p) := by
  infer_instance

theorem cmGlobalChosenMinimal_aux_eq_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.valuation_Δ_aux (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p)
      = (⟨1, le_rfl⟩ : {v : ℤᵐ⁰ // v ≤ 1}) := by
  let W := cmGlobalPrimeCurve p
  let M := cmGlobalChosenMinimal p
  have hWmin : WeierstrassCurve.IsMinimal
      (RationalPrimeIntegers p) W :=
    cmGlobalPrimeCurve_isMinimal hp2
  have hMmin : WeierstrassCurve.IsMinimal
      (RationalPrimeIntegers p) M := by
    dsimp [M]
    infer_instance
  have hWaux : WeierstrassCurve.valuation_Δ_aux
      (RationalPrimeIntegers p) W
      = (⟨1, le_rfl⟩ : {v : ℤᵐ⁰ // v ≤ 1}) := by
    apply Subtype.ext
    rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral]
    exact cmGlobalPrimeCurve_discriminant_valuation_eq_one hp2
  have hM_le_W : WeierstrassCurve.valuation_Δ_aux
      (RationalPrimeIntegers p) M ≤
      WeierstrassCurve.valuation_Δ_aux (RationalPrimeIntegers p) W := by
    rw [hWaux]
    exact (WeierstrassCurve.valuation_Δ_aux
      (RationalPrimeIntegers p) M).property
  have hW_le_M : WeierstrassCurve.valuation_Δ_aux
      (RationalPrimeIntegers p) W ≤
      WeierstrassCurve.valuation_Δ_aux (RationalPrimeIntegers p) M := by
    let C := (cmGlobalPrimeCurve p).exists_isMinimal
      (RationalPrimeIntegers p) |>.choose
    have hMC : M = C • W := by rfl
    subst M
    exact hWmin.val_Δ_maximal.2 (by infer_instance) hM_le_W
  exact le_antisymm hM_le_W hW_le_M

theorem cmGlobalChosenMinimal_discriminant_valuation_eq_one
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p))
      (cmGlobalChosenMinimal p).Δ = 1 := by
  have haux := congrArg
    (fun v : {v : ℤᵐ⁰ // v ≤ 1} => (v : ℤᵐ⁰))
    (cmGlobalChosenMinimal_aux_eq_one hp2)
  rw [WeierstrassCurve.valuation_Δ_aux_eq_of_isIntegral] at haux
  simpa using haux

instance cmGlobalChosenMinimal_hasGoodReduction
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.HasGoodReduction (RationalPrimeIntegers p)
      (cmGlobalChosenMinimal p) where
  toIsMinimal := by infer_instance
  goodReduction :=
    cmGlobalChosenMinimal_discriminant_valuation_eq_one hp2

end Synthesis.Millennium.BSD

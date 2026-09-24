import Synthesis.MillenniumBSDGlobalCompletionGoodReduction
import Synthesis.MillenniumBSDReductionPointCountExact
import Mathlib.Tactic

/-!
# Reduction point count on the actual global completion

The chosen minimal model on the height-one completion differs from the literal
global model by an integral variable change at odd primes.  After reducing,
the chosen reduction therefore has the same affine point count as the literal
reduction.  The canonical residue-field equivalence to ZMod p then identifies
that literal reduction with the already-counted curve y^2=x^3-x over F_p.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open IsDiscreteValuationRing
open IsLocalRing

noncomputable def cmGlobalChosenMinimalChange
    (p : ℕ) [Fact p.Prime] :
    WeierstrassCurve.VariableChange (RationalPrimeCompletion p) :=
  (cmGlobalPrimeCurve p).exists_isMinimal (RationalPrimeIntegers p) |>.choose

theorem cmGlobalChosenMinimal_eq_change
    (p : ℕ) [Fact p.Prime] :
    cmGlobalChosenMinimal p =
      cmGlobalChosenMinimalChange p • cmGlobalPrimeCurve p := rfl

theorem cmGlobalChosenMinimalChange_u_inv_valuation_pow_eq_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p))
      ((cmGlobalChosenMinimalChange p).u⁻¹ : RationalPrimeCompletion p)) ^ 12 = 1 := by
  let C := cmGlobalChosenMinimalChange p
  let W := cmGlobalPrimeCurve p
  have hM : valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p)) (C • W).Δ = 1 := by
    simpa [C, W, cmGlobalChosenMinimal_eq_change] using
      cmGlobalChosenMinimal_discriminant_valuation_eq_one hp2
  have hW : valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p)) W.Δ = 1 := by
    simpa [W] using cmGlobalPrimeCurve_discriminant_valuation_eq_one hp2
  rw [WeierstrassCurve.variableChange_Δ] at hM
  simpa [map_mul, map_pow, hW] using hM

theorem cmGlobalChosenMinimalChange_u_inv_valuation_eq_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p))
      ((cmGlobalChosenMinimalChange p).u⁻¹ : RationalPrimeCompletion p) = 1 := by
  apply pow_left_injective (by norm_num : (12 : ℕ) ≠ 0)
  simpa using cmGlobalChosenMinimalChange_u_inv_valuation_pow_eq_one hp2

theorem cmGlobalChosenMinimalChange_u_valuation_eq_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p))
      ((cmGlobalChosenMinimalChange p).u : RationalPrimeCompletion p) = 1 := by
  have h := cmGlobalChosenMinimalChange_u_inv_valuation_eq_one hp2
  rw [map_inv₀] at h
  have hi := congrArg Inv.inv h
  simpa using hi

theorem cmGlobalChosenMinimalChange_u_descends_to_unit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ u : (RationalPrimeIntegers p)ˣ,
      algebraMap (RationalPrimeIntegers p) (RationalPrimeCompletion p) u
        = (cmGlobalChosenMinimalChange p).u := by
  have hval : valuation (RationalPrimeCompletion p)
      (maximalIdeal (RationalPrimeIntegers p)) (1 : RationalPrimeCompletion p)
      = valuation (RationalPrimeCompletion p)
        (maximalIdeal (RationalPrimeIntegers p))
        ((cmGlobalChosenMinimalChange p).u : RationalPrimeCompletion p) := by
    simpa using (cmGlobalChosenMinimalChange_u_valuation_eq_one hp2).symm
  obtain ⟨u, hu⟩ :=
    IsDiscreteValuationRing.associated_of_valuation_eq
      (A := RationalPrimeIntegers p) (K := RationalPrimeCompletion p)
      (1 : RationalPrimeCompletion p)
      ((cmGlobalChosenMinimalChange p).u : RationalPrimeCompletion p) hval
  refine ⟨u, ?_⟩
  simpa [Algebra.smul_def] using hu

theorem cmGlobalChosenMinimalChange_descends
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ CR : WeierstrassCurve.VariableChange (RationalPrimeIntegers p),
      CR.baseChange (RationalPrimeCompletion p) =
        cmGlobalChosenMinimalChange p := by
  obtain ⟨u, hu⟩ := cmGlobalChosenMinimalChange_u_descends_to_unit hp2
  exact WeierstrassCurve.variableChange_integral_of_u_integral
    (R := RationalPrimeIntegers p) (K := RationalPrimeCompletion p)
    (W := cmGlobalPrimeCurve p) (W' := cmGlobalChosenMinimal p)
    (CK := cmGlobalChosenMinimalChange p)
    (cmGlobalChosenMinimal_eq_change p).symm hu

noncomputable def cmGlobalChosenIntegralChange
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    WeierstrassCurve.VariableChange (RationalPrimeIntegers p) :=
  (cmGlobalChosenMinimalChange_descends hp2).choose

theorem cmGlobalChosenIntegralChange_baseChange
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmGlobalChosenIntegralChange hp2).baseChange (RationalPrimeCompletion p)
      = cmGlobalChosenMinimalChange p :=
  (cmGlobalChosenMinimalChange_descends hp2).choose_spec

theorem cmGlobalChosenIntegralChange_integralModels
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    cmGlobalChosenIntegralChange hp2 •
        WeierstrassCurve.integralModel (RationalPrimeIntegers p)
          (cmGlobalPrimeCurve p)
      = WeierstrassCurve.integralModel (RationalPrimeIntegers p)
          (cmGlobalChosenMinimal p) := by
  apply WeierstrassCurve.map_injective
    (f := algebraMap (RationalPrimeIntegers p) (RationalPrimeCompletion p))
    (IsFractionRing.injective (RationalPrimeIntegers p) (RationalPrimeCompletion p))
  rw [WeierstrassCurve.map_variableChange]
  rw [cmGlobalChosenIntegralChange_baseChange hp2]
  rw [WeierstrassCurve.baseChange_integralModel_eq
    (RationalPrimeIntegers p) (cmGlobalPrimeCurve p)]
  rw [WeierstrassCurve.baseChange_integralModel_eq
    (RationalPrimeIntegers p) (cmGlobalChosenMinimal p)]
  exact (cmGlobalChosenMinimal_eq_change p).symm

noncomputable def cmGlobalReducedIntegralChange
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    WeierstrassCurve.VariableChange
      (IsLocalRing.ResidueField (RationalPrimeIntegers p)) :=
  (cmGlobalChosenIntegralChange hp2).map
    (IsLocalRing.residue (RationalPrimeIntegers p))

theorem cmGlobalChosenReduction_eq_changedLiteralReduction
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (cmGlobalChosenMinimal p).reduction (RationalPrimeIntegers p)
      = cmGlobalReducedIntegralChange hp2 •
        (cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p) := by
  unfold WeierstrassCurve.reduction
  have h := congrArg
    (fun W : WeierstrassCurve (RationalPrimeIntegers p) =>
      W.map (IsLocalRing.residue (RationalPrimeIntegers p)))
    (cmGlobalChosenIntegralChange_integralModels hp2)
  rw [WeierstrassCurve.map_variableChange] at h
  exact h.symm

theorem cmGlobalChosenReduction_affine_card_eq_literal
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Fintype.card (AffineEquationPoint
      ((cmGlobalChosenMinimal p).reduction (RationalPrimeIntegers p)))
      = Fintype.card (AffineEquationPoint
        ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p))) := by
  rw [cmGlobalChosenReduction_eq_changedLiteralReduction hp2]
  exact variableChange_affineEquationPoint_card
    (cmGlobalReducedIntegralChange hp2)
    ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p))

noncomputable def mapAffineEquationEquiv
    {F K : Type*} [Field F] [Field K]
    (e : F ≃+* K) (W : WeierstrassCurve F) :
    AffineEquationPoint W ≃ AffineEquationPoint (W.map e.toRingHom) where
  toFun := fun P =>
    ⟨(e P.1.1, e P.1.2), P.2.map⟩
  invFun := fun P =>
    ⟨(e.symm P.1.1, e.symm P.1.2), by
      have h := P.2.map (f := e.symm.toRingHom)
      simpa using h⟩
  left_inv := by intro P; apply Subtype.ext; simp
  right_inv := by intro P; apply Subtype.ext; simp

theorem cmGlobalLiteralReduction_map_ZMod
    (p : ℕ) [Fact p.Prime] :
    ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p)).map
      (rationalPrimeResidueFieldEquivZMod p).toRingHom
      = cmZModWeierstrass p := by
  ext <;> simp [cmGlobalPrimeCurve, cmWeierstrass, cmZModWeierstrass]

theorem cmGlobalLiteralReduction_affine_card_eq_ZMod
    (p : ℕ) [Fact p.Prime] :
    Fintype.card (AffineEquationPoint
      ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p)))
      = Fintype.card (AffineEquationPoint (cmZModWeierstrass p)) := by
  let e := mapAffineEquationEquiv
    (rationalPrimeResidueFieldEquivZMod p)
    ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p))
  rw [← cmGlobalLiteralReduction_map_ZMod p]
  exact Fintype.card_congr e

theorem cmGlobalChosenReduction_affine_card_eq_fiberCount
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Fintype.card (AffineEquationPoint
      ((cmGlobalChosenMinimal p).reduction (RationalPrimeIntegers p)))
      = affineFiberCount p := by
  calc
    Fintype.card (AffineEquationPoint
      ((cmGlobalChosenMinimal p).reduction (RationalPrimeIntegers p)))
      = Fintype.card (AffineEquationPoint
        ((cmGlobalPrimeCurve p).reduction (RationalPrimeIntegers p))) :=
          cmGlobalChosenReduction_affine_card_eq_literal hp2
    _ = Fintype.card (AffineEquationPoint (cmZModWeierstrass p)) :=
          cmGlobalLiteralReduction_affine_card_eq_ZMod p
    _ = affineFiberCount p := cmZMod_affine_card_eq_fiberCount p

theorem cmGlobalChosenReduction_point_card_eq_projectivePointCount
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card ((cmGlobalChosenMinimal p).reduction
      (RationalPrimeIntegers p)).toAffine.Point
      = projectivePointCount p := by
  letI : WeierstrassCurve.IsElliptic
      ((cmGlobalChosenMinimal p).reduction (RationalPrimeIntegers p)) :=
    WeierstrassCurve.HasGoodReduction.reduction_isElliptic
      (R := RationalPrimeIntegers p) (W := cmGlobalChosenMinimal p)
  rw [Nat.card_congr
    (((cmGlobalChosenMinimal p).reduction
      (RationalPrimeIntegers p)).toAffine.pointEquiv)]
  simp [Nat.card_eq_fintype_card,
    cmGlobalChosenReduction_affine_card_eq_fiberCount hp2]
  rfl

end Synthesis.Millennium.BSD

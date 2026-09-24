import Synthesis.MillenniumBSDOddPrimeGoodReduction
import Synthesis.MillenniumBSDVariableChangePointEquiv
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

/-!
# Reduction of the chosen minimal model is a literal variable change

At every odd prime p, the change used by mathlib's chosen minimal model has
already been shown to descend to an admissible change CR over Z_p.  Here we
show that CR carries the literal integral model of y²=x³-x to the chosen
integral minimal model, then reduce that equality modulo p.

Consequently the two finite-field reductions have exactly the same number of
affine solutions.  This removes the minimal-model choice from the local point
count.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open IsDiscreteValuationRing
open IsLocalRing

noncomputable def cmChosenIntegralChange
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.VariableChange ℤ_[p] :=
  (cmChosenMinimalChange_descends hp2).choose

theorem cmChosenIntegralChange_baseChange
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (cmChosenIntegralChange hp2).baseChange ℚ_[p] =
      cmChosenMinimalChange p :=
  (cmChosenMinimalChange_descends hp2).choose_spec

theorem cmChosenIntegralChange_integralModels
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    cmChosenIntegralChange hp2 •
        WeierstrassCurve.integralModel ℤ_[p]
          (cmPadicWeierstrass p)
      =
        WeierstrassCurve.integralModel ℤ_[p]
          (cmChosenMinimal p) := by
  apply WeierstrassCurve.map_injective
    (f := algebraMap ℤ_[p] ℚ_[p])
    (IsFractionRing.injective ℤ_[p] ℚ_[p])
  rw [WeierstrassCurve.map_variableChange]
  rw [cmChosenIntegralChange_baseChange hp2]
  rw [WeierstrassCurve.baseChange_integralModel_eq
        ℤ_[p] (cmPadicWeierstrass p)]
  rw [WeierstrassCurve.baseChange_integralModel_eq
        ℤ_[p] (cmChosenMinimal p)]
  exact (cmChosenMinimal_eq_change p).symm

noncomputable def cmReducedIntegralChange
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    WeierstrassCurve.VariableChange
      (IsLocalRing.ResidueField ℤ_[p]) :=
  (cmChosenIntegralChange hp2).map
    (IsLocalRing.residue ℤ_[p])

theorem cmChosenReduction_eq_changedLiteralReduction
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    (cmChosenMinimal p).reduction ℤ_[p]
      =
    cmReducedIntegralChange hp2 •
      (cmPadicWeierstrass p).reduction ℤ_[p] := by
  unfold WeierstrassCurve.reduction
  have h := congrArg
    (fun W : WeierstrassCurve ℤ_[p] =>
      W.map (IsLocalRing.residue ℤ_[p]))
    (cmChosenIntegralChange_integralModels hp2)
  rw [WeierstrassCurve.map_variableChange] at h
  exact h.symm

theorem chosenReduction_affineEquationPoint_card_eq_literal
    {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) :
    Fintype.card
      (AffineEquationPoint
        ((cmChosenMinimal p).reduction ℤ_[p]))
      =
    Fintype.card
      (AffineEquationPoint
        ((cmPadicWeierstrass p).reduction ℤ_[p])) := by
  rw [cmChosenReduction_eq_changedLiteralReduction hp2]
  exact variableChange_affineEquationPoint_card
    (cmReducedIntegralChange hp2)
    ((cmPadicWeierstrass p).reduction ℤ_[p])

noncomputable def padicResidueEquivZMod
    (p : ℕ) [Fact p.Prime] :
    IsLocalRing.ResidueField ℤ_[p] ≃+* ZMod p :=
  PadicInt.residueField

end Synthesis.Millennium.BSD
